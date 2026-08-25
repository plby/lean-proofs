/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, OpenAI Codex
-/
import ErdosProblems.Erdos232.CompactBase

open LeanCert.Core
namespace Erdos232

def compactCertificate224 : CompactCertificate where
  left := 103
  right := 104
  center := 207 / 2
  grid := fun i =>
    match i.val with
    | 0 => 33
    | 1 => 24
    | 2 => 39
    | 3 => 7
    | 4 => 19
    | 5 => 52
    | 6 => 38
    | 7 => 65
    | 8 => 48
    | 9 => 74
    | 10 => 43
    | 11 => 76
    | 12 => 71
    | 13 => 50
    | 14 => 57
    | 15 => 48
    | 16 => 42
    | 17 => 61
    | 18 => 34
    | 19 => 29
    | 20 => 18
    | 21 => 10
    | 22 => 26
    | 23 => 36
    | 24 => 15
    | 25 => 61
    | _ => 41
  point := fun i =>
    match i.val with
    | 0 => 207 / 2
    | 1 => 304950526215507 / 4000000000000
    | 2 => 98614734574131 / 800000000000
    | 3 => 88983802992249 / 4000000000000
    | 4 => 239023011444453 / 4000000000000
    | 5 => 648993972669201 / 4000000000000
    | 6 => 478046022889113 / 4000000000000
    | 7 => 819140008253949 / 4000000000000
    | 8 => 603374822611191 / 4000000000000
    | 9 => 925732142684793 / 4000000000000
    | 10 => 534471701776497 / 4000000000000
    | 11 => 948429413884773 / 4000000000000
    | 12 => 886145785478937 / 4000000000000
    | 13 => 632395445903721 / 4000000000000
    | 14 => 717069034333359 / 4000000000000
    | 15 => 597817402622271 / 4000000000000
    | 16 => 528189805199691 / 4000000000000
    | 17 => 153089992733409 / 800000000000
    | 18 => 423454976585523 / 4000000000000
    | 19 => 358967473287003 / 4000000000000
    | 20 => 224625177388809 / 4000000000000
    | 21 => 120804167469303 / 4000000000000
    | 22 => 328006814436909 / 4000000000000
    | 23 => 447865262948493 / 4000000000000
    | 24 => 189374822611191 / 4000000000000
    | 25 => 769798140138711 / 4000000000000
    | _ => 514189482038649 / 4000000000000
  state := fun i =>
    match i.val with
    | 0 => (orderedInterval (-45033366364 / 1000000000000) (-45033366363 / 1000000000000), orderedInterval (-63992545483 / 1000000000000) (-63992545482 / 1000000000000))
    | 1 => (orderedInterval (91254620860 / 1000000000000) (91254620920 / 1000000000000), orderedInterval (-5381965518 / 1000000000000) (-5381965459 / 1000000000000))
    | 2 => (orderedInterval (-71806368831 / 1000000000000) (-71806368810 / 1000000000000), orderedInterval (-2590283763 / 1000000000000) (-2590283742 / 1000000000000))
    | 3 => (orderedInterval (-145406008691 / 1000000000000) (-145406008690 / 1000000000000), orderedInterval (-83168338789 / 1000000000000) (-83168338788 / 1000000000000))
    | 4 => (orderedInterval (-77461504745 / 1000000000000) (-77461504744 / 1000000000000), orderedInterval (-67567483507 / 1000000000000) (-67567483506 / 1000000000000))
    | 5 => (orderedInterval (-20279959934 / 1000000000000) (-20279959452 / 1000000000000), orderedInterval (59328599000 / 1000000000000) (59328599482 / 1000000000000))
    | 6 => (orderedInterval (57860141429 / 1000000000000) (57860141430 / 1000000000000), orderedInterval (44244351784 / 1000000000000) (44244351785 / 1000000000000))
    | 7 => (orderedInterval (-54593704942 / 1000000000000) (-54593704938 / 1000000000000), orderedInterval (-11191082879 / 1000000000000) (-11191082876 / 1000000000000))
    | 8 => (orderedInterval (48019306644 / 1000000000000) (48019306645 / 1000000000000), orderedInterval (43596259657 / 1000000000000) (43596259658 / 1000000000000))
    | 9 => (orderedInterval (-13481403441 / 1000000000000) (-13481403320 / 1000000000000), orderedInterval (50714729688 / 1000000000000) (50714729808 / 1000000000000))
    | 10 => (orderedInterval (43728775324 / 1000000000000) (43728801313 / 1000000000000), orderedInterval (-53570369892 / 1000000000000) (-53570343903 / 1000000000000))
    | 11 => (orderedInterval (-39565250655 / 1000000000000) (-39565167956 / 1000000000000), orderedInterval (33542862187 / 1000000000000) (33542944887 / 1000000000000))
    | 12 => (orderedInterval (35820258754 / 1000000000000) (35820285102 / 1000000000000), orderedInterval (-39962757083 / 1000000000000) (-39962730735 / 1000000000000))
    | 13 => (orderedInterval (61740982200 / 1000000000000) (61740983295 / 1000000000000), orderedInterval (-14849698272 / 1000000000000) (-14849697177 / 1000000000000))
    | 14 => (orderedInterval (-49530162378 / 1000000000000) (-49530162377 / 1000000000000), orderedInterval (-32997795604 / 1000000000000) (-32997795603 / 1000000000000))
    | 15 => (orderedInterval (-34531791158 / 1000000000000) (-34531784289 / 1000000000000), orderedInterval (55497765924 / 1000000000000) (55497772793 / 1000000000000))
    | 16 => (orderedInterval (53736676869 / 1000000000000) (53736676870 / 1000000000000), orderedInterval (43768185737 / 1000000000000) (43768185738 / 1000000000000))
    | 17 => (orderedInterval (-28161362730 / 1000000000000) (-28161362729 / 1000000000000), orderedInterval (-50262466613 / 1000000000000) (-50262466612 / 1000000000000))
    | 18 => (orderedInterval (-12828159474 / 1000000000000) (-12828159396 / 1000000000000), orderedInterval (76539856257 / 1000000000000) (76539856335 / 1000000000000))
    | 19 => (orderedInterval (46179177284 / 1000000000000) (46179188932 / 1000000000000), orderedInterval (-70694678264 / 1000000000000) (-70694666616 / 1000000000000))
    | 20 => (orderedInterval (40557812622 / 1000000000000) (40557812623 / 1000000000000), orderedInterval (98086629303 / 1000000000000) (98086629304 / 1000000000000))
    | 21 => (orderedInterval (-60997981921 / 1000000000000) (-60997978522 / 1000000000000), orderedInterval (132768875335 / 1000000000000) (132768878734 / 1000000000000))
    | 22 => (orderedInterval (78690088002 / 1000000000000) (78690088003 / 1000000000000), orderedInterval (39159567390 / 1000000000000) (39159567391 / 1000000000000))
    | 23 => (orderedInterval (-25624662532 / 1000000000000) (-25624661721 / 1000000000000), orderedInterval (71031529941 / 1000000000000) (71031530751 / 1000000000000))
    | 24 => (orderedInterval (-97735385515 / 1000000000000) (-97735385514 / 1000000000000), orderedInterval (-61371818859 / 1000000000000) (-61371818858 / 1000000000000))
    | 25 => (orderedInterval (-57495025943 / 1000000000000) (-57495025848 / 1000000000000), orderedInterval (1663890802 / 1000000000000) (1663890897 / 1000000000000))
    | _ => (orderedInterval (-35363075734 / 1000000000000) (-35363075733 / 1000000000000), orderedInterval (-60705573025 / 1000000000000) (-60705573024 / 1000000000000))
  chunkTarget := fun r b =>
    match r.val with
    | 0 =>
      match b.val with
      | 0 => orderedInterval (-21213013497 / 1000000000000) (-21213013487 / 1000000000000)
      | 1 => orderedInterval (190992346 / 1000000000000) (190992393 / 1000000000000)
      | 2 => orderedInterval (2844420186 / 1000000000000) (2844420193 / 1000000000000)
      | 3 => orderedInterval (10991483 / 1000000000000) (11005228 / 1000000000000)
      | 4 => orderedInterval (5442388683 / 1000000000000) (5442389276 / 1000000000000)
      | 5 => orderedInterval (-4194975308 / 1000000000000) (-4194975218 / 1000000000000)
      | 6 => orderedInterval (757756238 / 1000000000000) (757756937 / 1000000000000)
      | 7 => orderedInterval (1304948755 / 1000000000000) (1304948893 / 1000000000000)
      | _ => orderedInterval (10726067381 / 1000000000000) (10726067418 / 1000000000000)
    | 1 =>
      match b.val with
      | 0 => orderedInterval (-25582377563 / 1000000000000) (-25582377552 / 1000000000000)
      | 1 => orderedInterval (-7842049343 / 1000000000000) (-7842049274 / 1000000000000)
      | 2 => orderedInterval (2218565463 / 1000000000000) (2218565474 / 1000000000000)
      | 3 => orderedInterval (-14350511423 / 1000000000000) (-14350481871 / 1000000000000)
      | 4 => orderedInterval (-311537293 / 1000000000000) (-311536095 / 1000000000000)
      | 5 => orderedInterval (-4649538804 / 1000000000000) (-4649538674 / 1000000000000)
      | 6 => orderedInterval (-7315651908 / 1000000000000) (-7315651299 / 1000000000000)
      | 7 => orderedInterval (-7308320535 / 1000000000000) (-7308320438 / 1000000000000)
      | _ => orderedInterval (13725310574 / 1000000000000) (13725310630 / 1000000000000)
    | 2 =>
      match b.val with
      | 0 => orderedInterval (23612480734 / 1000000000000) (23612480746 / 1000000000000)
      | 1 => orderedInterval (-2597219800 / 1000000000000) (-2597219695 / 1000000000000)
      | 2 => orderedInterval (-9078691177 / 1000000000000) (-9078691158 / 1000000000000)
      | 3 => orderedInterval (12279351762 / 1000000000000) (12279417245 / 1000000000000)
      | 4 => orderedInterval (-11409172143 / 1000000000000) (-11409169677 / 1000000000000)
      | 5 => orderedInterval (8346780685 / 1000000000000) (8346780874 / 1000000000000)
      | 6 => orderedInterval (-498856541 / 1000000000000) (-498856003 / 1000000000000)
      | 7 => orderedInterval (-1202939392 / 1000000000000) (-1202939301 / 1000000000000)
      | _ => orderedInterval (-26425822650 / 1000000000000) (-26425822563 / 1000000000000)
    | 3 =>
      match b.val with
      | 0 => orderedInterval (25410710657 / 1000000000000) (25410710672 / 1000000000000)
      | 1 => orderedInterval (16737858753 / 1000000000000) (16737858915 / 1000000000000)
      | 2 => orderedInterval (-5847550004 / 1000000000000) (-5847549969 / 1000000000000)
      | 3 => orderedInterval (51840915628 / 1000000000000) (51841062379 / 1000000000000)
      | 4 => orderedInterval (-2827415582 / 1000000000000) (-2827410469 / 1000000000000)
      | 5 => orderedInterval (11324683406 / 1000000000000) (11324683680 / 1000000000000)
      | 6 => orderedInterval (9981666211 / 1000000000000) (9981666682 / 1000000000000)
      | 7 => orderedInterval (7405623980 / 1000000000000) (7405624073 / 1000000000000)
      | _ => orderedInterval (-20659085751 / 1000000000000) (-20659085608 / 1000000000000)
    | _ =>
      match b.val with
      | 0 => orderedInterval (-26566403362 / 1000000000000) (-26566403345 / 1000000000000)
      | 1 => orderedInterval (8071765392 / 1000000000000) (8071765648 / 1000000000000)
      | 2 => orderedInterval (31155617250 / 1000000000000) (31155617313 / 1000000000000)
      | 3 => orderedInterval (-87030125618 / 1000000000000) (-87029792241 / 1000000000000)
      | 4 => orderedInterval (20522549446 / 1000000000000) (20522560189 / 1000000000000)
      | 5 => orderedInterval (-18525467007 / 1000000000000) (-18525466604 / 1000000000000)
      | 6 => orderedInterval (689179495 / 1000000000000) (689179912 / 1000000000000)
      | 7 => orderedInterval (1851167822 / 1000000000000) (1851167922 / 1000000000000)
      | _ => orderedInterval (72105398076 / 1000000000000) (72105398318 / 1000000000000)
  coefficientTarget := fun i =>
    match i.val with
    | 0 => orderedInterval (-4130423733 / 1000000000000) (-4130408367 / 1000000000000)
    | 1 => orderedInterval (-51416110832 / 1000000000000) (-51416079099 / 1000000000000)
    | 2 => orderedInterval (-6974088522 / 1000000000000) (-6974019532 / 1000000000000)
    | 3 => orderedInterval (93367407298 / 1000000000000) (93367560355 / 1000000000000)
    | _ => orderedInterval (2273681494 / 1000000000000) (2274027112 / 1000000000000)

theorem compactCertificate224_stateChecks0 :
    compactCertificate224.stateChecks 0 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 33 12 (207 / 2)) (orderedInterval (-45033366364 / 1000000000000) (-45033366363 / 1000000000000), orderedInterval (-63992545483 / 1000000000000) (-63992545482 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 24 12 (304950526215507 / 4000000000000)) (orderedInterval (91254620860 / 1000000000000) (91254620920 / 1000000000000), orderedInterval (-5381965518 / 1000000000000) (-5381965459 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 39 12 (98614734574131 / 800000000000)) (orderedInterval (-71806368831 / 1000000000000) (-71806368810 / 1000000000000), orderedInterval (-2590283763 / 1000000000000) (-2590283742 / 1000000000000))) = true
  norm_num [besselStateAtRationalPoint, besselIntervalStepZero,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, besselZeroTransition,
    besselInitial, besselGridStateAt, besselGridStateBlock00, besselGridStateBlock01,
    besselGridStateBlock02, besselGridStateBlock03, besselGridStateBlock04,
    besselGridStateBlock05, besselGridStateBlock06, besselGridStateBlock07,
    besselGridStateBlock08, besselGridStateBlock09, besselGridStateBlock10,
    besselGridStateBlock11, besselGridStateBlock12, besselGridStateBlock13,
    besselGridStateBlock14, besselGridState007, besselGridState010, besselGridState015, besselGridState018, besselGridState019, besselGridState024, besselGridState026, besselGridState029, besselGridState033, besselGridState034, besselGridState036, besselGridState038, besselGridState039, besselGridState041, besselGridState042, besselGridState043, besselGridState048, besselGridState050, besselGridState052, besselGridState057, besselGridState061, besselGridState065, besselGridState071, besselGridState074, besselGridState076, besselStateSubset, linearInterval, widenInterval,
    rationalErrorInterval, rationalIntervalSubset, orderedInterval, Finset.sum_range_succ,
    IntervalRat.add, IntervalRat.mul, IntervalRat.scale, IntervalRat.singleton]

theorem compactCertificate224_stateChecks1 :
    compactCertificate224.stateChecks 3 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 7 12 (88983802992249 / 4000000000000)) (orderedInterval (-145406008691 / 1000000000000) (-145406008690 / 1000000000000), orderedInterval (-83168338789 / 1000000000000) (-83168338788 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 19 12 (239023011444453 / 4000000000000)) (orderedInterval (-77461504745 / 1000000000000) (-77461504744 / 1000000000000), orderedInterval (-67567483507 / 1000000000000) (-67567483506 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 52 12 (648993972669201 / 4000000000000)) (orderedInterval (-20279959934 / 1000000000000) (-20279959452 / 1000000000000), orderedInterval (59328599000 / 1000000000000) (59328599482 / 1000000000000))) = true
  norm_num [besselStateAtRationalPoint, besselIntervalStepZero,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, besselZeroTransition,
    besselInitial, besselGridStateAt, besselGridStateBlock00, besselGridStateBlock01,
    besselGridStateBlock02, besselGridStateBlock03, besselGridStateBlock04,
    besselGridStateBlock05, besselGridStateBlock06, besselGridStateBlock07,
    besselGridStateBlock08, besselGridStateBlock09, besselGridStateBlock10,
    besselGridStateBlock11, besselGridStateBlock12, besselGridStateBlock13,
    besselGridStateBlock14, besselGridState007, besselGridState010, besselGridState015, besselGridState018, besselGridState019, besselGridState024, besselGridState026, besselGridState029, besselGridState033, besselGridState034, besselGridState036, besselGridState038, besselGridState039, besselGridState041, besselGridState042, besselGridState043, besselGridState048, besselGridState050, besselGridState052, besselGridState057, besselGridState061, besselGridState065, besselGridState071, besselGridState074, besselGridState076, besselStateSubset, linearInterval, widenInterval,
    rationalErrorInterval, rationalIntervalSubset, orderedInterval, Finset.sum_range_succ,
    IntervalRat.add, IntervalRat.mul, IntervalRat.scale, IntervalRat.singleton]

theorem compactCertificate224_stateChecks2 :
    compactCertificate224.stateChecks 6 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 38 12 (478046022889113 / 4000000000000)) (orderedInterval (57860141429 / 1000000000000) (57860141430 / 1000000000000), orderedInterval (44244351784 / 1000000000000) (44244351785 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 65 12 (819140008253949 / 4000000000000)) (orderedInterval (-54593704942 / 1000000000000) (-54593704938 / 1000000000000), orderedInterval (-11191082879 / 1000000000000) (-11191082876 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 48 12 (603374822611191 / 4000000000000)) (orderedInterval (48019306644 / 1000000000000) (48019306645 / 1000000000000), orderedInterval (43596259657 / 1000000000000) (43596259658 / 1000000000000))) = true
  norm_num [besselStateAtRationalPoint, besselIntervalStepZero,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, besselZeroTransition,
    besselInitial, besselGridStateAt, besselGridStateBlock00, besselGridStateBlock01,
    besselGridStateBlock02, besselGridStateBlock03, besselGridStateBlock04,
    besselGridStateBlock05, besselGridStateBlock06, besselGridStateBlock07,
    besselGridStateBlock08, besselGridStateBlock09, besselGridStateBlock10,
    besselGridStateBlock11, besselGridStateBlock12, besselGridStateBlock13,
    besselGridStateBlock14, besselGridState007, besselGridState010, besselGridState015, besselGridState018, besselGridState019, besselGridState024, besselGridState026, besselGridState029, besselGridState033, besselGridState034, besselGridState036, besselGridState038, besselGridState039, besselGridState041, besselGridState042, besselGridState043, besselGridState048, besselGridState050, besselGridState052, besselGridState057, besselGridState061, besselGridState065, besselGridState071, besselGridState074, besselGridState076, besselStateSubset, linearInterval, widenInterval,
    rationalErrorInterval, rationalIntervalSubset, orderedInterval, Finset.sum_range_succ,
    IntervalRat.add, IntervalRat.mul, IntervalRat.scale, IntervalRat.singleton]

theorem compactCertificate224_stateChecks3 :
    compactCertificate224.stateChecks 9 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 74 12 (925732142684793 / 4000000000000)) (orderedInterval (-13481403441 / 1000000000000) (-13481403320 / 1000000000000), orderedInterval (50714729688 / 1000000000000) (50714729808 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 43 12 (534471701776497 / 4000000000000)) (orderedInterval (43728775324 / 1000000000000) (43728801313 / 1000000000000), orderedInterval (-53570369892 / 1000000000000) (-53570343903 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 76 12 (948429413884773 / 4000000000000)) (orderedInterval (-39565250655 / 1000000000000) (-39565167956 / 1000000000000), orderedInterval (33542862187 / 1000000000000) (33542944887 / 1000000000000))) = true
  norm_num [besselStateAtRationalPoint, besselIntervalStepZero,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, besselZeroTransition,
    besselInitial, besselGridStateAt, besselGridStateBlock00, besselGridStateBlock01,
    besselGridStateBlock02, besselGridStateBlock03, besselGridStateBlock04,
    besselGridStateBlock05, besselGridStateBlock06, besselGridStateBlock07,
    besselGridStateBlock08, besselGridStateBlock09, besselGridStateBlock10,
    besselGridStateBlock11, besselGridStateBlock12, besselGridStateBlock13,
    besselGridStateBlock14, besselGridState007, besselGridState010, besselGridState015, besselGridState018, besselGridState019, besselGridState024, besselGridState026, besselGridState029, besselGridState033, besselGridState034, besselGridState036, besselGridState038, besselGridState039, besselGridState041, besselGridState042, besselGridState043, besselGridState048, besselGridState050, besselGridState052, besselGridState057, besselGridState061, besselGridState065, besselGridState071, besselGridState074, besselGridState076, besselStateSubset, linearInterval, widenInterval,
    rationalErrorInterval, rationalIntervalSubset, orderedInterval, Finset.sum_range_succ,
    IntervalRat.add, IntervalRat.mul, IntervalRat.scale, IntervalRat.singleton]

theorem compactCertificate224_stateChecks4 :
    compactCertificate224.stateChecks 12 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 71 12 (886145785478937 / 4000000000000)) (orderedInterval (35820258754 / 1000000000000) (35820285102 / 1000000000000), orderedInterval (-39962757083 / 1000000000000) (-39962730735 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 50 12 (632395445903721 / 4000000000000)) (orderedInterval (61740982200 / 1000000000000) (61740983295 / 1000000000000), orderedInterval (-14849698272 / 1000000000000) (-14849697177 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 57 12 (717069034333359 / 4000000000000)) (orderedInterval (-49530162378 / 1000000000000) (-49530162377 / 1000000000000), orderedInterval (-32997795604 / 1000000000000) (-32997795603 / 1000000000000))) = true
  norm_num [besselStateAtRationalPoint, besselIntervalStepZero,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, besselZeroTransition,
    besselInitial, besselGridStateAt, besselGridStateBlock00, besselGridStateBlock01,
    besselGridStateBlock02, besselGridStateBlock03, besselGridStateBlock04,
    besselGridStateBlock05, besselGridStateBlock06, besselGridStateBlock07,
    besselGridStateBlock08, besselGridStateBlock09, besselGridStateBlock10,
    besselGridStateBlock11, besselGridStateBlock12, besselGridStateBlock13,
    besselGridStateBlock14, besselGridState007, besselGridState010, besselGridState015, besselGridState018, besselGridState019, besselGridState024, besselGridState026, besselGridState029, besselGridState033, besselGridState034, besselGridState036, besselGridState038, besselGridState039, besselGridState041, besselGridState042, besselGridState043, besselGridState048, besselGridState050, besselGridState052, besselGridState057, besselGridState061, besselGridState065, besselGridState071, besselGridState074, besselGridState076, besselStateSubset, linearInterval, widenInterval,
    rationalErrorInterval, rationalIntervalSubset, orderedInterval, Finset.sum_range_succ,
    IntervalRat.add, IntervalRat.mul, IntervalRat.scale, IntervalRat.singleton]

theorem compactCertificate224_stateChecks5 :
    compactCertificate224.stateChecks 15 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 48 12 (597817402622271 / 4000000000000)) (orderedInterval (-34531791158 / 1000000000000) (-34531784289 / 1000000000000), orderedInterval (55497765924 / 1000000000000) (55497772793 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 42 12 (528189805199691 / 4000000000000)) (orderedInterval (53736676869 / 1000000000000) (53736676870 / 1000000000000), orderedInterval (43768185737 / 1000000000000) (43768185738 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 61 12 (153089992733409 / 800000000000)) (orderedInterval (-28161362730 / 1000000000000) (-28161362729 / 1000000000000), orderedInterval (-50262466613 / 1000000000000) (-50262466612 / 1000000000000))) = true
  norm_num [besselStateAtRationalPoint, besselIntervalStepZero,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, besselZeroTransition,
    besselInitial, besselGridStateAt, besselGridStateBlock00, besselGridStateBlock01,
    besselGridStateBlock02, besselGridStateBlock03, besselGridStateBlock04,
    besselGridStateBlock05, besselGridStateBlock06, besselGridStateBlock07,
    besselGridStateBlock08, besselGridStateBlock09, besselGridStateBlock10,
    besselGridStateBlock11, besselGridStateBlock12, besselGridStateBlock13,
    besselGridStateBlock14, besselGridState007, besselGridState010, besselGridState015, besselGridState018, besselGridState019, besselGridState024, besselGridState026, besselGridState029, besselGridState033, besselGridState034, besselGridState036, besselGridState038, besselGridState039, besselGridState041, besselGridState042, besselGridState043, besselGridState048, besselGridState050, besselGridState052, besselGridState057, besselGridState061, besselGridState065, besselGridState071, besselGridState074, besselGridState076, besselStateSubset, linearInterval, widenInterval,
    rationalErrorInterval, rationalIntervalSubset, orderedInterval, Finset.sum_range_succ,
    IntervalRat.add, IntervalRat.mul, IntervalRat.scale, IntervalRat.singleton]

theorem compactCertificate224_stateChecks6 :
    compactCertificate224.stateChecks 18 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 34 12 (423454976585523 / 4000000000000)) (orderedInterval (-12828159474 / 1000000000000) (-12828159396 / 1000000000000), orderedInterval (76539856257 / 1000000000000) (76539856335 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 29 12 (358967473287003 / 4000000000000)) (orderedInterval (46179177284 / 1000000000000) (46179188932 / 1000000000000), orderedInterval (-70694678264 / 1000000000000) (-70694666616 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 18 12 (224625177388809 / 4000000000000)) (orderedInterval (40557812622 / 1000000000000) (40557812623 / 1000000000000), orderedInterval (98086629303 / 1000000000000) (98086629304 / 1000000000000))) = true
  norm_num [besselStateAtRationalPoint, besselIntervalStepZero,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, besselZeroTransition,
    besselInitial, besselGridStateAt, besselGridStateBlock00, besselGridStateBlock01,
    besselGridStateBlock02, besselGridStateBlock03, besselGridStateBlock04,
    besselGridStateBlock05, besselGridStateBlock06, besselGridStateBlock07,
    besselGridStateBlock08, besselGridStateBlock09, besselGridStateBlock10,
    besselGridStateBlock11, besselGridStateBlock12, besselGridStateBlock13,
    besselGridStateBlock14, besselGridState007, besselGridState010, besselGridState015, besselGridState018, besselGridState019, besselGridState024, besselGridState026, besselGridState029, besselGridState033, besselGridState034, besselGridState036, besselGridState038, besselGridState039, besselGridState041, besselGridState042, besselGridState043, besselGridState048, besselGridState050, besselGridState052, besselGridState057, besselGridState061, besselGridState065, besselGridState071, besselGridState074, besselGridState076, besselStateSubset, linearInterval, widenInterval,
    rationalErrorInterval, rationalIntervalSubset, orderedInterval, Finset.sum_range_succ,
    IntervalRat.add, IntervalRat.mul, IntervalRat.scale, IntervalRat.singleton]

theorem compactCertificate224_stateChecks7 :
    compactCertificate224.stateChecks 21 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 10 12 (120804167469303 / 4000000000000)) (orderedInterval (-60997981921 / 1000000000000) (-60997978522 / 1000000000000), orderedInterval (132768875335 / 1000000000000) (132768878734 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 26 12 (328006814436909 / 4000000000000)) (orderedInterval (78690088002 / 1000000000000) (78690088003 / 1000000000000), orderedInterval (39159567390 / 1000000000000) (39159567391 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 36 12 (447865262948493 / 4000000000000)) (orderedInterval (-25624662532 / 1000000000000) (-25624661721 / 1000000000000), orderedInterval (71031529941 / 1000000000000) (71031530751 / 1000000000000))) = true
  norm_num [besselStateAtRationalPoint, besselIntervalStepZero,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, besselZeroTransition,
    besselInitial, besselGridStateAt, besselGridStateBlock00, besselGridStateBlock01,
    besselGridStateBlock02, besselGridStateBlock03, besselGridStateBlock04,
    besselGridStateBlock05, besselGridStateBlock06, besselGridStateBlock07,
    besselGridStateBlock08, besselGridStateBlock09, besselGridStateBlock10,
    besselGridStateBlock11, besselGridStateBlock12, besselGridStateBlock13,
    besselGridStateBlock14, besselGridState007, besselGridState010, besselGridState015, besselGridState018, besselGridState019, besselGridState024, besselGridState026, besselGridState029, besselGridState033, besselGridState034, besselGridState036, besselGridState038, besselGridState039, besselGridState041, besselGridState042, besselGridState043, besselGridState048, besselGridState050, besselGridState052, besselGridState057, besselGridState061, besselGridState065, besselGridState071, besselGridState074, besselGridState076, besselStateSubset, linearInterval, widenInterval,
    rationalErrorInterval, rationalIntervalSubset, orderedInterval, Finset.sum_range_succ,
    IntervalRat.add, IntervalRat.mul, IntervalRat.scale, IntervalRat.singleton]

theorem compactCertificate224_stateChecks8 :
    compactCertificate224.stateChecks 24 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 15 12 (189374822611191 / 4000000000000)) (orderedInterval (-97735385515 / 1000000000000) (-97735385514 / 1000000000000), orderedInterval (-61371818859 / 1000000000000) (-61371818858 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 61 12 (769798140138711 / 4000000000000)) (orderedInterval (-57495025943 / 1000000000000) (-57495025848 / 1000000000000), orderedInterval (1663890802 / 1000000000000) (1663890897 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 41 12 (514189482038649 / 4000000000000)) (orderedInterval (-35363075734 / 1000000000000) (-35363075733 / 1000000000000), orderedInterval (-60705573025 / 1000000000000) (-60705573024 / 1000000000000))) = true
  norm_num [besselStateAtRationalPoint, besselIntervalStepZero,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, besselZeroTransition,
    besselInitial, besselGridStateAt, besselGridStateBlock00, besselGridStateBlock01,
    besselGridStateBlock02, besselGridStateBlock03, besselGridStateBlock04,
    besselGridStateBlock05, besselGridStateBlock06, besselGridStateBlock07,
    besselGridStateBlock08, besselGridStateBlock09, besselGridStateBlock10,
    besselGridStateBlock11, besselGridStateBlock12, besselGridStateBlock13,
    besselGridStateBlock14, besselGridState007, besselGridState010, besselGridState015, besselGridState018, besselGridState019, besselGridState024, besselGridState026, besselGridState029, besselGridState033, besselGridState034, besselGridState036, besselGridState038, besselGridState039, besselGridState041, besselGridState042, besselGridState043, besselGridState048, besselGridState050, besselGridState052, besselGridState057, besselGridState061, besselGridState065, besselGridState071, besselGridState074, besselGridState076, besselStateSubset, linearInterval, widenInterval,
    rationalErrorInterval, rationalIntervalSubset, orderedInterval, Finset.sum_range_succ,
    IntervalRat.add, IntervalRat.mul, IntervalRat.scale, IntervalRat.singleton]

theorem compactCertificate224_states : ∀ j,
    BesselStateValid (compactCertificate224.point j) (compactCertificate224.state j) :=
  compactCertificate224.statesValid_of_checks3 compactCertificate224_stateChecks0
    compactCertificate224_stateChecks1 compactCertificate224_stateChecks2
    compactCertificate224_stateChecks3 compactCertificate224_stateChecks4
    compactCertificate224_stateChecks5 compactCertificate224_stateChecks6
    compactCertificate224_stateChecks7 compactCertificate224_stateChecks8

theorem compactCertificate224_chunkChecks0_0 :
    compactCertificate224.chunkChecks (0 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 0) <| besselDerivativeNearFromState (207 / 2) 0 (IntervalRat.scale (207 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-45033366364 / 1000000000000) (-45033366363 / 1000000000000), orderedInterval (-63992545483 / 1000000000000) (-63992545482 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 0) <| besselDerivativeNearFromState (304950526215507 / 4000000000000) 0 (IntervalRat.scale (207 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (91254620860 / 1000000000000) (91254620920 / 1000000000000), orderedInterval (-5381965518 / 1000000000000) (-5381965459 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 0) <| besselDerivativeNearFromState (98614734574131 / 800000000000) 0 (IntervalRat.scale (207 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-71806368831 / 1000000000000) (-71806368810 / 1000000000000), orderedInterval (-2590283763 / 1000000000000) (-2590283742 / 1000000000000)))) (orderedInterval (-21213013497 / 1000000000000) (-21213013487 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 0) <| besselDerivativeNearFromState (88983802992249 / 4000000000000) 0 (IntervalRat.scale (207 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-145406008691 / 1000000000000) (-145406008690 / 1000000000000), orderedInterval (-83168338789 / 1000000000000) (-83168338788 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 0) <| besselDerivativeNearFromState (239023011444453 / 4000000000000) 0 (IntervalRat.scale (207 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-77461504745 / 1000000000000) (-77461504744 / 1000000000000), orderedInterval (-67567483507 / 1000000000000) (-67567483506 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 0) <| besselDerivativeNearFromState (648993972669201 / 4000000000000) 0 (IntervalRat.scale (207 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-20279959934 / 1000000000000) (-20279959452 / 1000000000000), orderedInterval (59328599000 / 1000000000000) (59328599482 / 1000000000000)))) (orderedInterval (190992346 / 1000000000000) (190992393 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 0) <| besselDerivativeNearFromState (478046022889113 / 4000000000000) 0 (IntervalRat.scale (207 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (57860141429 / 1000000000000) (57860141430 / 1000000000000), orderedInterval (44244351784 / 1000000000000) (44244351785 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 0) <| besselDerivativeNearFromState (819140008253949 / 4000000000000) 0 (IntervalRat.scale (207 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-54593704942 / 1000000000000) (-54593704938 / 1000000000000), orderedInterval (-11191082879 / 1000000000000) (-11191082876 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 0) <| besselDerivativeNearFromState (603374822611191 / 4000000000000) 0 (IntervalRat.scale (207 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (48019306644 / 1000000000000) (48019306645 / 1000000000000), orderedInterval (43596259657 / 1000000000000) (43596259658 / 1000000000000)))) (orderedInterval (2844420186 / 1000000000000) (2844420193 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate224_chunkChecks0_1 :
    compactCertificate224.chunkChecks (0 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 0) <| besselDerivativeNearFromState (925732142684793 / 4000000000000) 0 (IntervalRat.scale (207 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-13481403441 / 1000000000000) (-13481403320 / 1000000000000), orderedInterval (50714729688 / 1000000000000) (50714729808 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 0) <| besselDerivativeNearFromState (534471701776497 / 4000000000000) 0 (IntervalRat.scale (207 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (43728775324 / 1000000000000) (43728801313 / 1000000000000), orderedInterval (-53570369892 / 1000000000000) (-53570343903 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 0) <| besselDerivativeNearFromState (948429413884773 / 4000000000000) 0 (IntervalRat.scale (207 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-39565250655 / 1000000000000) (-39565167956 / 1000000000000), orderedInterval (33542862187 / 1000000000000) (33542944887 / 1000000000000)))) (orderedInterval (10991483 / 1000000000000) (11005228 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 0) <| besselDerivativeNearFromState (886145785478937 / 4000000000000) 0 (IntervalRat.scale (207 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (35820258754 / 1000000000000) (35820285102 / 1000000000000), orderedInterval (-39962757083 / 1000000000000) (-39962730735 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 0) <| besselDerivativeNearFromState (632395445903721 / 4000000000000) 0 (IntervalRat.scale (207 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (61740982200 / 1000000000000) (61740983295 / 1000000000000), orderedInterval (-14849698272 / 1000000000000) (-14849697177 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 0) <| besselDerivativeNearFromState (717069034333359 / 4000000000000) 0 (IntervalRat.scale (207 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-49530162378 / 1000000000000) (-49530162377 / 1000000000000), orderedInterval (-32997795604 / 1000000000000) (-32997795603 / 1000000000000)))) (orderedInterval (5442388683 / 1000000000000) (5442389276 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 0) <| besselDerivativeNearFromState (597817402622271 / 4000000000000) 0 (IntervalRat.scale (207 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-34531791158 / 1000000000000) (-34531784289 / 1000000000000), orderedInterval (55497765924 / 1000000000000) (55497772793 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 0) <| besselDerivativeNearFromState (528189805199691 / 4000000000000) 0 (IntervalRat.scale (207 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (53736676869 / 1000000000000) (53736676870 / 1000000000000), orderedInterval (43768185737 / 1000000000000) (43768185738 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 0) <| besselDerivativeNearFromState (153089992733409 / 800000000000) 0 (IntervalRat.scale (207 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-28161362730 / 1000000000000) (-28161362729 / 1000000000000), orderedInterval (-50262466613 / 1000000000000) (-50262466612 / 1000000000000)))) (orderedInterval (-4194975308 / 1000000000000) (-4194975218 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate224_chunkChecks0_2 :
    compactCertificate224.chunkChecks (0 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 0) <| besselDerivativeNearFromState (423454976585523 / 4000000000000) 0 (IntervalRat.scale (207 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-12828159474 / 1000000000000) (-12828159396 / 1000000000000), orderedInterval (76539856257 / 1000000000000) (76539856335 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 0) <| besselDerivativeNearFromState (358967473287003 / 4000000000000) 0 (IntervalRat.scale (207 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (46179177284 / 1000000000000) (46179188932 / 1000000000000), orderedInterval (-70694678264 / 1000000000000) (-70694666616 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 0) <| besselDerivativeNearFromState (224625177388809 / 4000000000000) 0 (IntervalRat.scale (207 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (40557812622 / 1000000000000) (40557812623 / 1000000000000), orderedInterval (98086629303 / 1000000000000) (98086629304 / 1000000000000)))) (orderedInterval (757756238 / 1000000000000) (757756937 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 0) <| besselDerivativeNearFromState (120804167469303 / 4000000000000) 0 (IntervalRat.scale (207 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-60997981921 / 1000000000000) (-60997978522 / 1000000000000), orderedInterval (132768875335 / 1000000000000) (132768878734 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 0) <| besselDerivativeNearFromState (328006814436909 / 4000000000000) 0 (IntervalRat.scale (207 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (78690088002 / 1000000000000) (78690088003 / 1000000000000), orderedInterval (39159567390 / 1000000000000) (39159567391 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 0) <| besselDerivativeNearFromState (447865262948493 / 4000000000000) 0 (IntervalRat.scale (207 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-25624662532 / 1000000000000) (-25624661721 / 1000000000000), orderedInterval (71031529941 / 1000000000000) (71031530751 / 1000000000000)))) (orderedInterval (1304948755 / 1000000000000) (1304948893 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 0) <| besselDerivativeNearFromState (189374822611191 / 4000000000000) 0 (IntervalRat.scale (207 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-97735385515 / 1000000000000) (-97735385514 / 1000000000000), orderedInterval (-61371818859 / 1000000000000) (-61371818858 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 0) <| besselDerivativeNearFromState (769798140138711 / 4000000000000) 0 (IntervalRat.scale (207 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-57495025943 / 1000000000000) (-57495025848 / 1000000000000), orderedInterval (1663890802 / 1000000000000) (1663890897 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 0) <| besselDerivativeNearFromState (514189482038649 / 4000000000000) 0 (IntervalRat.scale (207 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-35363075734 / 1000000000000) (-35363075733 / 1000000000000), orderedInterval (-60705573025 / 1000000000000) (-60705573024 / 1000000000000)))) (orderedInterval (10726067381 / 1000000000000) (10726067418 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate224_chunkChecks0 :
    compactCertificate224.chunkChecks (0 : Fin 5) 0 9 = true :=
  compactCertificate224.chunkChecks_nine_of_three (0 : Fin 5) compactCertificate224_chunkChecks0_0
    compactCertificate224_chunkChecks0_1 compactCertificate224_chunkChecks0_2

theorem compactCertificate224_chunkChecks1_0 :
    compactCertificate224.chunkChecks (1 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 1) <| besselDerivativeNearFromState (207 / 2) 1 (IntervalRat.scale (207 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-45033366364 / 1000000000000) (-45033366363 / 1000000000000), orderedInterval (-63992545483 / 1000000000000) (-63992545482 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 1) <| besselDerivativeNearFromState (304950526215507 / 4000000000000) 1 (IntervalRat.scale (207 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (91254620860 / 1000000000000) (91254620920 / 1000000000000), orderedInterval (-5381965518 / 1000000000000) (-5381965459 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 1) <| besselDerivativeNearFromState (98614734574131 / 800000000000) 1 (IntervalRat.scale (207 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-71806368831 / 1000000000000) (-71806368810 / 1000000000000), orderedInterval (-2590283763 / 1000000000000) (-2590283742 / 1000000000000)))) (orderedInterval (-25582377563 / 1000000000000) (-25582377552 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 1) <| besselDerivativeNearFromState (88983802992249 / 4000000000000) 1 (IntervalRat.scale (207 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-145406008691 / 1000000000000) (-145406008690 / 1000000000000), orderedInterval (-83168338789 / 1000000000000) (-83168338788 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 1) <| besselDerivativeNearFromState (239023011444453 / 4000000000000) 1 (IntervalRat.scale (207 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-77461504745 / 1000000000000) (-77461504744 / 1000000000000), orderedInterval (-67567483507 / 1000000000000) (-67567483506 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 1) <| besselDerivativeNearFromState (648993972669201 / 4000000000000) 1 (IntervalRat.scale (207 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-20279959934 / 1000000000000) (-20279959452 / 1000000000000), orderedInterval (59328599000 / 1000000000000) (59328599482 / 1000000000000)))) (orderedInterval (-7842049343 / 1000000000000) (-7842049274 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 1) <| besselDerivativeNearFromState (478046022889113 / 4000000000000) 1 (IntervalRat.scale (207 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (57860141429 / 1000000000000) (57860141430 / 1000000000000), orderedInterval (44244351784 / 1000000000000) (44244351785 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 1) <| besselDerivativeNearFromState (819140008253949 / 4000000000000) 1 (IntervalRat.scale (207 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-54593704942 / 1000000000000) (-54593704938 / 1000000000000), orderedInterval (-11191082879 / 1000000000000) (-11191082876 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 1) <| besselDerivativeNearFromState (603374822611191 / 4000000000000) 1 (IntervalRat.scale (207 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (48019306644 / 1000000000000) (48019306645 / 1000000000000), orderedInterval (43596259657 / 1000000000000) (43596259658 / 1000000000000)))) (orderedInterval (2218565463 / 1000000000000) (2218565474 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate224_chunkChecks1_1 :
    compactCertificate224.chunkChecks (1 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 1) <| besselDerivativeNearFromState (925732142684793 / 4000000000000) 1 (IntervalRat.scale (207 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-13481403441 / 1000000000000) (-13481403320 / 1000000000000), orderedInterval (50714729688 / 1000000000000) (50714729808 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 1) <| besselDerivativeNearFromState (534471701776497 / 4000000000000) 1 (IntervalRat.scale (207 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (43728775324 / 1000000000000) (43728801313 / 1000000000000), orderedInterval (-53570369892 / 1000000000000) (-53570343903 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 1) <| besselDerivativeNearFromState (948429413884773 / 4000000000000) 1 (IntervalRat.scale (207 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-39565250655 / 1000000000000) (-39565167956 / 1000000000000), orderedInterval (33542862187 / 1000000000000) (33542944887 / 1000000000000)))) (orderedInterval (-14350511423 / 1000000000000) (-14350481871 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 1) <| besselDerivativeNearFromState (886145785478937 / 4000000000000) 1 (IntervalRat.scale (207 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (35820258754 / 1000000000000) (35820285102 / 1000000000000), orderedInterval (-39962757083 / 1000000000000) (-39962730735 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 1) <| besselDerivativeNearFromState (632395445903721 / 4000000000000) 1 (IntervalRat.scale (207 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (61740982200 / 1000000000000) (61740983295 / 1000000000000), orderedInterval (-14849698272 / 1000000000000) (-14849697177 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 1) <| besselDerivativeNearFromState (717069034333359 / 4000000000000) 1 (IntervalRat.scale (207 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-49530162378 / 1000000000000) (-49530162377 / 1000000000000), orderedInterval (-32997795604 / 1000000000000) (-32997795603 / 1000000000000)))) (orderedInterval (-311537293 / 1000000000000) (-311536095 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 1) <| besselDerivativeNearFromState (597817402622271 / 4000000000000) 1 (IntervalRat.scale (207 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-34531791158 / 1000000000000) (-34531784289 / 1000000000000), orderedInterval (55497765924 / 1000000000000) (55497772793 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 1) <| besselDerivativeNearFromState (528189805199691 / 4000000000000) 1 (IntervalRat.scale (207 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (53736676869 / 1000000000000) (53736676870 / 1000000000000), orderedInterval (43768185737 / 1000000000000) (43768185738 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 1) <| besselDerivativeNearFromState (153089992733409 / 800000000000) 1 (IntervalRat.scale (207 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-28161362730 / 1000000000000) (-28161362729 / 1000000000000), orderedInterval (-50262466613 / 1000000000000) (-50262466612 / 1000000000000)))) (orderedInterval (-4649538804 / 1000000000000) (-4649538674 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate224_chunkChecks1_2 :
    compactCertificate224.chunkChecks (1 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 1) <| besselDerivativeNearFromState (423454976585523 / 4000000000000) 1 (IntervalRat.scale (207 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-12828159474 / 1000000000000) (-12828159396 / 1000000000000), orderedInterval (76539856257 / 1000000000000) (76539856335 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 1) <| besselDerivativeNearFromState (358967473287003 / 4000000000000) 1 (IntervalRat.scale (207 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (46179177284 / 1000000000000) (46179188932 / 1000000000000), orderedInterval (-70694678264 / 1000000000000) (-70694666616 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 1) <| besselDerivativeNearFromState (224625177388809 / 4000000000000) 1 (IntervalRat.scale (207 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (40557812622 / 1000000000000) (40557812623 / 1000000000000), orderedInterval (98086629303 / 1000000000000) (98086629304 / 1000000000000)))) (orderedInterval (-7315651908 / 1000000000000) (-7315651299 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 1) <| besselDerivativeNearFromState (120804167469303 / 4000000000000) 1 (IntervalRat.scale (207 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-60997981921 / 1000000000000) (-60997978522 / 1000000000000), orderedInterval (132768875335 / 1000000000000) (132768878734 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 1) <| besselDerivativeNearFromState (328006814436909 / 4000000000000) 1 (IntervalRat.scale (207 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (78690088002 / 1000000000000) (78690088003 / 1000000000000), orderedInterval (39159567390 / 1000000000000) (39159567391 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 1) <| besselDerivativeNearFromState (447865262948493 / 4000000000000) 1 (IntervalRat.scale (207 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-25624662532 / 1000000000000) (-25624661721 / 1000000000000), orderedInterval (71031529941 / 1000000000000) (71031530751 / 1000000000000)))) (orderedInterval (-7308320535 / 1000000000000) (-7308320438 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 1) <| besselDerivativeNearFromState (189374822611191 / 4000000000000) 1 (IntervalRat.scale (207 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-97735385515 / 1000000000000) (-97735385514 / 1000000000000), orderedInterval (-61371818859 / 1000000000000) (-61371818858 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 1) <| besselDerivativeNearFromState (769798140138711 / 4000000000000) 1 (IntervalRat.scale (207 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-57495025943 / 1000000000000) (-57495025848 / 1000000000000), orderedInterval (1663890802 / 1000000000000) (1663890897 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 1) <| besselDerivativeNearFromState (514189482038649 / 4000000000000) 1 (IntervalRat.scale (207 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-35363075734 / 1000000000000) (-35363075733 / 1000000000000), orderedInterval (-60705573025 / 1000000000000) (-60705573024 / 1000000000000)))) (orderedInterval (13725310574 / 1000000000000) (13725310630 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate224_chunkChecks1 :
    compactCertificate224.chunkChecks (1 : Fin 5) 0 9 = true :=
  compactCertificate224.chunkChecks_nine_of_three (1 : Fin 5) compactCertificate224_chunkChecks1_0
    compactCertificate224_chunkChecks1_1 compactCertificate224_chunkChecks1_2

theorem compactCertificate224_chunkChecks2_0 :
    compactCertificate224.chunkChecks (2 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 2) <| besselDerivativeNearFromState (207 / 2) 2 (IntervalRat.scale (207 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-45033366364 / 1000000000000) (-45033366363 / 1000000000000), orderedInterval (-63992545483 / 1000000000000) (-63992545482 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 2) <| besselDerivativeNearFromState (304950526215507 / 4000000000000) 2 (IntervalRat.scale (207 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (91254620860 / 1000000000000) (91254620920 / 1000000000000), orderedInterval (-5381965518 / 1000000000000) (-5381965459 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 2) <| besselDerivativeNearFromState (98614734574131 / 800000000000) 2 (IntervalRat.scale (207 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-71806368831 / 1000000000000) (-71806368810 / 1000000000000), orderedInterval (-2590283763 / 1000000000000) (-2590283742 / 1000000000000)))) (orderedInterval (23612480734 / 1000000000000) (23612480746 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 2) <| besselDerivativeNearFromState (88983802992249 / 4000000000000) 2 (IntervalRat.scale (207 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-145406008691 / 1000000000000) (-145406008690 / 1000000000000), orderedInterval (-83168338789 / 1000000000000) (-83168338788 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 2) <| besselDerivativeNearFromState (239023011444453 / 4000000000000) 2 (IntervalRat.scale (207 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-77461504745 / 1000000000000) (-77461504744 / 1000000000000), orderedInterval (-67567483507 / 1000000000000) (-67567483506 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 2) <| besselDerivativeNearFromState (648993972669201 / 4000000000000) 2 (IntervalRat.scale (207 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-20279959934 / 1000000000000) (-20279959452 / 1000000000000), orderedInterval (59328599000 / 1000000000000) (59328599482 / 1000000000000)))) (orderedInterval (-2597219800 / 1000000000000) (-2597219695 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 2) <| besselDerivativeNearFromState (478046022889113 / 4000000000000) 2 (IntervalRat.scale (207 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (57860141429 / 1000000000000) (57860141430 / 1000000000000), orderedInterval (44244351784 / 1000000000000) (44244351785 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 2) <| besselDerivativeNearFromState (819140008253949 / 4000000000000) 2 (IntervalRat.scale (207 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-54593704942 / 1000000000000) (-54593704938 / 1000000000000), orderedInterval (-11191082879 / 1000000000000) (-11191082876 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 2) <| besselDerivativeNearFromState (603374822611191 / 4000000000000) 2 (IntervalRat.scale (207 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (48019306644 / 1000000000000) (48019306645 / 1000000000000), orderedInterval (43596259657 / 1000000000000) (43596259658 / 1000000000000)))) (orderedInterval (-9078691177 / 1000000000000) (-9078691158 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate224_chunkChecks2_1 :
    compactCertificate224.chunkChecks (2 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 2) <| besselDerivativeNearFromState (925732142684793 / 4000000000000) 2 (IntervalRat.scale (207 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-13481403441 / 1000000000000) (-13481403320 / 1000000000000), orderedInterval (50714729688 / 1000000000000) (50714729808 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 2) <| besselDerivativeNearFromState (534471701776497 / 4000000000000) 2 (IntervalRat.scale (207 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (43728775324 / 1000000000000) (43728801313 / 1000000000000), orderedInterval (-53570369892 / 1000000000000) (-53570343903 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 2) <| besselDerivativeNearFromState (948429413884773 / 4000000000000) 2 (IntervalRat.scale (207 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-39565250655 / 1000000000000) (-39565167956 / 1000000000000), orderedInterval (33542862187 / 1000000000000) (33542944887 / 1000000000000)))) (orderedInterval (12279351762 / 1000000000000) (12279417245 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 2) <| besselDerivativeNearFromState (886145785478937 / 4000000000000) 2 (IntervalRat.scale (207 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (35820258754 / 1000000000000) (35820285102 / 1000000000000), orderedInterval (-39962757083 / 1000000000000) (-39962730735 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 2) <| besselDerivativeNearFromState (632395445903721 / 4000000000000) 2 (IntervalRat.scale (207 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (61740982200 / 1000000000000) (61740983295 / 1000000000000), orderedInterval (-14849698272 / 1000000000000) (-14849697177 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 2) <| besselDerivativeNearFromState (717069034333359 / 4000000000000) 2 (IntervalRat.scale (207 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-49530162378 / 1000000000000) (-49530162377 / 1000000000000), orderedInterval (-32997795604 / 1000000000000) (-32997795603 / 1000000000000)))) (orderedInterval (-11409172143 / 1000000000000) (-11409169677 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 2) <| besselDerivativeNearFromState (597817402622271 / 4000000000000) 2 (IntervalRat.scale (207 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-34531791158 / 1000000000000) (-34531784289 / 1000000000000), orderedInterval (55497765924 / 1000000000000) (55497772793 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 2) <| besselDerivativeNearFromState (528189805199691 / 4000000000000) 2 (IntervalRat.scale (207 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (53736676869 / 1000000000000) (53736676870 / 1000000000000), orderedInterval (43768185737 / 1000000000000) (43768185738 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 2) <| besselDerivativeNearFromState (153089992733409 / 800000000000) 2 (IntervalRat.scale (207 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-28161362730 / 1000000000000) (-28161362729 / 1000000000000), orderedInterval (-50262466613 / 1000000000000) (-50262466612 / 1000000000000)))) (orderedInterval (8346780685 / 1000000000000) (8346780874 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate224_chunkChecks2_2 :
    compactCertificate224.chunkChecks (2 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 2) <| besselDerivativeNearFromState (423454976585523 / 4000000000000) 2 (IntervalRat.scale (207 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-12828159474 / 1000000000000) (-12828159396 / 1000000000000), orderedInterval (76539856257 / 1000000000000) (76539856335 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 2) <| besselDerivativeNearFromState (358967473287003 / 4000000000000) 2 (IntervalRat.scale (207 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (46179177284 / 1000000000000) (46179188932 / 1000000000000), orderedInterval (-70694678264 / 1000000000000) (-70694666616 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 2) <| besselDerivativeNearFromState (224625177388809 / 4000000000000) 2 (IntervalRat.scale (207 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (40557812622 / 1000000000000) (40557812623 / 1000000000000), orderedInterval (98086629303 / 1000000000000) (98086629304 / 1000000000000)))) (orderedInterval (-498856541 / 1000000000000) (-498856003 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 2) <| besselDerivativeNearFromState (120804167469303 / 4000000000000) 2 (IntervalRat.scale (207 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-60997981921 / 1000000000000) (-60997978522 / 1000000000000), orderedInterval (132768875335 / 1000000000000) (132768878734 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 2) <| besselDerivativeNearFromState (328006814436909 / 4000000000000) 2 (IntervalRat.scale (207 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (78690088002 / 1000000000000) (78690088003 / 1000000000000), orderedInterval (39159567390 / 1000000000000) (39159567391 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 2) <| besselDerivativeNearFromState (447865262948493 / 4000000000000) 2 (IntervalRat.scale (207 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-25624662532 / 1000000000000) (-25624661721 / 1000000000000), orderedInterval (71031529941 / 1000000000000) (71031530751 / 1000000000000)))) (orderedInterval (-1202939392 / 1000000000000) (-1202939301 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 2) <| besselDerivativeNearFromState (189374822611191 / 4000000000000) 2 (IntervalRat.scale (207 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-97735385515 / 1000000000000) (-97735385514 / 1000000000000), orderedInterval (-61371818859 / 1000000000000) (-61371818858 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 2) <| besselDerivativeNearFromState (769798140138711 / 4000000000000) 2 (IntervalRat.scale (207 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-57495025943 / 1000000000000) (-57495025848 / 1000000000000), orderedInterval (1663890802 / 1000000000000) (1663890897 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 2) <| besselDerivativeNearFromState (514189482038649 / 4000000000000) 2 (IntervalRat.scale (207 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-35363075734 / 1000000000000) (-35363075733 / 1000000000000), orderedInterval (-60705573025 / 1000000000000) (-60705573024 / 1000000000000)))) (orderedInterval (-26425822650 / 1000000000000) (-26425822563 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate224_chunkChecks2 :
    compactCertificate224.chunkChecks (2 : Fin 5) 0 9 = true :=
  compactCertificate224.chunkChecks_nine_of_three (2 : Fin 5) compactCertificate224_chunkChecks2_0
    compactCertificate224_chunkChecks2_1 compactCertificate224_chunkChecks2_2

theorem compactCertificate224_chunkChecks3_0 :
    compactCertificate224.chunkChecks (3 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 3) <| besselDerivativeNearFromState (207 / 2) 3 (IntervalRat.scale (207 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-45033366364 / 1000000000000) (-45033366363 / 1000000000000), orderedInterval (-63992545483 / 1000000000000) (-63992545482 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 3) <| besselDerivativeNearFromState (304950526215507 / 4000000000000) 3 (IntervalRat.scale (207 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (91254620860 / 1000000000000) (91254620920 / 1000000000000), orderedInterval (-5381965518 / 1000000000000) (-5381965459 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 3) <| besselDerivativeNearFromState (98614734574131 / 800000000000) 3 (IntervalRat.scale (207 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-71806368831 / 1000000000000) (-71806368810 / 1000000000000), orderedInterval (-2590283763 / 1000000000000) (-2590283742 / 1000000000000)))) (orderedInterval (25410710657 / 1000000000000) (25410710672 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 3) <| besselDerivativeNearFromState (88983802992249 / 4000000000000) 3 (IntervalRat.scale (207 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-145406008691 / 1000000000000) (-145406008690 / 1000000000000), orderedInterval (-83168338789 / 1000000000000) (-83168338788 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 3) <| besselDerivativeNearFromState (239023011444453 / 4000000000000) 3 (IntervalRat.scale (207 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-77461504745 / 1000000000000) (-77461504744 / 1000000000000), orderedInterval (-67567483507 / 1000000000000) (-67567483506 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 3) <| besselDerivativeNearFromState (648993972669201 / 4000000000000) 3 (IntervalRat.scale (207 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-20279959934 / 1000000000000) (-20279959452 / 1000000000000), orderedInterval (59328599000 / 1000000000000) (59328599482 / 1000000000000)))) (orderedInterval (16737858753 / 1000000000000) (16737858915 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 3) <| besselDerivativeNearFromState (478046022889113 / 4000000000000) 3 (IntervalRat.scale (207 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (57860141429 / 1000000000000) (57860141430 / 1000000000000), orderedInterval (44244351784 / 1000000000000) (44244351785 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 3) <| besselDerivativeNearFromState (819140008253949 / 4000000000000) 3 (IntervalRat.scale (207 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-54593704942 / 1000000000000) (-54593704938 / 1000000000000), orderedInterval (-11191082879 / 1000000000000) (-11191082876 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 3) <| besselDerivativeNearFromState (603374822611191 / 4000000000000) 3 (IntervalRat.scale (207 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (48019306644 / 1000000000000) (48019306645 / 1000000000000), orderedInterval (43596259657 / 1000000000000) (43596259658 / 1000000000000)))) (orderedInterval (-5847550004 / 1000000000000) (-5847549969 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate224_chunkChecks3_1 :
    compactCertificate224.chunkChecks (3 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 3) <| besselDerivativeNearFromState (925732142684793 / 4000000000000) 3 (IntervalRat.scale (207 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-13481403441 / 1000000000000) (-13481403320 / 1000000000000), orderedInterval (50714729688 / 1000000000000) (50714729808 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 3) <| besselDerivativeNearFromState (534471701776497 / 4000000000000) 3 (IntervalRat.scale (207 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (43728775324 / 1000000000000) (43728801313 / 1000000000000), orderedInterval (-53570369892 / 1000000000000) (-53570343903 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 3) <| besselDerivativeNearFromState (948429413884773 / 4000000000000) 3 (IntervalRat.scale (207 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-39565250655 / 1000000000000) (-39565167956 / 1000000000000), orderedInterval (33542862187 / 1000000000000) (33542944887 / 1000000000000)))) (orderedInterval (51840915628 / 1000000000000) (51841062379 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 3) <| besselDerivativeNearFromState (886145785478937 / 4000000000000) 3 (IntervalRat.scale (207 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (35820258754 / 1000000000000) (35820285102 / 1000000000000), orderedInterval (-39962757083 / 1000000000000) (-39962730735 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 3) <| besselDerivativeNearFromState (632395445903721 / 4000000000000) 3 (IntervalRat.scale (207 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (61740982200 / 1000000000000) (61740983295 / 1000000000000), orderedInterval (-14849698272 / 1000000000000) (-14849697177 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 3) <| besselDerivativeNearFromState (717069034333359 / 4000000000000) 3 (IntervalRat.scale (207 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-49530162378 / 1000000000000) (-49530162377 / 1000000000000), orderedInterval (-32997795604 / 1000000000000) (-32997795603 / 1000000000000)))) (orderedInterval (-2827415582 / 1000000000000) (-2827410469 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 3) <| besselDerivativeNearFromState (597817402622271 / 4000000000000) 3 (IntervalRat.scale (207 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-34531791158 / 1000000000000) (-34531784289 / 1000000000000), orderedInterval (55497765924 / 1000000000000) (55497772793 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 3) <| besselDerivativeNearFromState (528189805199691 / 4000000000000) 3 (IntervalRat.scale (207 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (53736676869 / 1000000000000) (53736676870 / 1000000000000), orderedInterval (43768185737 / 1000000000000) (43768185738 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 3) <| besselDerivativeNearFromState (153089992733409 / 800000000000) 3 (IntervalRat.scale (207 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-28161362730 / 1000000000000) (-28161362729 / 1000000000000), orderedInterval (-50262466613 / 1000000000000) (-50262466612 / 1000000000000)))) (orderedInterval (11324683406 / 1000000000000) (11324683680 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate224_chunkChecks3_2 :
    compactCertificate224.chunkChecks (3 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 3) <| besselDerivativeNearFromState (423454976585523 / 4000000000000) 3 (IntervalRat.scale (207 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-12828159474 / 1000000000000) (-12828159396 / 1000000000000), orderedInterval (76539856257 / 1000000000000) (76539856335 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 3) <| besselDerivativeNearFromState (358967473287003 / 4000000000000) 3 (IntervalRat.scale (207 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (46179177284 / 1000000000000) (46179188932 / 1000000000000), orderedInterval (-70694678264 / 1000000000000) (-70694666616 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 3) <| besselDerivativeNearFromState (224625177388809 / 4000000000000) 3 (IntervalRat.scale (207 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (40557812622 / 1000000000000) (40557812623 / 1000000000000), orderedInterval (98086629303 / 1000000000000) (98086629304 / 1000000000000)))) (orderedInterval (9981666211 / 1000000000000) (9981666682 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 3) <| besselDerivativeNearFromState (120804167469303 / 4000000000000) 3 (IntervalRat.scale (207 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-60997981921 / 1000000000000) (-60997978522 / 1000000000000), orderedInterval (132768875335 / 1000000000000) (132768878734 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 3) <| besselDerivativeNearFromState (328006814436909 / 4000000000000) 3 (IntervalRat.scale (207 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (78690088002 / 1000000000000) (78690088003 / 1000000000000), orderedInterval (39159567390 / 1000000000000) (39159567391 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 3) <| besselDerivativeNearFromState (447865262948493 / 4000000000000) 3 (IntervalRat.scale (207 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-25624662532 / 1000000000000) (-25624661721 / 1000000000000), orderedInterval (71031529941 / 1000000000000) (71031530751 / 1000000000000)))) (orderedInterval (7405623980 / 1000000000000) (7405624073 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 3) <| besselDerivativeNearFromState (189374822611191 / 4000000000000) 3 (IntervalRat.scale (207 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-97735385515 / 1000000000000) (-97735385514 / 1000000000000), orderedInterval (-61371818859 / 1000000000000) (-61371818858 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 3) <| besselDerivativeNearFromState (769798140138711 / 4000000000000) 3 (IntervalRat.scale (207 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-57495025943 / 1000000000000) (-57495025848 / 1000000000000), orderedInterval (1663890802 / 1000000000000) (1663890897 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 3) <| besselDerivativeNearFromState (514189482038649 / 4000000000000) 3 (IntervalRat.scale (207 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-35363075734 / 1000000000000) (-35363075733 / 1000000000000), orderedInterval (-60705573025 / 1000000000000) (-60705573024 / 1000000000000)))) (orderedInterval (-20659085751 / 1000000000000) (-20659085608 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate224_chunkChecks3 :
    compactCertificate224.chunkChecks (3 : Fin 5) 0 9 = true :=
  compactCertificate224.chunkChecks_nine_of_three (3 : Fin 5) compactCertificate224_chunkChecks3_0
    compactCertificate224_chunkChecks3_1 compactCertificate224_chunkChecks3_2

theorem compactCertificate224_chunkChecks4_0 :
    compactCertificate224.chunkChecks (4 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 4) <| besselDerivativeNearFromState (207 / 2) 4 (IntervalRat.scale (207 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-45033366364 / 1000000000000) (-45033366363 / 1000000000000), orderedInterval (-63992545483 / 1000000000000) (-63992545482 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 4) <| besselDerivativeNearFromState (304950526215507 / 4000000000000) 4 (IntervalRat.scale (207 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (91254620860 / 1000000000000) (91254620920 / 1000000000000), orderedInterval (-5381965518 / 1000000000000) (-5381965459 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 4) <| besselDerivativeNearFromState (98614734574131 / 800000000000) 4 (IntervalRat.scale (207 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-71806368831 / 1000000000000) (-71806368810 / 1000000000000), orderedInterval (-2590283763 / 1000000000000) (-2590283742 / 1000000000000)))) (orderedInterval (-26566403362 / 1000000000000) (-26566403345 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 4) <| besselDerivativeNearFromState (88983802992249 / 4000000000000) 4 (IntervalRat.scale (207 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-145406008691 / 1000000000000) (-145406008690 / 1000000000000), orderedInterval (-83168338789 / 1000000000000) (-83168338788 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 4) <| besselDerivativeNearFromState (239023011444453 / 4000000000000) 4 (IntervalRat.scale (207 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-77461504745 / 1000000000000) (-77461504744 / 1000000000000), orderedInterval (-67567483507 / 1000000000000) (-67567483506 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 4) <| besselDerivativeNearFromState (648993972669201 / 4000000000000) 4 (IntervalRat.scale (207 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-20279959934 / 1000000000000) (-20279959452 / 1000000000000), orderedInterval (59328599000 / 1000000000000) (59328599482 / 1000000000000)))) (orderedInterval (8071765392 / 1000000000000) (8071765648 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 4) <| besselDerivativeNearFromState (478046022889113 / 4000000000000) 4 (IntervalRat.scale (207 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (57860141429 / 1000000000000) (57860141430 / 1000000000000), orderedInterval (44244351784 / 1000000000000) (44244351785 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 4) <| besselDerivativeNearFromState (819140008253949 / 4000000000000) 4 (IntervalRat.scale (207 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-54593704942 / 1000000000000) (-54593704938 / 1000000000000), orderedInterval (-11191082879 / 1000000000000) (-11191082876 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 4) <| besselDerivativeNearFromState (603374822611191 / 4000000000000) 4 (IntervalRat.scale (207 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (48019306644 / 1000000000000) (48019306645 / 1000000000000), orderedInterval (43596259657 / 1000000000000) (43596259658 / 1000000000000)))) (orderedInterval (31155617250 / 1000000000000) (31155617313 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate224_chunkChecks4_1 :
    compactCertificate224.chunkChecks (4 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 4) <| besselDerivativeNearFromState (925732142684793 / 4000000000000) 4 (IntervalRat.scale (207 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-13481403441 / 1000000000000) (-13481403320 / 1000000000000), orderedInterval (50714729688 / 1000000000000) (50714729808 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 4) <| besselDerivativeNearFromState (534471701776497 / 4000000000000) 4 (IntervalRat.scale (207 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (43728775324 / 1000000000000) (43728801313 / 1000000000000), orderedInterval (-53570369892 / 1000000000000) (-53570343903 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 4) <| besselDerivativeNearFromState (948429413884773 / 4000000000000) 4 (IntervalRat.scale (207 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-39565250655 / 1000000000000) (-39565167956 / 1000000000000), orderedInterval (33542862187 / 1000000000000) (33542944887 / 1000000000000)))) (orderedInterval (-87030125618 / 1000000000000) (-87029792241 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 4) <| besselDerivativeNearFromState (886145785478937 / 4000000000000) 4 (IntervalRat.scale (207 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (35820258754 / 1000000000000) (35820285102 / 1000000000000), orderedInterval (-39962757083 / 1000000000000) (-39962730735 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 4) <| besselDerivativeNearFromState (632395445903721 / 4000000000000) 4 (IntervalRat.scale (207 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (61740982200 / 1000000000000) (61740983295 / 1000000000000), orderedInterval (-14849698272 / 1000000000000) (-14849697177 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 4) <| besselDerivativeNearFromState (717069034333359 / 4000000000000) 4 (IntervalRat.scale (207 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-49530162378 / 1000000000000) (-49530162377 / 1000000000000), orderedInterval (-32997795604 / 1000000000000) (-32997795603 / 1000000000000)))) (orderedInterval (20522549446 / 1000000000000) (20522560189 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 4) <| besselDerivativeNearFromState (597817402622271 / 4000000000000) 4 (IntervalRat.scale (207 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-34531791158 / 1000000000000) (-34531784289 / 1000000000000), orderedInterval (55497765924 / 1000000000000) (55497772793 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 4) <| besselDerivativeNearFromState (528189805199691 / 4000000000000) 4 (IntervalRat.scale (207 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (53736676869 / 1000000000000) (53736676870 / 1000000000000), orderedInterval (43768185737 / 1000000000000) (43768185738 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 4) <| besselDerivativeNearFromState (153089992733409 / 800000000000) 4 (IntervalRat.scale (207 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-28161362730 / 1000000000000) (-28161362729 / 1000000000000), orderedInterval (-50262466613 / 1000000000000) (-50262466612 / 1000000000000)))) (orderedInterval (-18525467007 / 1000000000000) (-18525466604 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate224_chunkChecks4_2 :
    compactCertificate224.chunkChecks (4 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 4) <| besselDerivativeNearFromState (423454976585523 / 4000000000000) 4 (IntervalRat.scale (207 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-12828159474 / 1000000000000) (-12828159396 / 1000000000000), orderedInterval (76539856257 / 1000000000000) (76539856335 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 4) <| besselDerivativeNearFromState (358967473287003 / 4000000000000) 4 (IntervalRat.scale (207 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (46179177284 / 1000000000000) (46179188932 / 1000000000000), orderedInterval (-70694678264 / 1000000000000) (-70694666616 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 4) <| besselDerivativeNearFromState (224625177388809 / 4000000000000) 4 (IntervalRat.scale (207 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (40557812622 / 1000000000000) (40557812623 / 1000000000000), orderedInterval (98086629303 / 1000000000000) (98086629304 / 1000000000000)))) (orderedInterval (689179495 / 1000000000000) (689179912 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 4) <| besselDerivativeNearFromState (120804167469303 / 4000000000000) 4 (IntervalRat.scale (207 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-60997981921 / 1000000000000) (-60997978522 / 1000000000000), orderedInterval (132768875335 / 1000000000000) (132768878734 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 4) <| besselDerivativeNearFromState (328006814436909 / 4000000000000) 4 (IntervalRat.scale (207 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (78690088002 / 1000000000000) (78690088003 / 1000000000000), orderedInterval (39159567390 / 1000000000000) (39159567391 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 4) <| besselDerivativeNearFromState (447865262948493 / 4000000000000) 4 (IntervalRat.scale (207 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-25624662532 / 1000000000000) (-25624661721 / 1000000000000), orderedInterval (71031529941 / 1000000000000) (71031530751 / 1000000000000)))) (orderedInterval (1851167822 / 1000000000000) (1851167922 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 4) <| besselDerivativeNearFromState (189374822611191 / 4000000000000) 4 (IntervalRat.scale (207 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-97735385515 / 1000000000000) (-97735385514 / 1000000000000), orderedInterval (-61371818859 / 1000000000000) (-61371818858 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 4) <| besselDerivativeNearFromState (769798140138711 / 4000000000000) 4 (IntervalRat.scale (207 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-57495025943 / 1000000000000) (-57495025848 / 1000000000000), orderedInterval (1663890802 / 1000000000000) (1663890897 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 4) <| besselDerivativeNearFromState (514189482038649 / 4000000000000) 4 (IntervalRat.scale (207 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-35363075734 / 1000000000000) (-35363075733 / 1000000000000), orderedInterval (-60705573025 / 1000000000000) (-60705573024 / 1000000000000)))) (orderedInterval (72105398076 / 1000000000000) (72105398318 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate224_chunkChecks4 :
    compactCertificate224.chunkChecks (4 : Fin 5) 0 9 = true :=
  compactCertificate224.chunkChecks_nine_of_three (4 : Fin 5) compactCertificate224_chunkChecks4_0
    compactCertificate224_chunkChecks4_1 compactCertificate224_chunkChecks4_2

theorem compactCertificate224_chunks :
    ∀ r : Fin 5, ∀ b, compactCertificate224.chunkCheck r b = true :=
  compactCertificate224.chunkChecks_all (by
    intro r
    fin_cases r
    · exact compactCertificate224_chunkChecks0
    · exact compactCertificate224_chunkChecks1
    · exact compactCertificate224_chunkChecks2
    · exact compactCertificate224_chunkChecks3
    · exact compactCertificate224_chunkChecks4)

theorem compactCertificate224_coefficient0 :
    compactCertificate224.coefficientCheck (0 : Fin 5) = true := by
  norm_num [CompactCertificate.coefficientCheck, intervalFinSumHull,
    compactCertificate224, rationalIntervalSubset, orderedInterval, Fin.sum_univ_succ]

theorem compactCertificate224_coefficient1 :
    compactCertificate224.coefficientCheck (1 : Fin 5) = true := by
  norm_num [CompactCertificate.coefficientCheck, intervalFinSumHull,
    compactCertificate224, rationalIntervalSubset, orderedInterval, Fin.sum_univ_succ]

theorem compactCertificate224_coefficient2 :
    compactCertificate224.coefficientCheck (2 : Fin 5) = true := by
  norm_num [CompactCertificate.coefficientCheck, intervalFinSumHull,
    compactCertificate224, rationalIntervalSubset, orderedInterval, Fin.sum_univ_succ]

theorem compactCertificate224_coefficient3 :
    compactCertificate224.coefficientCheck (3 : Fin 5) = true := by
  norm_num [CompactCertificate.coefficientCheck, intervalFinSumHull,
    compactCertificate224, rationalIntervalSubset, orderedInterval, Fin.sum_univ_succ]

theorem compactCertificate224_coefficient4 :
    compactCertificate224.coefficientCheck (4 : Fin 5) = true := by
  norm_num [CompactCertificate.coefficientCheck, intervalFinSumHull,
    compactCertificate224, rationalIntervalSubset, orderedInterval, Fin.sum_univ_succ]

theorem compactCertificate224_coefficients : ∀ r : Fin 5,
    compactCertificate224.coefficientCheck r = true := by
  intro r
  fin_cases r
  · exact compactCertificate224_coefficient0
  · exact compactCertificate224_coefficient1
  · exact compactCertificate224_coefficient2
  · exact compactCertificate224_coefficient3
  · exact compactCertificate224_coefficient4

theorem compactCertificate224_lower : (1 : ℚ) ≤ compactCertificate224.output.lo := by
  norm_num [CompactCertificate.output, CompactCertificate.interval,
    CompactCertificate.coefficientTargetNat, compactCertificate224, dualConstant,
    intervalTaylorSum, intervalPow, intervalSub, intervalMaxAbs, widenInterval,
    rationalErrorInterval, orderedInterval, IntervalRat.add, IntervalRat.mul, IntervalRat.scale,
    IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4]

theorem compactCertificate224_proves {t : ℝ} (ht : t ∈ compactCertificate224.interval) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t :=
  compactCertificate224.proves compactCertificate224_states compactCertificate224_chunks
    compactCertificate224_coefficients compactCertificate224_lower ht

end Erdos232
