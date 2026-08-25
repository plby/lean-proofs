/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, OpenAI Codex
-/
import ErdosProblems.Erdos232.CompactBase

open LeanCert.Core
namespace Erdos232

def compactCertificate227 : CompactCertificate where
  left := 105
  right := 211 / 2
  center := 421 / 4
  grid := fun i =>
    match i.val with
    | 0 => 34
    | 1 => 25
    | 2 => 40
    | 3 => 7
    | 4 => 19
    | 5 => 53
    | 6 => 39
    | 7 => 66
    | 8 => 49
    | 9 => 75
    | 10 => 43
    | 11 => 77
    | 12 => 72
    | 13 => 51
    | 14 => 58
    | 15 => 48
    | 16 => 43
    | 17 => 62
    | 18 => 34
    | 19 => 29
    | 20 => 18
    | 21 => 10
    | 22 => 27
    | 23 => 36
    | 24 => 15
    | 25 => 62
    | _ => 42
  point := fun i =>
    match i.val with
    | 0 => 421 / 4
    | 1 => 620213389066321 / 8000000000000
    | 2 => 200564266935793 / 1600000000000
    | 3 => 180976720095347 / 8000000000000
    | 4 => 486128926657559 / 8000000000000
    | 5 => 1319934601419003 / 8000000000000
    | 6 => 972257853315539 / 8000000000000
    | 7 => 1665980403260447 / 8000000000000
    | 8 => 1227153624730973 / 8000000000000
    | 9 => 1882769237054579 / 8000000000000
    | 10 => 1087017325835291 / 8000000000000
    | 11 => 1928931320026519 / 8000000000000
    | 12 => 1802257853558611 / 8000000000000
    | 13 => 1286176245050563 / 8000000000000
    | 14 => 1458386779972677 / 8000000000000
    | 15 => 1215850852676213 / 8000000000000
    | 16 => 1074241101396473 / 8000000000000
    | 17 => 311356941742827 / 1600000000000
    | 18 => 861229686678769 / 8000000000000
    | 19 => 730073943255209 / 8000000000000
    | 20 => 456846375269027 / 8000000000000
    | 21 => 245693500022109 / 8000000000000
    | 22 => 667105646753327 / 8000000000000
    | 23 => 910875728025679 / 8000000000000
    | 24 => 385153624730973 / 8000000000000
    | 25 => 1565628101441533 / 8000000000000
    | _ => 1045767014194547 / 8000000000000
  state := fun i =>
    match i.val with
    | 0 => (orderedInterval (-54692556856 / 1000000000000) (-54692488708 / 1000000000000), orderedInterval (55553291693 / 1000000000000) (55553359841 / 1000000000000))
    | 1 => (orderedInterval (20601894409 / 1000000000000) (20601894636 / 1000000000000), orderedInterval (-88378756332 / 1000000000000) (-88378756105 / 1000000000000))
    | 2 => (orderedInterval (32487997928 / 1000000000000) (32487997929 / 1000000000000), orderedInterval (63298983855 / 1000000000000) (63298983856 / 1000000000000))
    | 3 => (orderedInterval (-165592097429 / 1000000000000) (-165592097427 / 1000000000000), orderedInterval (-23067525142 / 1000000000000) (-23067525140 / 1000000000000))
    | 4 => (orderedInterval (-98126141562 / 1000000000000) (-98126140369 / 1000000000000), orderedInterval (29919582428 / 1000000000000) (29919583620 / 1000000000000))
    | 5 => (orderedInterval (41328460328 / 1000000000000) (41328493359 / 1000000000000), orderedInterval (-46498222697 / 1000000000000) (-46498189666 / 1000000000000))
    | 6 => (orderedInterval (14769595595 / 1000000000000) (14769595717 / 1000000000000), orderedInterval (-70913984455 / 1000000000000) (-70913984332 / 1000000000000))
    | 7 => (orderedInterval (54915990818 / 1000000000000) (54915991174 / 1000000000000), orderedInterval (-6555170880 / 1000000000000) (-6555170525 / 1000000000000))
    | 8 => (orderedInterval (-15359985930 / 1000000000000) (-15359985929 / 1000000000000), orderedInterval (-62514387557 / 1000000000000) (-62514387556 / 1000000000000))
    | 9 => (orderedInterval (-25461402971 / 1000000000000) (-25461402970 / 1000000000000), orderedInterval (-45297377836 / 1000000000000) (-45297377835 / 1000000000000))
    | 10 => (orderedInterval (-68448532078 / 1000000000000) (-68448532034 / 1000000000000), orderedInterval (413655251 / 1000000000000) (413655295 / 1000000000000))
    | 11 => (orderedInterval (68832524 / 1000000000000) (68832527 / 1000000000000), orderedInterval (-51384005585 / 1000000000000) (-51384005583 / 1000000000000))
    | 12 => (orderedInterval (-6764476947 / 1000000000000) (-6764476929 / 1000000000000), orderedInterval (52741905080 / 1000000000000) (52741905098 / 1000000000000))
    | 13 => (orderedInterval (-61191519387 / 1000000000000) (-61191519385 / 1000000000000), orderedInterval (-14484431128 / 1000000000000) (-14484431126 / 1000000000000))
    | 14 => (orderedInterval (45193854000 / 1000000000000) (45193854001 / 1000000000000), orderedInterval (37950965088 / 1000000000000) (37950965089 / 1000000000000))
    | 15 => (orderedInterval (59644781128 / 1000000000000) (59644787700 / 1000000000000), orderedInterval (-25321622337 / 1000000000000) (-25321615765 / 1000000000000))
    | 16 => (orderedInterval (1644030530 / 1000000000000) (1644030538 / 1000000000000), orderedInterval (-68841522427 / 1000000000000) (-68841522420 / 1000000000000))
    | 17 => (orderedInterval (32488887206 / 1000000000000) (32488887207 / 1000000000000), orderedInterval (46990248528 / 1000000000000) (46990248529 / 1000000000000))
    | 18 => (orderedInterval (76791461505 / 1000000000000) (76791461581 / 1000000000000), orderedInterval (-4430564054 / 1000000000000) (-4430563978 / 1000000000000))
    | 19 => (orderedInterval (-67304572287 / 1000000000000) (-67304572286 / 1000000000000), orderedInterval (-49088426683 / 1000000000000) (-49088426682 / 1000000000000))
    | 20 => (orderedInterval (102791036670 / 1000000000000) (102791036671 / 1000000000000), orderedInterval (23218446716 / 1000000000000) (23218446717 / 1000000000000))
    | 21 => (orderedInterval (11087518805 / 1000000000000) (11087518809 / 1000000000000), orderedInterval (143376794429 / 1000000000000) (143376794432 / 1000000000000))
    | 22 => (orderedInterval (52940082019 / 1000000000000) (52940105637 / 1000000000000), orderedInterval (-69828531749 / 1000000000000) (-69828508131 / 1000000000000))
    | 23 => (orderedInterval (74752284300 / 1000000000000) (74752284325 / 1000000000000), orderedInterval (1493494866 / 1000000000000) (1493494891 / 1000000000000))
    | 24 => (orderedInterval (-111899838650 / 1000000000000) (-111899838086 / 1000000000000), orderedInterval (27637949193 / 1000000000000) (27637949758 / 1000000000000))
    | 25 => (orderedInterval (56486838640 / 1000000000000) (56486839076 / 1000000000000), orderedInterval (-8031498693 / 1000000000000) (-8031498258 / 1000000000000))
    | _ => (orderedInterval (-29823717140 / 1000000000000) (-29823714949 / 1000000000000), orderedInterval (63206370285 / 1000000000000) (63206372476 / 1000000000000))
  chunkTarget := fun r b =>
    match r.val with
    | 0 =>
      match b.val with
      | 0 => orderedInterval (-19579812477 / 1000000000000) (-19579785455 / 1000000000000)
      | 1 => orderedInterval (-4724227667 / 1000000000000) (-4724225262 / 1000000000000)
      | 2 => orderedInterval (-2065049445 / 1000000000000) (-2065049427 / 1000000000000)
      | 3 => orderedInterval (-537504150 / 1000000000000) (-537504103 / 1000000000000)
      | 4 => orderedInterval (-5893032704 / 1000000000000) (-5893032690 / 1000000000000)
      | 5 => orderedInterval (1426519683 / 1000000000000) (1426519771 / 1000000000000)
      | 6 => orderedInterval (-5122548445 / 1000000000000) (-5122548406 / 1000000000000)
      | 7 => orderedInterval (-7134707810 / 1000000000000) (-7134707259 / 1000000000000)
      | _ => orderedInterval (323022035 / 1000000000000) (323022515 / 1000000000000)
    | 1 =>
      match b.val with
      | 0 => orderedInterval (25836694825 / 1000000000000) (25836721847 / 1000000000000)
      | 1 => orderedInterval (5866322549 / 1000000000000) (5866326271 / 1000000000000)
      | 2 => orderedInterval (-1801904521 / 1000000000000) (-1801904489 / 1000000000000)
      | 3 => orderedInterval (1303311914 / 1000000000000) (1303312007 / 1000000000000)
      | 4 => orderedInterval (-4462919011 / 1000000000000) (-4462918989 / 1000000000000)
      | 5 => orderedInterval (6828446097 / 1000000000000) (6828446222 / 1000000000000)
      | 6 => orderedInterval (3543787058 / 1000000000000) (3543787096 / 1000000000000)
      | 7 => orderedInterval (358785386 / 1000000000000) (358785825 / 1000000000000)
      | _ => orderedInterval (-13437301343 / 1000000000000) (-13437300723 / 1000000000000)
    | 2 =>
      match b.val with
      | 0 => orderedInterval (18624315754 / 1000000000000) (18624343034 / 1000000000000)
      | 1 => orderedInterval (8275501477 / 1000000000000) (8275507318 / 1000000000000)
      | 2 => orderedInterval (7436720607 / 1000000000000) (7436720669 / 1000000000000)
      | 3 => orderedInterval (-14232200854 / 1000000000000) (-14232200659 / 1000000000000)
      | 4 => orderedInterval (13670735975 / 1000000000000) (13670736011 / 1000000000000)
      | 5 => orderedInterval (-4191541002 / 1000000000000) (-4191540819 / 1000000000000)
      | 6 => orderedInterval (8962828446 / 1000000000000) (8962828483 / 1000000000000)
      | 7 => orderedInterval (7472460337 / 1000000000000) (7472460692 / 1000000000000)
      | _ => orderedInterval (7534706078 / 1000000000000) (7534706902 / 1000000000000)
    | 3 =>
      match b.val with
      | 0 => orderedInterval (-28140134139 / 1000000000000) (-28140106863 / 1000000000000)
      | 1 => orderedInterval (-13024782930 / 1000000000000) (-13024773791 / 1000000000000)
      | 2 => orderedInterval (3040202936 / 1000000000000) (3040203055 / 1000000000000)
      | 3 => orderedInterval (-2096180882 / 1000000000000) (-2096180463 / 1000000000000)
      | 4 => orderedInterval (15086840864 / 1000000000000) (15086840926 / 1000000000000)
      | 5 => orderedInterval (-14864742088 / 1000000000000) (-14864741823 / 1000000000000)
      | 6 => orderedInterval (-2774809590 / 1000000000000) (-2774809553 / 1000000000000)
      | 7 => orderedInterval (-648149738 / 1000000000000) (-648149454 / 1000000000000)
      | _ => orderedInterval (18429046262 / 1000000000000) (18429047379 / 1000000000000)
    | _ =>
      match b.val with
      | 0 => orderedInterval (-17249412925 / 1000000000000) (-17249385393 / 1000000000000)
      | 1 => orderedInterval (-17888602981 / 1000000000000) (-17888588579 / 1000000000000)
      | 2 => orderedInterval (-27691724615 / 1000000000000) (-27691724383 / 1000000000000)
      | 3 => orderedInterval (99325229805 / 1000000000000) (99325230733 / 1000000000000)
      | 4 => orderedInterval (-31284458212 / 1000000000000) (-31284458104 / 1000000000000)
      | 5 => orderedInterval (12748345340 / 1000000000000) (12748345729 / 1000000000000)
      | 6 => orderedInterval (-10942328785 / 1000000000000) (-10942328748 / 1000000000000)
      | 7 => orderedInterval (-8307984514 / 1000000000000) (-8307984282 / 1000000000000)
      | _ => orderedInterval (-42028972930 / 1000000000000) (-42028971358 / 1000000000000)
  coefficientTarget := fun i =>
    match i.val with
    | 0 => orderedInterval (-43307340980 / 1000000000000) (-43307310316 / 1000000000000)
    | 1 => orderedInterval (24035222954 / 1000000000000) (24035255067 / 1000000000000)
    | 2 => orderedInterval (53553526818 / 1000000000000) (53553561631 / 1000000000000)
    | 3 => orderedInterval (-24992709305 / 1000000000000) (-24992670587 / 1000000000000)
    | _ => orderedInterval (-43319909817 / 1000000000000) (-43319864385 / 1000000000000)

theorem compactCertificate227_stateChecks0 :
    compactCertificate227.stateChecks 0 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 34 12 (421 / 4)) (orderedInterval (-54692556856 / 1000000000000) (-54692488708 / 1000000000000), orderedInterval (55553291693 / 1000000000000) (55553359841 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 25 12 (620213389066321 / 8000000000000)) (orderedInterval (20601894409 / 1000000000000) (20601894636 / 1000000000000), orderedInterval (-88378756332 / 1000000000000) (-88378756105 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 40 12 (200564266935793 / 1600000000000)) (orderedInterval (32487997928 / 1000000000000) (32487997929 / 1000000000000), orderedInterval (63298983855 / 1000000000000) (63298983856 / 1000000000000))) = true
  norm_num [besselStateAtRationalPoint, besselIntervalStepZero,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, besselZeroTransition,
    besselInitial, besselGridStateAt, besselGridStateBlock00, besselGridStateBlock01,
    besselGridStateBlock02, besselGridStateBlock03, besselGridStateBlock04,
    besselGridStateBlock05, besselGridStateBlock06, besselGridStateBlock07,
    besselGridStateBlock08, besselGridStateBlock09, besselGridStateBlock10,
    besselGridStateBlock11, besselGridStateBlock12, besselGridStateBlock13,
    besselGridStateBlock14, besselGridState007, besselGridState010, besselGridState015, besselGridState018, besselGridState019, besselGridState025, besselGridState027, besselGridState029, besselGridState034, besselGridState036, besselGridState039, besselGridState040, besselGridState042, besselGridState043, besselGridState048, besselGridState049, besselGridState051, besselGridState053, besselGridState058, besselGridState062, besselGridState066, besselGridState072, besselGridState075, besselGridState077, besselStateSubset, linearInterval, widenInterval,
    rationalErrorInterval, rationalIntervalSubset, orderedInterval, Finset.sum_range_succ,
    IntervalRat.add, IntervalRat.mul, IntervalRat.scale, IntervalRat.singleton]

theorem compactCertificate227_stateChecks1 :
    compactCertificate227.stateChecks 3 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 7 12 (180976720095347 / 8000000000000)) (orderedInterval (-165592097429 / 1000000000000) (-165592097427 / 1000000000000), orderedInterval (-23067525142 / 1000000000000) (-23067525140 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 19 12 (486128926657559 / 8000000000000)) (orderedInterval (-98126141562 / 1000000000000) (-98126140369 / 1000000000000), orderedInterval (29919582428 / 1000000000000) (29919583620 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 53 12 (1319934601419003 / 8000000000000)) (orderedInterval (41328460328 / 1000000000000) (41328493359 / 1000000000000), orderedInterval (-46498222697 / 1000000000000) (-46498189666 / 1000000000000))) = true
  norm_num [besselStateAtRationalPoint, besselIntervalStepZero,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, besselZeroTransition,
    besselInitial, besselGridStateAt, besselGridStateBlock00, besselGridStateBlock01,
    besselGridStateBlock02, besselGridStateBlock03, besselGridStateBlock04,
    besselGridStateBlock05, besselGridStateBlock06, besselGridStateBlock07,
    besselGridStateBlock08, besselGridStateBlock09, besselGridStateBlock10,
    besselGridStateBlock11, besselGridStateBlock12, besselGridStateBlock13,
    besselGridStateBlock14, besselGridState007, besselGridState010, besselGridState015, besselGridState018, besselGridState019, besselGridState025, besselGridState027, besselGridState029, besselGridState034, besselGridState036, besselGridState039, besselGridState040, besselGridState042, besselGridState043, besselGridState048, besselGridState049, besselGridState051, besselGridState053, besselGridState058, besselGridState062, besselGridState066, besselGridState072, besselGridState075, besselGridState077, besselStateSubset, linearInterval, widenInterval,
    rationalErrorInterval, rationalIntervalSubset, orderedInterval, Finset.sum_range_succ,
    IntervalRat.add, IntervalRat.mul, IntervalRat.scale, IntervalRat.singleton]

theorem compactCertificate227_stateChecks2 :
    compactCertificate227.stateChecks 6 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 39 12 (972257853315539 / 8000000000000)) (orderedInterval (14769595595 / 1000000000000) (14769595717 / 1000000000000), orderedInterval (-70913984455 / 1000000000000) (-70913984332 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 66 12 (1665980403260447 / 8000000000000)) (orderedInterval (54915990818 / 1000000000000) (54915991174 / 1000000000000), orderedInterval (-6555170880 / 1000000000000) (-6555170525 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 49 12 (1227153624730973 / 8000000000000)) (orderedInterval (-15359985930 / 1000000000000) (-15359985929 / 1000000000000), orderedInterval (-62514387557 / 1000000000000) (-62514387556 / 1000000000000))) = true
  norm_num [besselStateAtRationalPoint, besselIntervalStepZero,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, besselZeroTransition,
    besselInitial, besselGridStateAt, besselGridStateBlock00, besselGridStateBlock01,
    besselGridStateBlock02, besselGridStateBlock03, besselGridStateBlock04,
    besselGridStateBlock05, besselGridStateBlock06, besselGridStateBlock07,
    besselGridStateBlock08, besselGridStateBlock09, besselGridStateBlock10,
    besselGridStateBlock11, besselGridStateBlock12, besselGridStateBlock13,
    besselGridStateBlock14, besselGridState007, besselGridState010, besselGridState015, besselGridState018, besselGridState019, besselGridState025, besselGridState027, besselGridState029, besselGridState034, besselGridState036, besselGridState039, besselGridState040, besselGridState042, besselGridState043, besselGridState048, besselGridState049, besselGridState051, besselGridState053, besselGridState058, besselGridState062, besselGridState066, besselGridState072, besselGridState075, besselGridState077, besselStateSubset, linearInterval, widenInterval,
    rationalErrorInterval, rationalIntervalSubset, orderedInterval, Finset.sum_range_succ,
    IntervalRat.add, IntervalRat.mul, IntervalRat.scale, IntervalRat.singleton]

theorem compactCertificate227_stateChecks3 :
    compactCertificate227.stateChecks 9 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 75 12 (1882769237054579 / 8000000000000)) (orderedInterval (-25461402971 / 1000000000000) (-25461402970 / 1000000000000), orderedInterval (-45297377836 / 1000000000000) (-45297377835 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 43 12 (1087017325835291 / 8000000000000)) (orderedInterval (-68448532078 / 1000000000000) (-68448532034 / 1000000000000), orderedInterval (413655251 / 1000000000000) (413655295 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 77 12 (1928931320026519 / 8000000000000)) (orderedInterval (68832524 / 1000000000000) (68832527 / 1000000000000), orderedInterval (-51384005585 / 1000000000000) (-51384005583 / 1000000000000))) = true
  norm_num [besselStateAtRationalPoint, besselIntervalStepZero,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, besselZeroTransition,
    besselInitial, besselGridStateAt, besselGridStateBlock00, besselGridStateBlock01,
    besselGridStateBlock02, besselGridStateBlock03, besselGridStateBlock04,
    besselGridStateBlock05, besselGridStateBlock06, besselGridStateBlock07,
    besselGridStateBlock08, besselGridStateBlock09, besselGridStateBlock10,
    besselGridStateBlock11, besselGridStateBlock12, besselGridStateBlock13,
    besselGridStateBlock14, besselGridState007, besselGridState010, besselGridState015, besselGridState018, besselGridState019, besselGridState025, besselGridState027, besselGridState029, besselGridState034, besselGridState036, besselGridState039, besselGridState040, besselGridState042, besselGridState043, besselGridState048, besselGridState049, besselGridState051, besselGridState053, besselGridState058, besselGridState062, besselGridState066, besselGridState072, besselGridState075, besselGridState077, besselStateSubset, linearInterval, widenInterval,
    rationalErrorInterval, rationalIntervalSubset, orderedInterval, Finset.sum_range_succ,
    IntervalRat.add, IntervalRat.mul, IntervalRat.scale, IntervalRat.singleton]

theorem compactCertificate227_stateChecks4 :
    compactCertificate227.stateChecks 12 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 72 12 (1802257853558611 / 8000000000000)) (orderedInterval (-6764476947 / 1000000000000) (-6764476929 / 1000000000000), orderedInterval (52741905080 / 1000000000000) (52741905098 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 51 12 (1286176245050563 / 8000000000000)) (orderedInterval (-61191519387 / 1000000000000) (-61191519385 / 1000000000000), orderedInterval (-14484431128 / 1000000000000) (-14484431126 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 58 12 (1458386779972677 / 8000000000000)) (orderedInterval (45193854000 / 1000000000000) (45193854001 / 1000000000000), orderedInterval (37950965088 / 1000000000000) (37950965089 / 1000000000000))) = true
  norm_num [besselStateAtRationalPoint, besselIntervalStepZero,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, besselZeroTransition,
    besselInitial, besselGridStateAt, besselGridStateBlock00, besselGridStateBlock01,
    besselGridStateBlock02, besselGridStateBlock03, besselGridStateBlock04,
    besselGridStateBlock05, besselGridStateBlock06, besselGridStateBlock07,
    besselGridStateBlock08, besselGridStateBlock09, besselGridStateBlock10,
    besselGridStateBlock11, besselGridStateBlock12, besselGridStateBlock13,
    besselGridStateBlock14, besselGridState007, besselGridState010, besselGridState015, besselGridState018, besselGridState019, besselGridState025, besselGridState027, besselGridState029, besselGridState034, besselGridState036, besselGridState039, besselGridState040, besselGridState042, besselGridState043, besselGridState048, besselGridState049, besselGridState051, besselGridState053, besselGridState058, besselGridState062, besselGridState066, besselGridState072, besselGridState075, besselGridState077, besselStateSubset, linearInterval, widenInterval,
    rationalErrorInterval, rationalIntervalSubset, orderedInterval, Finset.sum_range_succ,
    IntervalRat.add, IntervalRat.mul, IntervalRat.scale, IntervalRat.singleton]

theorem compactCertificate227_stateChecks5 :
    compactCertificate227.stateChecks 15 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 48 12 (1215850852676213 / 8000000000000)) (orderedInterval (59644781128 / 1000000000000) (59644787700 / 1000000000000), orderedInterval (-25321622337 / 1000000000000) (-25321615765 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 43 12 (1074241101396473 / 8000000000000)) (orderedInterval (1644030530 / 1000000000000) (1644030538 / 1000000000000), orderedInterval (-68841522427 / 1000000000000) (-68841522420 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 62 12 (311356941742827 / 1600000000000)) (orderedInterval (32488887206 / 1000000000000) (32488887207 / 1000000000000), orderedInterval (46990248528 / 1000000000000) (46990248529 / 1000000000000))) = true
  norm_num [besselStateAtRationalPoint, besselIntervalStepZero,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, besselZeroTransition,
    besselInitial, besselGridStateAt, besselGridStateBlock00, besselGridStateBlock01,
    besselGridStateBlock02, besselGridStateBlock03, besselGridStateBlock04,
    besselGridStateBlock05, besselGridStateBlock06, besselGridStateBlock07,
    besselGridStateBlock08, besselGridStateBlock09, besselGridStateBlock10,
    besselGridStateBlock11, besselGridStateBlock12, besselGridStateBlock13,
    besselGridStateBlock14, besselGridState007, besselGridState010, besselGridState015, besselGridState018, besselGridState019, besselGridState025, besselGridState027, besselGridState029, besselGridState034, besselGridState036, besselGridState039, besselGridState040, besselGridState042, besselGridState043, besselGridState048, besselGridState049, besselGridState051, besselGridState053, besselGridState058, besselGridState062, besselGridState066, besselGridState072, besselGridState075, besselGridState077, besselStateSubset, linearInterval, widenInterval,
    rationalErrorInterval, rationalIntervalSubset, orderedInterval, Finset.sum_range_succ,
    IntervalRat.add, IntervalRat.mul, IntervalRat.scale, IntervalRat.singleton]

theorem compactCertificate227_stateChecks6 :
    compactCertificate227.stateChecks 18 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 34 12 (861229686678769 / 8000000000000)) (orderedInterval (76791461505 / 1000000000000) (76791461581 / 1000000000000), orderedInterval (-4430564054 / 1000000000000) (-4430563978 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 29 12 (730073943255209 / 8000000000000)) (orderedInterval (-67304572287 / 1000000000000) (-67304572286 / 1000000000000), orderedInterval (-49088426683 / 1000000000000) (-49088426682 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 18 12 (456846375269027 / 8000000000000)) (orderedInterval (102791036670 / 1000000000000) (102791036671 / 1000000000000), orderedInterval (23218446716 / 1000000000000) (23218446717 / 1000000000000))) = true
  norm_num [besselStateAtRationalPoint, besselIntervalStepZero,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, besselZeroTransition,
    besselInitial, besselGridStateAt, besselGridStateBlock00, besselGridStateBlock01,
    besselGridStateBlock02, besselGridStateBlock03, besselGridStateBlock04,
    besselGridStateBlock05, besselGridStateBlock06, besselGridStateBlock07,
    besselGridStateBlock08, besselGridStateBlock09, besselGridStateBlock10,
    besselGridStateBlock11, besselGridStateBlock12, besselGridStateBlock13,
    besselGridStateBlock14, besselGridState007, besselGridState010, besselGridState015, besselGridState018, besselGridState019, besselGridState025, besselGridState027, besselGridState029, besselGridState034, besselGridState036, besselGridState039, besselGridState040, besselGridState042, besselGridState043, besselGridState048, besselGridState049, besselGridState051, besselGridState053, besselGridState058, besselGridState062, besselGridState066, besselGridState072, besselGridState075, besselGridState077, besselStateSubset, linearInterval, widenInterval,
    rationalErrorInterval, rationalIntervalSubset, orderedInterval, Finset.sum_range_succ,
    IntervalRat.add, IntervalRat.mul, IntervalRat.scale, IntervalRat.singleton]

theorem compactCertificate227_stateChecks7 :
    compactCertificate227.stateChecks 21 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 10 12 (245693500022109 / 8000000000000)) (orderedInterval (11087518805 / 1000000000000) (11087518809 / 1000000000000), orderedInterval (143376794429 / 1000000000000) (143376794432 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 27 12 (667105646753327 / 8000000000000)) (orderedInterval (52940082019 / 1000000000000) (52940105637 / 1000000000000), orderedInterval (-69828531749 / 1000000000000) (-69828508131 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 36 12 (910875728025679 / 8000000000000)) (orderedInterval (74752284300 / 1000000000000) (74752284325 / 1000000000000), orderedInterval (1493494866 / 1000000000000) (1493494891 / 1000000000000))) = true
  norm_num [besselStateAtRationalPoint, besselIntervalStepZero,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, besselZeroTransition,
    besselInitial, besselGridStateAt, besselGridStateBlock00, besselGridStateBlock01,
    besselGridStateBlock02, besselGridStateBlock03, besselGridStateBlock04,
    besselGridStateBlock05, besselGridStateBlock06, besselGridStateBlock07,
    besselGridStateBlock08, besselGridStateBlock09, besselGridStateBlock10,
    besselGridStateBlock11, besselGridStateBlock12, besselGridStateBlock13,
    besselGridStateBlock14, besselGridState007, besselGridState010, besselGridState015, besselGridState018, besselGridState019, besselGridState025, besselGridState027, besselGridState029, besselGridState034, besselGridState036, besselGridState039, besselGridState040, besselGridState042, besselGridState043, besselGridState048, besselGridState049, besselGridState051, besselGridState053, besselGridState058, besselGridState062, besselGridState066, besselGridState072, besselGridState075, besselGridState077, besselStateSubset, linearInterval, widenInterval,
    rationalErrorInterval, rationalIntervalSubset, orderedInterval, Finset.sum_range_succ,
    IntervalRat.add, IntervalRat.mul, IntervalRat.scale, IntervalRat.singleton]

theorem compactCertificate227_stateChecks8 :
    compactCertificate227.stateChecks 24 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 15 12 (385153624730973 / 8000000000000)) (orderedInterval (-111899838650 / 1000000000000) (-111899838086 / 1000000000000), orderedInterval (27637949193 / 1000000000000) (27637949758 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 62 12 (1565628101441533 / 8000000000000)) (orderedInterval (56486838640 / 1000000000000) (56486839076 / 1000000000000), orderedInterval (-8031498693 / 1000000000000) (-8031498258 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 42 12 (1045767014194547 / 8000000000000)) (orderedInterval (-29823717140 / 1000000000000) (-29823714949 / 1000000000000), orderedInterval (63206370285 / 1000000000000) (63206372476 / 1000000000000))) = true
  norm_num [besselStateAtRationalPoint, besselIntervalStepZero,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, besselZeroTransition,
    besselInitial, besselGridStateAt, besselGridStateBlock00, besselGridStateBlock01,
    besselGridStateBlock02, besselGridStateBlock03, besselGridStateBlock04,
    besselGridStateBlock05, besselGridStateBlock06, besselGridStateBlock07,
    besselGridStateBlock08, besselGridStateBlock09, besselGridStateBlock10,
    besselGridStateBlock11, besselGridStateBlock12, besselGridStateBlock13,
    besselGridStateBlock14, besselGridState007, besselGridState010, besselGridState015, besselGridState018, besselGridState019, besselGridState025, besselGridState027, besselGridState029, besselGridState034, besselGridState036, besselGridState039, besselGridState040, besselGridState042, besselGridState043, besselGridState048, besselGridState049, besselGridState051, besselGridState053, besselGridState058, besselGridState062, besselGridState066, besselGridState072, besselGridState075, besselGridState077, besselStateSubset, linearInterval, widenInterval,
    rationalErrorInterval, rationalIntervalSubset, orderedInterval, Finset.sum_range_succ,
    IntervalRat.add, IntervalRat.mul, IntervalRat.scale, IntervalRat.singleton]

theorem compactCertificate227_states : ∀ j,
    BesselStateValid (compactCertificate227.point j) (compactCertificate227.state j) :=
  compactCertificate227.statesValid_of_checks3 compactCertificate227_stateChecks0
    compactCertificate227_stateChecks1 compactCertificate227_stateChecks2
    compactCertificate227_stateChecks3 compactCertificate227_stateChecks4
    compactCertificate227_stateChecks5 compactCertificate227_stateChecks6
    compactCertificate227_stateChecks7 compactCertificate227_stateChecks8

theorem compactCertificate227_chunkChecks0_0 :
    compactCertificate227.chunkChecks (0 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 0) <| besselDerivativeNearFromState (421 / 4) 0 (IntervalRat.scale (421 / 4) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-54692556856 / 1000000000000) (-54692488708 / 1000000000000), orderedInterval (55553291693 / 1000000000000) (55553359841 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 0) <| besselDerivativeNearFromState (620213389066321 / 8000000000000) 0 (IntervalRat.scale (421 / 4) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (20601894409 / 1000000000000) (20601894636 / 1000000000000), orderedInterval (-88378756332 / 1000000000000) (-88378756105 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 0) <| besselDerivativeNearFromState (200564266935793 / 1600000000000) 0 (IntervalRat.scale (421 / 4) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (32487997928 / 1000000000000) (32487997929 / 1000000000000), orderedInterval (63298983855 / 1000000000000) (63298983856 / 1000000000000)))) (orderedInterval (-19579812477 / 1000000000000) (-19579785455 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 0) <| besselDerivativeNearFromState (180976720095347 / 8000000000000) 0 (IntervalRat.scale (421 / 4) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-165592097429 / 1000000000000) (-165592097427 / 1000000000000), orderedInterval (-23067525142 / 1000000000000) (-23067525140 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 0) <| besselDerivativeNearFromState (486128926657559 / 8000000000000) 0 (IntervalRat.scale (421 / 4) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-98126141562 / 1000000000000) (-98126140369 / 1000000000000), orderedInterval (29919582428 / 1000000000000) (29919583620 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 0) <| besselDerivativeNearFromState (1319934601419003 / 8000000000000) 0 (IntervalRat.scale (421 / 4) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (41328460328 / 1000000000000) (41328493359 / 1000000000000), orderedInterval (-46498222697 / 1000000000000) (-46498189666 / 1000000000000)))) (orderedInterval (-4724227667 / 1000000000000) (-4724225262 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 0) <| besselDerivativeNearFromState (972257853315539 / 8000000000000) 0 (IntervalRat.scale (421 / 4) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (14769595595 / 1000000000000) (14769595717 / 1000000000000), orderedInterval (-70913984455 / 1000000000000) (-70913984332 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 0) <| besselDerivativeNearFromState (1665980403260447 / 8000000000000) 0 (IntervalRat.scale (421 / 4) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (54915990818 / 1000000000000) (54915991174 / 1000000000000), orderedInterval (-6555170880 / 1000000000000) (-6555170525 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 0) <| besselDerivativeNearFromState (1227153624730973 / 8000000000000) 0 (IntervalRat.scale (421 / 4) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-15359985930 / 1000000000000) (-15359985929 / 1000000000000), orderedInterval (-62514387557 / 1000000000000) (-62514387556 / 1000000000000)))) (orderedInterval (-2065049445 / 1000000000000) (-2065049427 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate227_chunkChecks0_1 :
    compactCertificate227.chunkChecks (0 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 0) <| besselDerivativeNearFromState (1882769237054579 / 8000000000000) 0 (IntervalRat.scale (421 / 4) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-25461402971 / 1000000000000) (-25461402970 / 1000000000000), orderedInterval (-45297377836 / 1000000000000) (-45297377835 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 0) <| besselDerivativeNearFromState (1087017325835291 / 8000000000000) 0 (IntervalRat.scale (421 / 4) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-68448532078 / 1000000000000) (-68448532034 / 1000000000000), orderedInterval (413655251 / 1000000000000) (413655295 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 0) <| besselDerivativeNearFromState (1928931320026519 / 8000000000000) 0 (IntervalRat.scale (421 / 4) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (68832524 / 1000000000000) (68832527 / 1000000000000), orderedInterval (-51384005585 / 1000000000000) (-51384005583 / 1000000000000)))) (orderedInterval (-537504150 / 1000000000000) (-537504103 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 0) <| besselDerivativeNearFromState (1802257853558611 / 8000000000000) 0 (IntervalRat.scale (421 / 4) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-6764476947 / 1000000000000) (-6764476929 / 1000000000000), orderedInterval (52741905080 / 1000000000000) (52741905098 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 0) <| besselDerivativeNearFromState (1286176245050563 / 8000000000000) 0 (IntervalRat.scale (421 / 4) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-61191519387 / 1000000000000) (-61191519385 / 1000000000000), orderedInterval (-14484431128 / 1000000000000) (-14484431126 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 0) <| besselDerivativeNearFromState (1458386779972677 / 8000000000000) 0 (IntervalRat.scale (421 / 4) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (45193854000 / 1000000000000) (45193854001 / 1000000000000), orderedInterval (37950965088 / 1000000000000) (37950965089 / 1000000000000)))) (orderedInterval (-5893032704 / 1000000000000) (-5893032690 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 0) <| besselDerivativeNearFromState (1215850852676213 / 8000000000000) 0 (IntervalRat.scale (421 / 4) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (59644781128 / 1000000000000) (59644787700 / 1000000000000), orderedInterval (-25321622337 / 1000000000000) (-25321615765 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 0) <| besselDerivativeNearFromState (1074241101396473 / 8000000000000) 0 (IntervalRat.scale (421 / 4) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (1644030530 / 1000000000000) (1644030538 / 1000000000000), orderedInterval (-68841522427 / 1000000000000) (-68841522420 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 0) <| besselDerivativeNearFromState (311356941742827 / 1600000000000) 0 (IntervalRat.scale (421 / 4) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (32488887206 / 1000000000000) (32488887207 / 1000000000000), orderedInterval (46990248528 / 1000000000000) (46990248529 / 1000000000000)))) (orderedInterval (1426519683 / 1000000000000) (1426519771 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate227_chunkChecks0_2 :
    compactCertificate227.chunkChecks (0 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 0) <| besselDerivativeNearFromState (861229686678769 / 8000000000000) 0 (IntervalRat.scale (421 / 4) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (76791461505 / 1000000000000) (76791461581 / 1000000000000), orderedInterval (-4430564054 / 1000000000000) (-4430563978 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 0) <| besselDerivativeNearFromState (730073943255209 / 8000000000000) 0 (IntervalRat.scale (421 / 4) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-67304572287 / 1000000000000) (-67304572286 / 1000000000000), orderedInterval (-49088426683 / 1000000000000) (-49088426682 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 0) <| besselDerivativeNearFromState (456846375269027 / 8000000000000) 0 (IntervalRat.scale (421 / 4) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (102791036670 / 1000000000000) (102791036671 / 1000000000000), orderedInterval (23218446716 / 1000000000000) (23218446717 / 1000000000000)))) (orderedInterval (-5122548445 / 1000000000000) (-5122548406 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 0) <| besselDerivativeNearFromState (245693500022109 / 8000000000000) 0 (IntervalRat.scale (421 / 4) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (11087518805 / 1000000000000) (11087518809 / 1000000000000), orderedInterval (143376794429 / 1000000000000) (143376794432 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 0) <| besselDerivativeNearFromState (667105646753327 / 8000000000000) 0 (IntervalRat.scale (421 / 4) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (52940082019 / 1000000000000) (52940105637 / 1000000000000), orderedInterval (-69828531749 / 1000000000000) (-69828508131 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 0) <| besselDerivativeNearFromState (910875728025679 / 8000000000000) 0 (IntervalRat.scale (421 / 4) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (74752284300 / 1000000000000) (74752284325 / 1000000000000), orderedInterval (1493494866 / 1000000000000) (1493494891 / 1000000000000)))) (orderedInterval (-7134707810 / 1000000000000) (-7134707259 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 0) <| besselDerivativeNearFromState (385153624730973 / 8000000000000) 0 (IntervalRat.scale (421 / 4) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-111899838650 / 1000000000000) (-111899838086 / 1000000000000), orderedInterval (27637949193 / 1000000000000) (27637949758 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 0) <| besselDerivativeNearFromState (1565628101441533 / 8000000000000) 0 (IntervalRat.scale (421 / 4) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (56486838640 / 1000000000000) (56486839076 / 1000000000000), orderedInterval (-8031498693 / 1000000000000) (-8031498258 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 0) <| besselDerivativeNearFromState (1045767014194547 / 8000000000000) 0 (IntervalRat.scale (421 / 4) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-29823717140 / 1000000000000) (-29823714949 / 1000000000000), orderedInterval (63206370285 / 1000000000000) (63206372476 / 1000000000000)))) (orderedInterval (323022035 / 1000000000000) (323022515 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate227_chunkChecks0 :
    compactCertificate227.chunkChecks (0 : Fin 5) 0 9 = true :=
  compactCertificate227.chunkChecks_nine_of_three (0 : Fin 5) compactCertificate227_chunkChecks0_0
    compactCertificate227_chunkChecks0_1 compactCertificate227_chunkChecks0_2

theorem compactCertificate227_chunkChecks1_0 :
    compactCertificate227.chunkChecks (1 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 1) <| besselDerivativeNearFromState (421 / 4) 1 (IntervalRat.scale (421 / 4) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-54692556856 / 1000000000000) (-54692488708 / 1000000000000), orderedInterval (55553291693 / 1000000000000) (55553359841 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 1) <| besselDerivativeNearFromState (620213389066321 / 8000000000000) 1 (IntervalRat.scale (421 / 4) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (20601894409 / 1000000000000) (20601894636 / 1000000000000), orderedInterval (-88378756332 / 1000000000000) (-88378756105 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 1) <| besselDerivativeNearFromState (200564266935793 / 1600000000000) 1 (IntervalRat.scale (421 / 4) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (32487997928 / 1000000000000) (32487997929 / 1000000000000), orderedInterval (63298983855 / 1000000000000) (63298983856 / 1000000000000)))) (orderedInterval (25836694825 / 1000000000000) (25836721847 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 1) <| besselDerivativeNearFromState (180976720095347 / 8000000000000) 1 (IntervalRat.scale (421 / 4) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-165592097429 / 1000000000000) (-165592097427 / 1000000000000), orderedInterval (-23067525142 / 1000000000000) (-23067525140 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 1) <| besselDerivativeNearFromState (486128926657559 / 8000000000000) 1 (IntervalRat.scale (421 / 4) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-98126141562 / 1000000000000) (-98126140369 / 1000000000000), orderedInterval (29919582428 / 1000000000000) (29919583620 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 1) <| besselDerivativeNearFromState (1319934601419003 / 8000000000000) 1 (IntervalRat.scale (421 / 4) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (41328460328 / 1000000000000) (41328493359 / 1000000000000), orderedInterval (-46498222697 / 1000000000000) (-46498189666 / 1000000000000)))) (orderedInterval (5866322549 / 1000000000000) (5866326271 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 1) <| besselDerivativeNearFromState (972257853315539 / 8000000000000) 1 (IntervalRat.scale (421 / 4) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (14769595595 / 1000000000000) (14769595717 / 1000000000000), orderedInterval (-70913984455 / 1000000000000) (-70913984332 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 1) <| besselDerivativeNearFromState (1665980403260447 / 8000000000000) 1 (IntervalRat.scale (421 / 4) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (54915990818 / 1000000000000) (54915991174 / 1000000000000), orderedInterval (-6555170880 / 1000000000000) (-6555170525 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 1) <| besselDerivativeNearFromState (1227153624730973 / 8000000000000) 1 (IntervalRat.scale (421 / 4) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-15359985930 / 1000000000000) (-15359985929 / 1000000000000), orderedInterval (-62514387557 / 1000000000000) (-62514387556 / 1000000000000)))) (orderedInterval (-1801904521 / 1000000000000) (-1801904489 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate227_chunkChecks1_1 :
    compactCertificate227.chunkChecks (1 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 1) <| besselDerivativeNearFromState (1882769237054579 / 8000000000000) 1 (IntervalRat.scale (421 / 4) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-25461402971 / 1000000000000) (-25461402970 / 1000000000000), orderedInterval (-45297377836 / 1000000000000) (-45297377835 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 1) <| besselDerivativeNearFromState (1087017325835291 / 8000000000000) 1 (IntervalRat.scale (421 / 4) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-68448532078 / 1000000000000) (-68448532034 / 1000000000000), orderedInterval (413655251 / 1000000000000) (413655295 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 1) <| besselDerivativeNearFromState (1928931320026519 / 8000000000000) 1 (IntervalRat.scale (421 / 4) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (68832524 / 1000000000000) (68832527 / 1000000000000), orderedInterval (-51384005585 / 1000000000000) (-51384005583 / 1000000000000)))) (orderedInterval (1303311914 / 1000000000000) (1303312007 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 1) <| besselDerivativeNearFromState (1802257853558611 / 8000000000000) 1 (IntervalRat.scale (421 / 4) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-6764476947 / 1000000000000) (-6764476929 / 1000000000000), orderedInterval (52741905080 / 1000000000000) (52741905098 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 1) <| besselDerivativeNearFromState (1286176245050563 / 8000000000000) 1 (IntervalRat.scale (421 / 4) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-61191519387 / 1000000000000) (-61191519385 / 1000000000000), orderedInterval (-14484431128 / 1000000000000) (-14484431126 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 1) <| besselDerivativeNearFromState (1458386779972677 / 8000000000000) 1 (IntervalRat.scale (421 / 4) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (45193854000 / 1000000000000) (45193854001 / 1000000000000), orderedInterval (37950965088 / 1000000000000) (37950965089 / 1000000000000)))) (orderedInterval (-4462919011 / 1000000000000) (-4462918989 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 1) <| besselDerivativeNearFromState (1215850852676213 / 8000000000000) 1 (IntervalRat.scale (421 / 4) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (59644781128 / 1000000000000) (59644787700 / 1000000000000), orderedInterval (-25321622337 / 1000000000000) (-25321615765 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 1) <| besselDerivativeNearFromState (1074241101396473 / 8000000000000) 1 (IntervalRat.scale (421 / 4) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (1644030530 / 1000000000000) (1644030538 / 1000000000000), orderedInterval (-68841522427 / 1000000000000) (-68841522420 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 1) <| besselDerivativeNearFromState (311356941742827 / 1600000000000) 1 (IntervalRat.scale (421 / 4) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (32488887206 / 1000000000000) (32488887207 / 1000000000000), orderedInterval (46990248528 / 1000000000000) (46990248529 / 1000000000000)))) (orderedInterval (6828446097 / 1000000000000) (6828446222 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate227_chunkChecks1_2 :
    compactCertificate227.chunkChecks (1 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 1) <| besselDerivativeNearFromState (861229686678769 / 8000000000000) 1 (IntervalRat.scale (421 / 4) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (76791461505 / 1000000000000) (76791461581 / 1000000000000), orderedInterval (-4430564054 / 1000000000000) (-4430563978 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 1) <| besselDerivativeNearFromState (730073943255209 / 8000000000000) 1 (IntervalRat.scale (421 / 4) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-67304572287 / 1000000000000) (-67304572286 / 1000000000000), orderedInterval (-49088426683 / 1000000000000) (-49088426682 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 1) <| besselDerivativeNearFromState (456846375269027 / 8000000000000) 1 (IntervalRat.scale (421 / 4) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (102791036670 / 1000000000000) (102791036671 / 1000000000000), orderedInterval (23218446716 / 1000000000000) (23218446717 / 1000000000000)))) (orderedInterval (3543787058 / 1000000000000) (3543787096 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 1) <| besselDerivativeNearFromState (245693500022109 / 8000000000000) 1 (IntervalRat.scale (421 / 4) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (11087518805 / 1000000000000) (11087518809 / 1000000000000), orderedInterval (143376794429 / 1000000000000) (143376794432 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 1) <| besselDerivativeNearFromState (667105646753327 / 8000000000000) 1 (IntervalRat.scale (421 / 4) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (52940082019 / 1000000000000) (52940105637 / 1000000000000), orderedInterval (-69828531749 / 1000000000000) (-69828508131 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 1) <| besselDerivativeNearFromState (910875728025679 / 8000000000000) 1 (IntervalRat.scale (421 / 4) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (74752284300 / 1000000000000) (74752284325 / 1000000000000), orderedInterval (1493494866 / 1000000000000) (1493494891 / 1000000000000)))) (orderedInterval (358785386 / 1000000000000) (358785825 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 1) <| besselDerivativeNearFromState (385153624730973 / 8000000000000) 1 (IntervalRat.scale (421 / 4) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-111899838650 / 1000000000000) (-111899838086 / 1000000000000), orderedInterval (27637949193 / 1000000000000) (27637949758 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 1) <| besselDerivativeNearFromState (1565628101441533 / 8000000000000) 1 (IntervalRat.scale (421 / 4) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (56486838640 / 1000000000000) (56486839076 / 1000000000000), orderedInterval (-8031498693 / 1000000000000) (-8031498258 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 1) <| besselDerivativeNearFromState (1045767014194547 / 8000000000000) 1 (IntervalRat.scale (421 / 4) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-29823717140 / 1000000000000) (-29823714949 / 1000000000000), orderedInterval (63206370285 / 1000000000000) (63206372476 / 1000000000000)))) (orderedInterval (-13437301343 / 1000000000000) (-13437300723 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate227_chunkChecks1 :
    compactCertificate227.chunkChecks (1 : Fin 5) 0 9 = true :=
  compactCertificate227.chunkChecks_nine_of_three (1 : Fin 5) compactCertificate227_chunkChecks1_0
    compactCertificate227_chunkChecks1_1 compactCertificate227_chunkChecks1_2

theorem compactCertificate227_chunkChecks2_0 :
    compactCertificate227.chunkChecks (2 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 2) <| besselDerivativeNearFromState (421 / 4) 2 (IntervalRat.scale (421 / 4) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-54692556856 / 1000000000000) (-54692488708 / 1000000000000), orderedInterval (55553291693 / 1000000000000) (55553359841 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 2) <| besselDerivativeNearFromState (620213389066321 / 8000000000000) 2 (IntervalRat.scale (421 / 4) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (20601894409 / 1000000000000) (20601894636 / 1000000000000), orderedInterval (-88378756332 / 1000000000000) (-88378756105 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 2) <| besselDerivativeNearFromState (200564266935793 / 1600000000000) 2 (IntervalRat.scale (421 / 4) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (32487997928 / 1000000000000) (32487997929 / 1000000000000), orderedInterval (63298983855 / 1000000000000) (63298983856 / 1000000000000)))) (orderedInterval (18624315754 / 1000000000000) (18624343034 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 2) <| besselDerivativeNearFromState (180976720095347 / 8000000000000) 2 (IntervalRat.scale (421 / 4) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-165592097429 / 1000000000000) (-165592097427 / 1000000000000), orderedInterval (-23067525142 / 1000000000000) (-23067525140 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 2) <| besselDerivativeNearFromState (486128926657559 / 8000000000000) 2 (IntervalRat.scale (421 / 4) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-98126141562 / 1000000000000) (-98126140369 / 1000000000000), orderedInterval (29919582428 / 1000000000000) (29919583620 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 2) <| besselDerivativeNearFromState (1319934601419003 / 8000000000000) 2 (IntervalRat.scale (421 / 4) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (41328460328 / 1000000000000) (41328493359 / 1000000000000), orderedInterval (-46498222697 / 1000000000000) (-46498189666 / 1000000000000)))) (orderedInterval (8275501477 / 1000000000000) (8275507318 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 2) <| besselDerivativeNearFromState (972257853315539 / 8000000000000) 2 (IntervalRat.scale (421 / 4) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (14769595595 / 1000000000000) (14769595717 / 1000000000000), orderedInterval (-70913984455 / 1000000000000) (-70913984332 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 2) <| besselDerivativeNearFromState (1665980403260447 / 8000000000000) 2 (IntervalRat.scale (421 / 4) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (54915990818 / 1000000000000) (54915991174 / 1000000000000), orderedInterval (-6555170880 / 1000000000000) (-6555170525 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 2) <| besselDerivativeNearFromState (1227153624730973 / 8000000000000) 2 (IntervalRat.scale (421 / 4) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-15359985930 / 1000000000000) (-15359985929 / 1000000000000), orderedInterval (-62514387557 / 1000000000000) (-62514387556 / 1000000000000)))) (orderedInterval (7436720607 / 1000000000000) (7436720669 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate227_chunkChecks2_1 :
    compactCertificate227.chunkChecks (2 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 2) <| besselDerivativeNearFromState (1882769237054579 / 8000000000000) 2 (IntervalRat.scale (421 / 4) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-25461402971 / 1000000000000) (-25461402970 / 1000000000000), orderedInterval (-45297377836 / 1000000000000) (-45297377835 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 2) <| besselDerivativeNearFromState (1087017325835291 / 8000000000000) 2 (IntervalRat.scale (421 / 4) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-68448532078 / 1000000000000) (-68448532034 / 1000000000000), orderedInterval (413655251 / 1000000000000) (413655295 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 2) <| besselDerivativeNearFromState (1928931320026519 / 8000000000000) 2 (IntervalRat.scale (421 / 4) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (68832524 / 1000000000000) (68832527 / 1000000000000), orderedInterval (-51384005585 / 1000000000000) (-51384005583 / 1000000000000)))) (orderedInterval (-14232200854 / 1000000000000) (-14232200659 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 2) <| besselDerivativeNearFromState (1802257853558611 / 8000000000000) 2 (IntervalRat.scale (421 / 4) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-6764476947 / 1000000000000) (-6764476929 / 1000000000000), orderedInterval (52741905080 / 1000000000000) (52741905098 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 2) <| besselDerivativeNearFromState (1286176245050563 / 8000000000000) 2 (IntervalRat.scale (421 / 4) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-61191519387 / 1000000000000) (-61191519385 / 1000000000000), orderedInterval (-14484431128 / 1000000000000) (-14484431126 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 2) <| besselDerivativeNearFromState (1458386779972677 / 8000000000000) 2 (IntervalRat.scale (421 / 4) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (45193854000 / 1000000000000) (45193854001 / 1000000000000), orderedInterval (37950965088 / 1000000000000) (37950965089 / 1000000000000)))) (orderedInterval (13670735975 / 1000000000000) (13670736011 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 2) <| besselDerivativeNearFromState (1215850852676213 / 8000000000000) 2 (IntervalRat.scale (421 / 4) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (59644781128 / 1000000000000) (59644787700 / 1000000000000), orderedInterval (-25321622337 / 1000000000000) (-25321615765 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 2) <| besselDerivativeNearFromState (1074241101396473 / 8000000000000) 2 (IntervalRat.scale (421 / 4) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (1644030530 / 1000000000000) (1644030538 / 1000000000000), orderedInterval (-68841522427 / 1000000000000) (-68841522420 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 2) <| besselDerivativeNearFromState (311356941742827 / 1600000000000) 2 (IntervalRat.scale (421 / 4) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (32488887206 / 1000000000000) (32488887207 / 1000000000000), orderedInterval (46990248528 / 1000000000000) (46990248529 / 1000000000000)))) (orderedInterval (-4191541002 / 1000000000000) (-4191540819 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate227_chunkChecks2_2 :
    compactCertificate227.chunkChecks (2 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 2) <| besselDerivativeNearFromState (861229686678769 / 8000000000000) 2 (IntervalRat.scale (421 / 4) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (76791461505 / 1000000000000) (76791461581 / 1000000000000), orderedInterval (-4430564054 / 1000000000000) (-4430563978 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 2) <| besselDerivativeNearFromState (730073943255209 / 8000000000000) 2 (IntervalRat.scale (421 / 4) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-67304572287 / 1000000000000) (-67304572286 / 1000000000000), orderedInterval (-49088426683 / 1000000000000) (-49088426682 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 2) <| besselDerivativeNearFromState (456846375269027 / 8000000000000) 2 (IntervalRat.scale (421 / 4) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (102791036670 / 1000000000000) (102791036671 / 1000000000000), orderedInterval (23218446716 / 1000000000000) (23218446717 / 1000000000000)))) (orderedInterval (8962828446 / 1000000000000) (8962828483 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 2) <| besselDerivativeNearFromState (245693500022109 / 8000000000000) 2 (IntervalRat.scale (421 / 4) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (11087518805 / 1000000000000) (11087518809 / 1000000000000), orderedInterval (143376794429 / 1000000000000) (143376794432 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 2) <| besselDerivativeNearFromState (667105646753327 / 8000000000000) 2 (IntervalRat.scale (421 / 4) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (52940082019 / 1000000000000) (52940105637 / 1000000000000), orderedInterval (-69828531749 / 1000000000000) (-69828508131 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 2) <| besselDerivativeNearFromState (910875728025679 / 8000000000000) 2 (IntervalRat.scale (421 / 4) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (74752284300 / 1000000000000) (74752284325 / 1000000000000), orderedInterval (1493494866 / 1000000000000) (1493494891 / 1000000000000)))) (orderedInterval (7472460337 / 1000000000000) (7472460692 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 2) <| besselDerivativeNearFromState (385153624730973 / 8000000000000) 2 (IntervalRat.scale (421 / 4) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-111899838650 / 1000000000000) (-111899838086 / 1000000000000), orderedInterval (27637949193 / 1000000000000) (27637949758 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 2) <| besselDerivativeNearFromState (1565628101441533 / 8000000000000) 2 (IntervalRat.scale (421 / 4) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (56486838640 / 1000000000000) (56486839076 / 1000000000000), orderedInterval (-8031498693 / 1000000000000) (-8031498258 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 2) <| besselDerivativeNearFromState (1045767014194547 / 8000000000000) 2 (IntervalRat.scale (421 / 4) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-29823717140 / 1000000000000) (-29823714949 / 1000000000000), orderedInterval (63206370285 / 1000000000000) (63206372476 / 1000000000000)))) (orderedInterval (7534706078 / 1000000000000) (7534706902 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate227_chunkChecks2 :
    compactCertificate227.chunkChecks (2 : Fin 5) 0 9 = true :=
  compactCertificate227.chunkChecks_nine_of_three (2 : Fin 5) compactCertificate227_chunkChecks2_0
    compactCertificate227_chunkChecks2_1 compactCertificate227_chunkChecks2_2

theorem compactCertificate227_chunkChecks3_0 :
    compactCertificate227.chunkChecks (3 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 3) <| besselDerivativeNearFromState (421 / 4) 3 (IntervalRat.scale (421 / 4) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-54692556856 / 1000000000000) (-54692488708 / 1000000000000), orderedInterval (55553291693 / 1000000000000) (55553359841 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 3) <| besselDerivativeNearFromState (620213389066321 / 8000000000000) 3 (IntervalRat.scale (421 / 4) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (20601894409 / 1000000000000) (20601894636 / 1000000000000), orderedInterval (-88378756332 / 1000000000000) (-88378756105 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 3) <| besselDerivativeNearFromState (200564266935793 / 1600000000000) 3 (IntervalRat.scale (421 / 4) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (32487997928 / 1000000000000) (32487997929 / 1000000000000), orderedInterval (63298983855 / 1000000000000) (63298983856 / 1000000000000)))) (orderedInterval (-28140134139 / 1000000000000) (-28140106863 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 3) <| besselDerivativeNearFromState (180976720095347 / 8000000000000) 3 (IntervalRat.scale (421 / 4) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-165592097429 / 1000000000000) (-165592097427 / 1000000000000), orderedInterval (-23067525142 / 1000000000000) (-23067525140 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 3) <| besselDerivativeNearFromState (486128926657559 / 8000000000000) 3 (IntervalRat.scale (421 / 4) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-98126141562 / 1000000000000) (-98126140369 / 1000000000000), orderedInterval (29919582428 / 1000000000000) (29919583620 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 3) <| besselDerivativeNearFromState (1319934601419003 / 8000000000000) 3 (IntervalRat.scale (421 / 4) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (41328460328 / 1000000000000) (41328493359 / 1000000000000), orderedInterval (-46498222697 / 1000000000000) (-46498189666 / 1000000000000)))) (orderedInterval (-13024782930 / 1000000000000) (-13024773791 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 3) <| besselDerivativeNearFromState (972257853315539 / 8000000000000) 3 (IntervalRat.scale (421 / 4) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (14769595595 / 1000000000000) (14769595717 / 1000000000000), orderedInterval (-70913984455 / 1000000000000) (-70913984332 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 3) <| besselDerivativeNearFromState (1665980403260447 / 8000000000000) 3 (IntervalRat.scale (421 / 4) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (54915990818 / 1000000000000) (54915991174 / 1000000000000), orderedInterval (-6555170880 / 1000000000000) (-6555170525 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 3) <| besselDerivativeNearFromState (1227153624730973 / 8000000000000) 3 (IntervalRat.scale (421 / 4) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-15359985930 / 1000000000000) (-15359985929 / 1000000000000), orderedInterval (-62514387557 / 1000000000000) (-62514387556 / 1000000000000)))) (orderedInterval (3040202936 / 1000000000000) (3040203055 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate227_chunkChecks3_1 :
    compactCertificate227.chunkChecks (3 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 3) <| besselDerivativeNearFromState (1882769237054579 / 8000000000000) 3 (IntervalRat.scale (421 / 4) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-25461402971 / 1000000000000) (-25461402970 / 1000000000000), orderedInterval (-45297377836 / 1000000000000) (-45297377835 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 3) <| besselDerivativeNearFromState (1087017325835291 / 8000000000000) 3 (IntervalRat.scale (421 / 4) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-68448532078 / 1000000000000) (-68448532034 / 1000000000000), orderedInterval (413655251 / 1000000000000) (413655295 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 3) <| besselDerivativeNearFromState (1928931320026519 / 8000000000000) 3 (IntervalRat.scale (421 / 4) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (68832524 / 1000000000000) (68832527 / 1000000000000), orderedInterval (-51384005585 / 1000000000000) (-51384005583 / 1000000000000)))) (orderedInterval (-2096180882 / 1000000000000) (-2096180463 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 3) <| besselDerivativeNearFromState (1802257853558611 / 8000000000000) 3 (IntervalRat.scale (421 / 4) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-6764476947 / 1000000000000) (-6764476929 / 1000000000000), orderedInterval (52741905080 / 1000000000000) (52741905098 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 3) <| besselDerivativeNearFromState (1286176245050563 / 8000000000000) 3 (IntervalRat.scale (421 / 4) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-61191519387 / 1000000000000) (-61191519385 / 1000000000000), orderedInterval (-14484431128 / 1000000000000) (-14484431126 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 3) <| besselDerivativeNearFromState (1458386779972677 / 8000000000000) 3 (IntervalRat.scale (421 / 4) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (45193854000 / 1000000000000) (45193854001 / 1000000000000), orderedInterval (37950965088 / 1000000000000) (37950965089 / 1000000000000)))) (orderedInterval (15086840864 / 1000000000000) (15086840926 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 3) <| besselDerivativeNearFromState (1215850852676213 / 8000000000000) 3 (IntervalRat.scale (421 / 4) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (59644781128 / 1000000000000) (59644787700 / 1000000000000), orderedInterval (-25321622337 / 1000000000000) (-25321615765 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 3) <| besselDerivativeNearFromState (1074241101396473 / 8000000000000) 3 (IntervalRat.scale (421 / 4) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (1644030530 / 1000000000000) (1644030538 / 1000000000000), orderedInterval (-68841522427 / 1000000000000) (-68841522420 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 3) <| besselDerivativeNearFromState (311356941742827 / 1600000000000) 3 (IntervalRat.scale (421 / 4) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (32488887206 / 1000000000000) (32488887207 / 1000000000000), orderedInterval (46990248528 / 1000000000000) (46990248529 / 1000000000000)))) (orderedInterval (-14864742088 / 1000000000000) (-14864741823 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate227_chunkChecks3_2 :
    compactCertificate227.chunkChecks (3 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 3) <| besselDerivativeNearFromState (861229686678769 / 8000000000000) 3 (IntervalRat.scale (421 / 4) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (76791461505 / 1000000000000) (76791461581 / 1000000000000), orderedInterval (-4430564054 / 1000000000000) (-4430563978 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 3) <| besselDerivativeNearFromState (730073943255209 / 8000000000000) 3 (IntervalRat.scale (421 / 4) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-67304572287 / 1000000000000) (-67304572286 / 1000000000000), orderedInterval (-49088426683 / 1000000000000) (-49088426682 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 3) <| besselDerivativeNearFromState (456846375269027 / 8000000000000) 3 (IntervalRat.scale (421 / 4) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (102791036670 / 1000000000000) (102791036671 / 1000000000000), orderedInterval (23218446716 / 1000000000000) (23218446717 / 1000000000000)))) (orderedInterval (-2774809590 / 1000000000000) (-2774809553 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 3) <| besselDerivativeNearFromState (245693500022109 / 8000000000000) 3 (IntervalRat.scale (421 / 4) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (11087518805 / 1000000000000) (11087518809 / 1000000000000), orderedInterval (143376794429 / 1000000000000) (143376794432 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 3) <| besselDerivativeNearFromState (667105646753327 / 8000000000000) 3 (IntervalRat.scale (421 / 4) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (52940082019 / 1000000000000) (52940105637 / 1000000000000), orderedInterval (-69828531749 / 1000000000000) (-69828508131 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 3) <| besselDerivativeNearFromState (910875728025679 / 8000000000000) 3 (IntervalRat.scale (421 / 4) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (74752284300 / 1000000000000) (74752284325 / 1000000000000), orderedInterval (1493494866 / 1000000000000) (1493494891 / 1000000000000)))) (orderedInterval (-648149738 / 1000000000000) (-648149454 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 3) <| besselDerivativeNearFromState (385153624730973 / 8000000000000) 3 (IntervalRat.scale (421 / 4) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-111899838650 / 1000000000000) (-111899838086 / 1000000000000), orderedInterval (27637949193 / 1000000000000) (27637949758 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 3) <| besselDerivativeNearFromState (1565628101441533 / 8000000000000) 3 (IntervalRat.scale (421 / 4) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (56486838640 / 1000000000000) (56486839076 / 1000000000000), orderedInterval (-8031498693 / 1000000000000) (-8031498258 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 3) <| besselDerivativeNearFromState (1045767014194547 / 8000000000000) 3 (IntervalRat.scale (421 / 4) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-29823717140 / 1000000000000) (-29823714949 / 1000000000000), orderedInterval (63206370285 / 1000000000000) (63206372476 / 1000000000000)))) (orderedInterval (18429046262 / 1000000000000) (18429047379 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate227_chunkChecks3 :
    compactCertificate227.chunkChecks (3 : Fin 5) 0 9 = true :=
  compactCertificate227.chunkChecks_nine_of_three (3 : Fin 5) compactCertificate227_chunkChecks3_0
    compactCertificate227_chunkChecks3_1 compactCertificate227_chunkChecks3_2

theorem compactCertificate227_chunkChecks4_0 :
    compactCertificate227.chunkChecks (4 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 4) <| besselDerivativeNearFromState (421 / 4) 4 (IntervalRat.scale (421 / 4) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-54692556856 / 1000000000000) (-54692488708 / 1000000000000), orderedInterval (55553291693 / 1000000000000) (55553359841 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 4) <| besselDerivativeNearFromState (620213389066321 / 8000000000000) 4 (IntervalRat.scale (421 / 4) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (20601894409 / 1000000000000) (20601894636 / 1000000000000), orderedInterval (-88378756332 / 1000000000000) (-88378756105 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 4) <| besselDerivativeNearFromState (200564266935793 / 1600000000000) 4 (IntervalRat.scale (421 / 4) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (32487997928 / 1000000000000) (32487997929 / 1000000000000), orderedInterval (63298983855 / 1000000000000) (63298983856 / 1000000000000)))) (orderedInterval (-17249412925 / 1000000000000) (-17249385393 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 4) <| besselDerivativeNearFromState (180976720095347 / 8000000000000) 4 (IntervalRat.scale (421 / 4) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-165592097429 / 1000000000000) (-165592097427 / 1000000000000), orderedInterval (-23067525142 / 1000000000000) (-23067525140 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 4) <| besselDerivativeNearFromState (486128926657559 / 8000000000000) 4 (IntervalRat.scale (421 / 4) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-98126141562 / 1000000000000) (-98126140369 / 1000000000000), orderedInterval (29919582428 / 1000000000000) (29919583620 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 4) <| besselDerivativeNearFromState (1319934601419003 / 8000000000000) 4 (IntervalRat.scale (421 / 4) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (41328460328 / 1000000000000) (41328493359 / 1000000000000), orderedInterval (-46498222697 / 1000000000000) (-46498189666 / 1000000000000)))) (orderedInterval (-17888602981 / 1000000000000) (-17888588579 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 4) <| besselDerivativeNearFromState (972257853315539 / 8000000000000) 4 (IntervalRat.scale (421 / 4) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (14769595595 / 1000000000000) (14769595717 / 1000000000000), orderedInterval (-70913984455 / 1000000000000) (-70913984332 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 4) <| besselDerivativeNearFromState (1665980403260447 / 8000000000000) 4 (IntervalRat.scale (421 / 4) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (54915990818 / 1000000000000) (54915991174 / 1000000000000), orderedInterval (-6555170880 / 1000000000000) (-6555170525 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 4) <| besselDerivativeNearFromState (1227153624730973 / 8000000000000) 4 (IntervalRat.scale (421 / 4) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-15359985930 / 1000000000000) (-15359985929 / 1000000000000), orderedInterval (-62514387557 / 1000000000000) (-62514387556 / 1000000000000)))) (orderedInterval (-27691724615 / 1000000000000) (-27691724383 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate227_chunkChecks4_1 :
    compactCertificate227.chunkChecks (4 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 4) <| besselDerivativeNearFromState (1882769237054579 / 8000000000000) 4 (IntervalRat.scale (421 / 4) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-25461402971 / 1000000000000) (-25461402970 / 1000000000000), orderedInterval (-45297377836 / 1000000000000) (-45297377835 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 4) <| besselDerivativeNearFromState (1087017325835291 / 8000000000000) 4 (IntervalRat.scale (421 / 4) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-68448532078 / 1000000000000) (-68448532034 / 1000000000000), orderedInterval (413655251 / 1000000000000) (413655295 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 4) <| besselDerivativeNearFromState (1928931320026519 / 8000000000000) 4 (IntervalRat.scale (421 / 4) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (68832524 / 1000000000000) (68832527 / 1000000000000), orderedInterval (-51384005585 / 1000000000000) (-51384005583 / 1000000000000)))) (orderedInterval (99325229805 / 1000000000000) (99325230733 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 4) <| besselDerivativeNearFromState (1802257853558611 / 8000000000000) 4 (IntervalRat.scale (421 / 4) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-6764476947 / 1000000000000) (-6764476929 / 1000000000000), orderedInterval (52741905080 / 1000000000000) (52741905098 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 4) <| besselDerivativeNearFromState (1286176245050563 / 8000000000000) 4 (IntervalRat.scale (421 / 4) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-61191519387 / 1000000000000) (-61191519385 / 1000000000000), orderedInterval (-14484431128 / 1000000000000) (-14484431126 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 4) <| besselDerivativeNearFromState (1458386779972677 / 8000000000000) 4 (IntervalRat.scale (421 / 4) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (45193854000 / 1000000000000) (45193854001 / 1000000000000), orderedInterval (37950965088 / 1000000000000) (37950965089 / 1000000000000)))) (orderedInterval (-31284458212 / 1000000000000) (-31284458104 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 4) <| besselDerivativeNearFromState (1215850852676213 / 8000000000000) 4 (IntervalRat.scale (421 / 4) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (59644781128 / 1000000000000) (59644787700 / 1000000000000), orderedInterval (-25321622337 / 1000000000000) (-25321615765 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 4) <| besselDerivativeNearFromState (1074241101396473 / 8000000000000) 4 (IntervalRat.scale (421 / 4) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (1644030530 / 1000000000000) (1644030538 / 1000000000000), orderedInterval (-68841522427 / 1000000000000) (-68841522420 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 4) <| besselDerivativeNearFromState (311356941742827 / 1600000000000) 4 (IntervalRat.scale (421 / 4) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (32488887206 / 1000000000000) (32488887207 / 1000000000000), orderedInterval (46990248528 / 1000000000000) (46990248529 / 1000000000000)))) (orderedInterval (12748345340 / 1000000000000) (12748345729 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate227_chunkChecks4_2 :
    compactCertificate227.chunkChecks (4 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 4) <| besselDerivativeNearFromState (861229686678769 / 8000000000000) 4 (IntervalRat.scale (421 / 4) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (76791461505 / 1000000000000) (76791461581 / 1000000000000), orderedInterval (-4430564054 / 1000000000000) (-4430563978 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 4) <| besselDerivativeNearFromState (730073943255209 / 8000000000000) 4 (IntervalRat.scale (421 / 4) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-67304572287 / 1000000000000) (-67304572286 / 1000000000000), orderedInterval (-49088426683 / 1000000000000) (-49088426682 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 4) <| besselDerivativeNearFromState (456846375269027 / 8000000000000) 4 (IntervalRat.scale (421 / 4) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (102791036670 / 1000000000000) (102791036671 / 1000000000000), orderedInterval (23218446716 / 1000000000000) (23218446717 / 1000000000000)))) (orderedInterval (-10942328785 / 1000000000000) (-10942328748 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 4) <| besselDerivativeNearFromState (245693500022109 / 8000000000000) 4 (IntervalRat.scale (421 / 4) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (11087518805 / 1000000000000) (11087518809 / 1000000000000), orderedInterval (143376794429 / 1000000000000) (143376794432 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 4) <| besselDerivativeNearFromState (667105646753327 / 8000000000000) 4 (IntervalRat.scale (421 / 4) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (52940082019 / 1000000000000) (52940105637 / 1000000000000), orderedInterval (-69828531749 / 1000000000000) (-69828508131 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 4) <| besselDerivativeNearFromState (910875728025679 / 8000000000000) 4 (IntervalRat.scale (421 / 4) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (74752284300 / 1000000000000) (74752284325 / 1000000000000), orderedInterval (1493494866 / 1000000000000) (1493494891 / 1000000000000)))) (orderedInterval (-8307984514 / 1000000000000) (-8307984282 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 4) <| besselDerivativeNearFromState (385153624730973 / 8000000000000) 4 (IntervalRat.scale (421 / 4) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-111899838650 / 1000000000000) (-111899838086 / 1000000000000), orderedInterval (27637949193 / 1000000000000) (27637949758 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 4) <| besselDerivativeNearFromState (1565628101441533 / 8000000000000) 4 (IntervalRat.scale (421 / 4) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (56486838640 / 1000000000000) (56486839076 / 1000000000000), orderedInterval (-8031498693 / 1000000000000) (-8031498258 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 4) <| besselDerivativeNearFromState (1045767014194547 / 8000000000000) 4 (IntervalRat.scale (421 / 4) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-29823717140 / 1000000000000) (-29823714949 / 1000000000000), orderedInterval (63206370285 / 1000000000000) (63206372476 / 1000000000000)))) (orderedInterval (-42028972930 / 1000000000000) (-42028971358 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate227_chunkChecks4 :
    compactCertificate227.chunkChecks (4 : Fin 5) 0 9 = true :=
  compactCertificate227.chunkChecks_nine_of_three (4 : Fin 5) compactCertificate227_chunkChecks4_0
    compactCertificate227_chunkChecks4_1 compactCertificate227_chunkChecks4_2

theorem compactCertificate227_chunks :
    ∀ r : Fin 5, ∀ b, compactCertificate227.chunkCheck r b = true :=
  compactCertificate227.chunkChecks_all (by
    intro r
    fin_cases r
    · exact compactCertificate227_chunkChecks0
    · exact compactCertificate227_chunkChecks1
    · exact compactCertificate227_chunkChecks2
    · exact compactCertificate227_chunkChecks3
    · exact compactCertificate227_chunkChecks4)

theorem compactCertificate227_coefficient0 :
    compactCertificate227.coefficientCheck (0 : Fin 5) = true := by
  norm_num [CompactCertificate.coefficientCheck, intervalFinSumHull,
    compactCertificate227, rationalIntervalSubset, orderedInterval, Fin.sum_univ_succ]

theorem compactCertificate227_coefficient1 :
    compactCertificate227.coefficientCheck (1 : Fin 5) = true := by
  norm_num [CompactCertificate.coefficientCheck, intervalFinSumHull,
    compactCertificate227, rationalIntervalSubset, orderedInterval, Fin.sum_univ_succ]

theorem compactCertificate227_coefficient2 :
    compactCertificate227.coefficientCheck (2 : Fin 5) = true := by
  norm_num [CompactCertificate.coefficientCheck, intervalFinSumHull,
    compactCertificate227, rationalIntervalSubset, orderedInterval, Fin.sum_univ_succ]

theorem compactCertificate227_coefficient3 :
    compactCertificate227.coefficientCheck (3 : Fin 5) = true := by
  norm_num [CompactCertificate.coefficientCheck, intervalFinSumHull,
    compactCertificate227, rationalIntervalSubset, orderedInterval, Fin.sum_univ_succ]

theorem compactCertificate227_coefficient4 :
    compactCertificate227.coefficientCheck (4 : Fin 5) = true := by
  norm_num [CompactCertificate.coefficientCheck, intervalFinSumHull,
    compactCertificate227, rationalIntervalSubset, orderedInterval, Fin.sum_univ_succ]

theorem compactCertificate227_coefficients : ∀ r : Fin 5,
    compactCertificate227.coefficientCheck r = true := by
  intro r
  fin_cases r
  · exact compactCertificate227_coefficient0
  · exact compactCertificate227_coefficient1
  · exact compactCertificate227_coefficient2
  · exact compactCertificate227_coefficient3
  · exact compactCertificate227_coefficient4

theorem compactCertificate227_lower : (1 : ℚ) ≤ compactCertificate227.output.lo := by
  norm_num [CompactCertificate.output, CompactCertificate.interval,
    CompactCertificate.coefficientTargetNat, compactCertificate227, dualConstant,
    intervalTaylorSum, intervalPow, intervalSub, intervalMaxAbs, widenInterval,
    rationalErrorInterval, orderedInterval, IntervalRat.add, IntervalRat.mul, IntervalRat.scale,
    IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4]

theorem compactCertificate227_proves {t : ℝ} (ht : t ∈ compactCertificate227.interval) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t :=
  compactCertificate227.proves compactCertificate227_states compactCertificate227_chunks
    compactCertificate227_coefficients compactCertificate227_lower ht

end Erdos232
