/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, OpenAI Codex
-/
import ErdosProblems.Erdos232.CompactBase

open LeanCert.Core
namespace Erdos232

def compactCertificate234 : CompactCertificate where
  left := 111
  right := 112
  center := 223 / 2
  grid := fun i =>
    match i.val with
    | 0 => 36
    | 1 => 26
    | 2 => 42
    | 3 => 8
    | 4 => 21
    | 5 => 56
    | 6 => 41
    | 7 => 70
    | 8 => 52
    | 9 => 79
    | 10 => 46
    | 11 => 81
    | 12 => 76
    | 13 => 54
    | 14 => 62
    | 15 => 51
    | 16 => 45
    | 17 => 66
    | 18 => 36
    | 19 => 31
    | 20 => 19
    | 21 => 10
    | 22 => 28
    | 23 => 38
    | 24 => 16
    | 25 => 66
    | _ => 44
  point := fun i =>
    match i.val with
    | 0 => 223 / 2
    | 1 => 328521581381923 / 4000000000000
    | 2 => 106237129517059 / 800000000000
    | 3 => 95861778102761 / 4000000000000
    | 4 => 257498220058517 / 4000000000000
    | 5 => 699157757996289 / 4000000000000
    | 6 => 514996440117257 / 4000000000000
    | 7 => 882455177974061 / 4000000000000
    | 8 => 650012490059399 / 4000000000000
    | 9 => 997286317964777 / 4000000000000
    | 10 => 575783524136033 / 4000000000000
    | 11 => 1021737967614997 / 4000000000000
    | 12 => 954640145709193 / 4000000000000
    | 13 => 681276253316569 / 4000000000000
    | 14 => 772494660175551 / 4000000000000
    | 15 => 644025511037519 / 4000000000000
    | 16 => 569016070335899 / 4000000000000
    | 17 => 164923035650001 / 800000000000
    | 18 => 456185796031747 / 4000000000000
    | 19 => 386713751415467 / 4000000000000
    | 20 => 241987509940601 / 4000000000000
    | 21 => 130141687660167 / 4000000000000
    | 22 => 353359998161501 / 4000000000000
    | 23 => 482482867814077 / 4000000000000
    | 24 => 204012490059399 / 4000000000000
    | 25 => 829299445656679 / 4000000000000
    | _ => 553933596592361 / 4000000000000
  state := fun i =>
    match i.val with
    | 0 => (orderedInterval (-54887335618 / 1000000000000) (-54887247610 / 1000000000000), orderedInterval (52178499284 / 1000000000000) (52178587292 / 1000000000000))
    | 1 => (orderedInterval (83061385748 / 1000000000000) (83061385749 / 1000000000000), orderedInterval (28683798692 / 1000000000000) (28683798693 / 1000000000000))
    | 2 => (orderedInterval (69099985638 / 1000000000000) (69099985742 / 1000000000000), orderedInterval (-4631826019 / 1000000000000) (-4631825915 / 1000000000000))
    | 3 => (orderedInterval (-61522324603 / 1000000000000) (-61522322522 / 1000000000000), orderedInterval (152224045713 / 1000000000000) (152224047794 / 1000000000000))
    | 4 => (orderedInterval (72397119624 / 1000000000000) (72397228528 / 1000000000000), orderedInterval (-68738118473 / 1000000000000) (-68738009569 / 1000000000000))
    | 5 => (orderedInterval (-20981025550 / 1000000000000) (-20981024939 / 1000000000000), orderedInterval (56646388926 / 1000000000000) (56646389537 / 1000000000000))
    | 6 => (orderedInterval (-46800545593 / 1000000000000) (-46800545592 / 1000000000000), orderedInterval (-52300314975 / 1000000000000) (-52300314974 / 1000000000000))
    | 7 => (orderedInterval (53530552742 / 1000000000000) (53530552765 / 1000000000000), orderedInterval (4367318917 / 1000000000000) (4367318940 / 1000000000000))
    | 8 => (orderedInterval (-4694036363 / 1000000000000) (-4694036350 / 1000000000000), orderedInterval (62428938011 / 1000000000000) (62428938024 / 1000000000000))
    | 9 => (orderedInterval (-47470061618 / 1000000000000) (-47470055031 / 1000000000000), orderedInterval (17415640699 / 1000000000000) (17415647286 / 1000000000000))
    | 10 => (orderedInterval (14327751391 / 1000000000000) (14327751392 / 1000000000000), orderedInterval (64891533364 / 1000000000000) (64891533365 / 1000000000000))
    | 11 => (orderedInterval (-49119914806 / 1000000000000) (-49119913766 / 1000000000000), orderedInterval (9014168138 / 1000000000000) (9014169177 / 1000000000000))
    | 12 => (orderedInterval (32630760951 / 1000000000000) (32630760952 / 1000000000000), orderedInterval (39965498591 / 1000000000000) (39965498592 / 1000000000000))
    | 13 => (orderedInterval (60747060884 / 1000000000000) (60747060894 / 1000000000000), orderedInterval (6719915366 / 1000000000000) (6719915376 / 1000000000000))
    | 14 => (orderedInterval (-43895773509 / 1000000000000) (-43895672562 / 1000000000000), orderedInterval (37121691181 / 1000000000000) (37121792128 / 1000000000000))
    | 15 => (orderedInterval (-62880682669 / 1000000000000) (-62880682618 / 1000000000000), orderedInterval (131002038 / 1000000000000) (131002089 / 1000000000000))
    | 16 => (orderedInterval (-66588488386 / 1000000000000) (-66588488211 / 1000000000000), orderedInterval (6651083053 / 1000000000000) (6651083228 / 1000000000000))
    | 17 => (orderedInterval (-21973847349 / 1000000000000) (-21973846407 / 1000000000000), orderedInterval (51094826617 / 1000000000000) (51094827559 / 1000000000000))
    | 18 => (orderedInterval (73727436259 / 1000000000000) (73727436609 / 1000000000000), orderedInterval (-12419667333 / 1000000000000) (-12419666983 / 1000000000000))
    | 19 => (orderedInterval (-5932299008 / 1000000000000) (-5932299006 / 1000000000000), orderedInterval (-80900246780 / 1000000000000) (-80900246778 / 1000000000000))
    | 20 => (orderedInterval (-102562005929 / 1000000000000) (-102562005897 / 1000000000000), orderedInterval (2812280605 / 1000000000000) (2812280638 / 1000000000000))
    | 21 => (orderedInterval (132314836072 / 1000000000000) (132314837748 / 1000000000000), orderedInterval (-47397406668 / 1000000000000) (-47397404993 / 1000000000000))
    | 22 => (orderedInterval (77806914490 / 1000000000000) (77806914491 / 1000000000000), orderedInterval (33507797324 / 1000000000000) (33507797325 / 1000000000000))
    | 23 => (orderedInterval (65296884888 / 1000000000000) (65296894687 / 1000000000000), orderedInterval (-32116431529 / 1000000000000) (-32116421730 / 1000000000000))
    | 24 => (orderedInterval (111579295965 / 1000000000000) (111579295975 / 1000000000000), orderedInterval (4513461919 / 1000000000000) (4513461930 / 1000000000000))
    | 25 => (orderedInterval (38357405060 / 1000000000000) (38357405061 / 1000000000000), orderedInterval (39899352791 / 1000000000000) (39899352792 / 1000000000000))
    | _ => (orderedInterval (58397332869 / 1000000000000) (58397332870 / 1000000000000), orderedInterval (34239420777 / 1000000000000) (34239420778 / 1000000000000))
  chunkTarget := fun r b =>
    match r.val with
    | 0 =>
      match b.val with
      | 0 => orderedInterval (-16926581495 / 1000000000000) (-16926546597 / 1000000000000)
      | 1 => orderedInterval (4802352347 / 1000000000000) (4802356403 / 1000000000000)
      | 2 => orderedInterval (-1764542024 / 1000000000000) (-1764542016 / 1000000000000)
      | 3 => orderedInterval (2513738774 / 1000000000000) (2513740137 / 1000000000000)
      | 4 => orderedInterval (5377467625 / 1000000000000) (5377468151 / 1000000000000)
      | 5 => orderedInterval (2521895239 / 1000000000000) (2521895286 / 1000000000000)
      | 6 => orderedInterval (-14791625931 / 1000000000000) (-14791625845 / 1000000000000)
      | 7 => orderedInterval (-9212683922 / 1000000000000) (-9212683126 / 1000000000000)
      | _ => orderedInterval (-13406613107 / 1000000000000) (-13406613075 / 1000000000000)
    | 1 =>
      match b.val with
      | 0 => orderedInterval (20554891215 / 1000000000000) (20554926115 / 1000000000000)
      | 1 => orderedInterval (-8116731223 / 1000000000000) (-8116728839 / 1000000000000)
      | 2 => orderedInterval (1932414721 / 1000000000000) (1932414735 / 1000000000000)
      | 3 => orderedInterval (2222973015 / 1000000000000) (2222976063 / 1000000000000)
      | 4 => orderedInterval (-899041317 / 1000000000000) (-899040408 / 1000000000000)
      | 5 => orderedInterval (1935384564 / 1000000000000) (1935384639 / 1000000000000)
      | 6 => orderedInterval (6051114039 / 1000000000000) (6051114124 / 1000000000000)
      | 7 => orderedInterval (2315801084 / 1000000000000) (2315801918 / 1000000000000)
      | _ => orderedInterval (-14005618843 / 1000000000000) (-14005618798 / 1000000000000)
    | 2 =>
      match b.val with
      | 0 => orderedInterval (15399356068 / 1000000000000) (15399391283 / 1000000000000)
      | 1 => orderedInterval (-4504491489 / 1000000000000) (-4504490012 / 1000000000000)
      | 2 => orderedInterval (6687439792 / 1000000000000) (6687439816 / 1000000000000)
      | 3 => orderedInterval (-7317060580 / 1000000000000) (-7317053728 / 1000000000000)
      | 4 => orderedInterval (-11363078814 / 1000000000000) (-11363077235 / 1000000000000)
      | 5 => orderedInterval (-2782631599 / 1000000000000) (-2782631475 / 1000000000000)
      | 6 => orderedInterval (13009289318 / 1000000000000) (13009289403 / 1000000000000)
      | 7 => orderedInterval (7151771187 / 1000000000000) (7151772089 / 1000000000000)
      | _ => orderedInterval (27682003617 / 1000000000000) (27682003682 / 1000000000000)
    | 3 =>
      match b.val with
      | 0 => orderedInterval (-20465860009 / 1000000000000) (-20465824796 / 1000000000000)
      | 1 => orderedInterval (16052278760 / 1000000000000) (16052279737 / 1000000000000)
      | 2 => orderedInterval (-3687163289 / 1000000000000) (-3687163246 / 1000000000000)
      | 3 => orderedInterval (8912376254 / 1000000000000) (8912391606 / 1000000000000)
      | 4 => orderedInterval (5888473158 / 1000000000000) (5888475891 / 1000000000000)
      | 5 => orderedInterval (-7457644424 / 1000000000000) (-7457644212 / 1000000000000)
      | 6 => orderedInterval (-5240713404 / 1000000000000) (-5240713319 / 1000000000000)
      | 7 => orderedInterval (-2823777362 / 1000000000000) (-2823776390 / 1000000000000)
      | _ => orderedInterval (32935990308 / 1000000000000) (32935990408 / 1000000000000)
    | _ =>
      match b.val with
      | 0 => orderedInterval (-13000522016 / 1000000000000) (-13000486489 / 1000000000000)
      | 1 => orderedInterval (9014133230 / 1000000000000) (9014134000 / 1000000000000)
      | 2 => orderedInterval (-25750008690 / 1000000000000) (-25750008612 / 1000000000000)
      | 3 => orderedInterval (21332336814 / 1000000000000) (21332371368 / 1000000000000)
      | 4 => orderedInterval (20802744678 / 1000000000000) (20802749435 / 1000000000000)
      | 5 => orderedInterval (497890533 / 1000000000000) (497890904 / 1000000000000)
      | 6 => orderedInterval (-12907352830 / 1000000000000) (-12907352743 / 1000000000000)
      | 7 => orderedInterval (-7515803389 / 1000000000000) (-7515802330 / 1000000000000)
      | _ => orderedInterval (-63955437470 / 1000000000000) (-63955437309 / 1000000000000)
  coefficientTarget := fun i =>
    match i.val with
    | 0 => orderedInterval (-40886592494 / 1000000000000) (-40886550682 / 1000000000000)
    | 1 => orderedInterval (11991187255 / 1000000000000) (11991229549 / 1000000000000)
    | 2 => orderedInterval (43962597500 / 1000000000000) (43962643823 / 1000000000000)
    | 3 => orderedInterval (24113959992 / 1000000000000) (24114015679 / 1000000000000)
    | _ => orderedInterval (-71482019140 / 1000000000000) (-71481941776 / 1000000000000)

theorem compactCertificate234_stateChecks0 :
    compactCertificate234.stateChecks 0 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 36 12 (223 / 2)) (orderedInterval (-54887335618 / 1000000000000) (-54887247610 / 1000000000000), orderedInterval (52178499284 / 1000000000000) (52178587292 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 26 12 (328521581381923 / 4000000000000)) (orderedInterval (83061385748 / 1000000000000) (83061385749 / 1000000000000), orderedInterval (28683798692 / 1000000000000) (28683798693 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 42 12 (106237129517059 / 800000000000)) (orderedInterval (69099985638 / 1000000000000) (69099985742 / 1000000000000), orderedInterval (-4631826019 / 1000000000000) (-4631825915 / 1000000000000))) = true
  norm_num [besselStateAtRationalPoint, besselIntervalStepZero,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, besselZeroTransition,
    besselInitial, besselGridStateAt, besselGridStateBlock00, besselGridStateBlock01,
    besselGridStateBlock02, besselGridStateBlock03, besselGridStateBlock04,
    besselGridStateBlock05, besselGridStateBlock06, besselGridStateBlock07,
    besselGridStateBlock08, besselGridStateBlock09, besselGridStateBlock10,
    besselGridStateBlock11, besselGridStateBlock12, besselGridStateBlock13,
    besselGridStateBlock14, besselGridState008, besselGridState010, besselGridState016, besselGridState019, besselGridState021, besselGridState026, besselGridState028, besselGridState031, besselGridState036, besselGridState038, besselGridState041, besselGridState042, besselGridState044, besselGridState045, besselGridState046, besselGridState051, besselGridState052, besselGridState054, besselGridState056, besselGridState062, besselGridState066, besselGridState070, besselGridState076, besselGridState079, besselGridState081, besselStateSubset, linearInterval, widenInterval,
    rationalErrorInterval, rationalIntervalSubset, orderedInterval, Finset.sum_range_succ,
    IntervalRat.add, IntervalRat.mul, IntervalRat.scale, IntervalRat.singleton]

theorem compactCertificate234_stateChecks1 :
    compactCertificate234.stateChecks 3 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 8 12 (95861778102761 / 4000000000000)) (orderedInterval (-61522324603 / 1000000000000) (-61522322522 / 1000000000000), orderedInterval (152224045713 / 1000000000000) (152224047794 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 21 12 (257498220058517 / 4000000000000)) (orderedInterval (72397119624 / 1000000000000) (72397228528 / 1000000000000), orderedInterval (-68738118473 / 1000000000000) (-68738009569 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 56 12 (699157757996289 / 4000000000000)) (orderedInterval (-20981025550 / 1000000000000) (-20981024939 / 1000000000000), orderedInterval (56646388926 / 1000000000000) (56646389537 / 1000000000000))) = true
  norm_num [besselStateAtRationalPoint, besselIntervalStepZero,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, besselZeroTransition,
    besselInitial, besselGridStateAt, besselGridStateBlock00, besselGridStateBlock01,
    besselGridStateBlock02, besselGridStateBlock03, besselGridStateBlock04,
    besselGridStateBlock05, besselGridStateBlock06, besselGridStateBlock07,
    besselGridStateBlock08, besselGridStateBlock09, besselGridStateBlock10,
    besselGridStateBlock11, besselGridStateBlock12, besselGridStateBlock13,
    besselGridStateBlock14, besselGridState008, besselGridState010, besselGridState016, besselGridState019, besselGridState021, besselGridState026, besselGridState028, besselGridState031, besselGridState036, besselGridState038, besselGridState041, besselGridState042, besselGridState044, besselGridState045, besselGridState046, besselGridState051, besselGridState052, besselGridState054, besselGridState056, besselGridState062, besselGridState066, besselGridState070, besselGridState076, besselGridState079, besselGridState081, besselStateSubset, linearInterval, widenInterval,
    rationalErrorInterval, rationalIntervalSubset, orderedInterval, Finset.sum_range_succ,
    IntervalRat.add, IntervalRat.mul, IntervalRat.scale, IntervalRat.singleton]

theorem compactCertificate234_stateChecks2 :
    compactCertificate234.stateChecks 6 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 41 12 (514996440117257 / 4000000000000)) (orderedInterval (-46800545593 / 1000000000000) (-46800545592 / 1000000000000), orderedInterval (-52300314975 / 1000000000000) (-52300314974 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 70 12 (882455177974061 / 4000000000000)) (orderedInterval (53530552742 / 1000000000000) (53530552765 / 1000000000000), orderedInterval (4367318917 / 1000000000000) (4367318940 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 52 12 (650012490059399 / 4000000000000)) (orderedInterval (-4694036363 / 1000000000000) (-4694036350 / 1000000000000), orderedInterval (62428938011 / 1000000000000) (62428938024 / 1000000000000))) = true
  norm_num [besselStateAtRationalPoint, besselIntervalStepZero,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, besselZeroTransition,
    besselInitial, besselGridStateAt, besselGridStateBlock00, besselGridStateBlock01,
    besselGridStateBlock02, besselGridStateBlock03, besselGridStateBlock04,
    besselGridStateBlock05, besselGridStateBlock06, besselGridStateBlock07,
    besselGridStateBlock08, besselGridStateBlock09, besselGridStateBlock10,
    besselGridStateBlock11, besselGridStateBlock12, besselGridStateBlock13,
    besselGridStateBlock14, besselGridState008, besselGridState010, besselGridState016, besselGridState019, besselGridState021, besselGridState026, besselGridState028, besselGridState031, besselGridState036, besselGridState038, besselGridState041, besselGridState042, besselGridState044, besselGridState045, besselGridState046, besselGridState051, besselGridState052, besselGridState054, besselGridState056, besselGridState062, besselGridState066, besselGridState070, besselGridState076, besselGridState079, besselGridState081, besselStateSubset, linearInterval, widenInterval,
    rationalErrorInterval, rationalIntervalSubset, orderedInterval, Finset.sum_range_succ,
    IntervalRat.add, IntervalRat.mul, IntervalRat.scale, IntervalRat.singleton]

theorem compactCertificate234_stateChecks3 :
    compactCertificate234.stateChecks 9 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 79 12 (997286317964777 / 4000000000000)) (orderedInterval (-47470061618 / 1000000000000) (-47470055031 / 1000000000000), orderedInterval (17415640699 / 1000000000000) (17415647286 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 46 12 (575783524136033 / 4000000000000)) (orderedInterval (14327751391 / 1000000000000) (14327751392 / 1000000000000), orderedInterval (64891533364 / 1000000000000) (64891533365 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 81 12 (1021737967614997 / 4000000000000)) (orderedInterval (-49119914806 / 1000000000000) (-49119913766 / 1000000000000), orderedInterval (9014168138 / 1000000000000) (9014169177 / 1000000000000))) = true
  norm_num [besselStateAtRationalPoint, besselIntervalStepZero,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, besselZeroTransition,
    besselInitial, besselGridStateAt, besselGridStateBlock00, besselGridStateBlock01,
    besselGridStateBlock02, besselGridStateBlock03, besselGridStateBlock04,
    besselGridStateBlock05, besselGridStateBlock06, besselGridStateBlock07,
    besselGridStateBlock08, besselGridStateBlock09, besselGridStateBlock10,
    besselGridStateBlock11, besselGridStateBlock12, besselGridStateBlock13,
    besselGridStateBlock14, besselGridState008, besselGridState010, besselGridState016, besselGridState019, besselGridState021, besselGridState026, besselGridState028, besselGridState031, besselGridState036, besselGridState038, besselGridState041, besselGridState042, besselGridState044, besselGridState045, besselGridState046, besselGridState051, besselGridState052, besselGridState054, besselGridState056, besselGridState062, besselGridState066, besselGridState070, besselGridState076, besselGridState079, besselGridState081, besselStateSubset, linearInterval, widenInterval,
    rationalErrorInterval, rationalIntervalSubset, orderedInterval, Finset.sum_range_succ,
    IntervalRat.add, IntervalRat.mul, IntervalRat.scale, IntervalRat.singleton]

theorem compactCertificate234_stateChecks4 :
    compactCertificate234.stateChecks 12 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 76 12 (954640145709193 / 4000000000000)) (orderedInterval (32630760951 / 1000000000000) (32630760952 / 1000000000000), orderedInterval (39965498591 / 1000000000000) (39965498592 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 54 12 (681276253316569 / 4000000000000)) (orderedInterval (60747060884 / 1000000000000) (60747060894 / 1000000000000), orderedInterval (6719915366 / 1000000000000) (6719915376 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 62 12 (772494660175551 / 4000000000000)) (orderedInterval (-43895773509 / 1000000000000) (-43895672562 / 1000000000000), orderedInterval (37121691181 / 1000000000000) (37121792128 / 1000000000000))) = true
  norm_num [besselStateAtRationalPoint, besselIntervalStepZero,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, besselZeroTransition,
    besselInitial, besselGridStateAt, besselGridStateBlock00, besselGridStateBlock01,
    besselGridStateBlock02, besselGridStateBlock03, besselGridStateBlock04,
    besselGridStateBlock05, besselGridStateBlock06, besselGridStateBlock07,
    besselGridStateBlock08, besselGridStateBlock09, besselGridStateBlock10,
    besselGridStateBlock11, besselGridStateBlock12, besselGridStateBlock13,
    besselGridStateBlock14, besselGridState008, besselGridState010, besselGridState016, besselGridState019, besselGridState021, besselGridState026, besselGridState028, besselGridState031, besselGridState036, besselGridState038, besselGridState041, besselGridState042, besselGridState044, besselGridState045, besselGridState046, besselGridState051, besselGridState052, besselGridState054, besselGridState056, besselGridState062, besselGridState066, besselGridState070, besselGridState076, besselGridState079, besselGridState081, besselStateSubset, linearInterval, widenInterval,
    rationalErrorInterval, rationalIntervalSubset, orderedInterval, Finset.sum_range_succ,
    IntervalRat.add, IntervalRat.mul, IntervalRat.scale, IntervalRat.singleton]

theorem compactCertificate234_stateChecks5 :
    compactCertificate234.stateChecks 15 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 51 12 (644025511037519 / 4000000000000)) (orderedInterval (-62880682669 / 1000000000000) (-62880682618 / 1000000000000), orderedInterval (131002038 / 1000000000000) (131002089 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 45 12 (569016070335899 / 4000000000000)) (orderedInterval (-66588488386 / 1000000000000) (-66588488211 / 1000000000000), orderedInterval (6651083053 / 1000000000000) (6651083228 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 66 12 (164923035650001 / 800000000000)) (orderedInterval (-21973847349 / 1000000000000) (-21973846407 / 1000000000000), orderedInterval (51094826617 / 1000000000000) (51094827559 / 1000000000000))) = true
  norm_num [besselStateAtRationalPoint, besselIntervalStepZero,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, besselZeroTransition,
    besselInitial, besselGridStateAt, besselGridStateBlock00, besselGridStateBlock01,
    besselGridStateBlock02, besselGridStateBlock03, besselGridStateBlock04,
    besselGridStateBlock05, besselGridStateBlock06, besselGridStateBlock07,
    besselGridStateBlock08, besselGridStateBlock09, besselGridStateBlock10,
    besselGridStateBlock11, besselGridStateBlock12, besselGridStateBlock13,
    besselGridStateBlock14, besselGridState008, besselGridState010, besselGridState016, besselGridState019, besselGridState021, besselGridState026, besselGridState028, besselGridState031, besselGridState036, besselGridState038, besselGridState041, besselGridState042, besselGridState044, besselGridState045, besselGridState046, besselGridState051, besselGridState052, besselGridState054, besselGridState056, besselGridState062, besselGridState066, besselGridState070, besselGridState076, besselGridState079, besselGridState081, besselStateSubset, linearInterval, widenInterval,
    rationalErrorInterval, rationalIntervalSubset, orderedInterval, Finset.sum_range_succ,
    IntervalRat.add, IntervalRat.mul, IntervalRat.scale, IntervalRat.singleton]

theorem compactCertificate234_stateChecks6 :
    compactCertificate234.stateChecks 18 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 36 12 (456185796031747 / 4000000000000)) (orderedInterval (73727436259 / 1000000000000) (73727436609 / 1000000000000), orderedInterval (-12419667333 / 1000000000000) (-12419666983 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 31 12 (386713751415467 / 4000000000000)) (orderedInterval (-5932299008 / 1000000000000) (-5932299006 / 1000000000000), orderedInterval (-80900246780 / 1000000000000) (-80900246778 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 19 12 (241987509940601 / 4000000000000)) (orderedInterval (-102562005929 / 1000000000000) (-102562005897 / 1000000000000), orderedInterval (2812280605 / 1000000000000) (2812280638 / 1000000000000))) = true
  norm_num [besselStateAtRationalPoint, besselIntervalStepZero,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, besselZeroTransition,
    besselInitial, besselGridStateAt, besselGridStateBlock00, besselGridStateBlock01,
    besselGridStateBlock02, besselGridStateBlock03, besselGridStateBlock04,
    besselGridStateBlock05, besselGridStateBlock06, besselGridStateBlock07,
    besselGridStateBlock08, besselGridStateBlock09, besselGridStateBlock10,
    besselGridStateBlock11, besselGridStateBlock12, besselGridStateBlock13,
    besselGridStateBlock14, besselGridState008, besselGridState010, besselGridState016, besselGridState019, besselGridState021, besselGridState026, besselGridState028, besselGridState031, besselGridState036, besselGridState038, besselGridState041, besselGridState042, besselGridState044, besselGridState045, besselGridState046, besselGridState051, besselGridState052, besselGridState054, besselGridState056, besselGridState062, besselGridState066, besselGridState070, besselGridState076, besselGridState079, besselGridState081, besselStateSubset, linearInterval, widenInterval,
    rationalErrorInterval, rationalIntervalSubset, orderedInterval, Finset.sum_range_succ,
    IntervalRat.add, IntervalRat.mul, IntervalRat.scale, IntervalRat.singleton]

theorem compactCertificate234_stateChecks7 :
    compactCertificate234.stateChecks 21 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 10 12 (130141687660167 / 4000000000000)) (orderedInterval (132314836072 / 1000000000000) (132314837748 / 1000000000000), orderedInterval (-47397406668 / 1000000000000) (-47397404993 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 28 12 (353359998161501 / 4000000000000)) (orderedInterval (77806914490 / 1000000000000) (77806914491 / 1000000000000), orderedInterval (33507797324 / 1000000000000) (33507797325 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 38 12 (482482867814077 / 4000000000000)) (orderedInterval (65296884888 / 1000000000000) (65296894687 / 1000000000000), orderedInterval (-32116431529 / 1000000000000) (-32116421730 / 1000000000000))) = true
  norm_num [besselStateAtRationalPoint, besselIntervalStepZero,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, besselZeroTransition,
    besselInitial, besselGridStateAt, besselGridStateBlock00, besselGridStateBlock01,
    besselGridStateBlock02, besselGridStateBlock03, besselGridStateBlock04,
    besselGridStateBlock05, besselGridStateBlock06, besselGridStateBlock07,
    besselGridStateBlock08, besselGridStateBlock09, besselGridStateBlock10,
    besselGridStateBlock11, besselGridStateBlock12, besselGridStateBlock13,
    besselGridStateBlock14, besselGridState008, besselGridState010, besselGridState016, besselGridState019, besselGridState021, besselGridState026, besselGridState028, besselGridState031, besselGridState036, besselGridState038, besselGridState041, besselGridState042, besselGridState044, besselGridState045, besselGridState046, besselGridState051, besselGridState052, besselGridState054, besselGridState056, besselGridState062, besselGridState066, besselGridState070, besselGridState076, besselGridState079, besselGridState081, besselStateSubset, linearInterval, widenInterval,
    rationalErrorInterval, rationalIntervalSubset, orderedInterval, Finset.sum_range_succ,
    IntervalRat.add, IntervalRat.mul, IntervalRat.scale, IntervalRat.singleton]

theorem compactCertificate234_stateChecks8 :
    compactCertificate234.stateChecks 24 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 16 12 (204012490059399 / 4000000000000)) (orderedInterval (111579295965 / 1000000000000) (111579295975 / 1000000000000), orderedInterval (4513461919 / 1000000000000) (4513461930 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 66 12 (829299445656679 / 4000000000000)) (orderedInterval (38357405060 / 1000000000000) (38357405061 / 1000000000000), orderedInterval (39899352791 / 1000000000000) (39899352792 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 44 12 (553933596592361 / 4000000000000)) (orderedInterval (58397332869 / 1000000000000) (58397332870 / 1000000000000), orderedInterval (34239420777 / 1000000000000) (34239420778 / 1000000000000))) = true
  norm_num [besselStateAtRationalPoint, besselIntervalStepZero,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, besselZeroTransition,
    besselInitial, besselGridStateAt, besselGridStateBlock00, besselGridStateBlock01,
    besselGridStateBlock02, besselGridStateBlock03, besselGridStateBlock04,
    besselGridStateBlock05, besselGridStateBlock06, besselGridStateBlock07,
    besselGridStateBlock08, besselGridStateBlock09, besselGridStateBlock10,
    besselGridStateBlock11, besselGridStateBlock12, besselGridStateBlock13,
    besselGridStateBlock14, besselGridState008, besselGridState010, besselGridState016, besselGridState019, besselGridState021, besselGridState026, besselGridState028, besselGridState031, besselGridState036, besselGridState038, besselGridState041, besselGridState042, besselGridState044, besselGridState045, besselGridState046, besselGridState051, besselGridState052, besselGridState054, besselGridState056, besselGridState062, besselGridState066, besselGridState070, besselGridState076, besselGridState079, besselGridState081, besselStateSubset, linearInterval, widenInterval,
    rationalErrorInterval, rationalIntervalSubset, orderedInterval, Finset.sum_range_succ,
    IntervalRat.add, IntervalRat.mul, IntervalRat.scale, IntervalRat.singleton]

theorem compactCertificate234_states : ∀ j,
    BesselStateValid (compactCertificate234.point j) (compactCertificate234.state j) :=
  compactCertificate234.statesValid_of_checks3 compactCertificate234_stateChecks0
    compactCertificate234_stateChecks1 compactCertificate234_stateChecks2
    compactCertificate234_stateChecks3 compactCertificate234_stateChecks4
    compactCertificate234_stateChecks5 compactCertificate234_stateChecks6
    compactCertificate234_stateChecks7 compactCertificate234_stateChecks8

theorem compactCertificate234_chunkChecks0_0 :
    compactCertificate234.chunkChecks (0 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 0) <| besselDerivativeNearFromState (223 / 2) 0 (IntervalRat.scale (223 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-54887335618 / 1000000000000) (-54887247610 / 1000000000000), orderedInterval (52178499284 / 1000000000000) (52178587292 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 0) <| besselDerivativeNearFromState (328521581381923 / 4000000000000) 0 (IntervalRat.scale (223 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (83061385748 / 1000000000000) (83061385749 / 1000000000000), orderedInterval (28683798692 / 1000000000000) (28683798693 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 0) <| besselDerivativeNearFromState (106237129517059 / 800000000000) 0 (IntervalRat.scale (223 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (69099985638 / 1000000000000) (69099985742 / 1000000000000), orderedInterval (-4631826019 / 1000000000000) (-4631825915 / 1000000000000)))) (orderedInterval (-16926581495 / 1000000000000) (-16926546597 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 0) <| besselDerivativeNearFromState (95861778102761 / 4000000000000) 0 (IntervalRat.scale (223 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-61522324603 / 1000000000000) (-61522322522 / 1000000000000), orderedInterval (152224045713 / 1000000000000) (152224047794 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 0) <| besselDerivativeNearFromState (257498220058517 / 4000000000000) 0 (IntervalRat.scale (223 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (72397119624 / 1000000000000) (72397228528 / 1000000000000), orderedInterval (-68738118473 / 1000000000000) (-68738009569 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 0) <| besselDerivativeNearFromState (699157757996289 / 4000000000000) 0 (IntervalRat.scale (223 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-20981025550 / 1000000000000) (-20981024939 / 1000000000000), orderedInterval (56646388926 / 1000000000000) (56646389537 / 1000000000000)))) (orderedInterval (4802352347 / 1000000000000) (4802356403 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 0) <| besselDerivativeNearFromState (514996440117257 / 4000000000000) 0 (IntervalRat.scale (223 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-46800545593 / 1000000000000) (-46800545592 / 1000000000000), orderedInterval (-52300314975 / 1000000000000) (-52300314974 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 0) <| besselDerivativeNearFromState (882455177974061 / 4000000000000) 0 (IntervalRat.scale (223 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (53530552742 / 1000000000000) (53530552765 / 1000000000000), orderedInterval (4367318917 / 1000000000000) (4367318940 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 0) <| besselDerivativeNearFromState (650012490059399 / 4000000000000) 0 (IntervalRat.scale (223 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-4694036363 / 1000000000000) (-4694036350 / 1000000000000), orderedInterval (62428938011 / 1000000000000) (62428938024 / 1000000000000)))) (orderedInterval (-1764542024 / 1000000000000) (-1764542016 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate234_chunkChecks0_1 :
    compactCertificate234.chunkChecks (0 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 0) <| besselDerivativeNearFromState (997286317964777 / 4000000000000) 0 (IntervalRat.scale (223 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-47470061618 / 1000000000000) (-47470055031 / 1000000000000), orderedInterval (17415640699 / 1000000000000) (17415647286 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 0) <| besselDerivativeNearFromState (575783524136033 / 4000000000000) 0 (IntervalRat.scale (223 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (14327751391 / 1000000000000) (14327751392 / 1000000000000), orderedInterval (64891533364 / 1000000000000) (64891533365 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 0) <| besselDerivativeNearFromState (1021737967614997 / 4000000000000) 0 (IntervalRat.scale (223 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-49119914806 / 1000000000000) (-49119913766 / 1000000000000), orderedInterval (9014168138 / 1000000000000) (9014169177 / 1000000000000)))) (orderedInterval (2513738774 / 1000000000000) (2513740137 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 0) <| besselDerivativeNearFromState (954640145709193 / 4000000000000) 0 (IntervalRat.scale (223 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (32630760951 / 1000000000000) (32630760952 / 1000000000000), orderedInterval (39965498591 / 1000000000000) (39965498592 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 0) <| besselDerivativeNearFromState (681276253316569 / 4000000000000) 0 (IntervalRat.scale (223 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (60747060884 / 1000000000000) (60747060894 / 1000000000000), orderedInterval (6719915366 / 1000000000000) (6719915376 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 0) <| besselDerivativeNearFromState (772494660175551 / 4000000000000) 0 (IntervalRat.scale (223 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-43895773509 / 1000000000000) (-43895672562 / 1000000000000), orderedInterval (37121691181 / 1000000000000) (37121792128 / 1000000000000)))) (orderedInterval (5377467625 / 1000000000000) (5377468151 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 0) <| besselDerivativeNearFromState (644025511037519 / 4000000000000) 0 (IntervalRat.scale (223 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-62880682669 / 1000000000000) (-62880682618 / 1000000000000), orderedInterval (131002038 / 1000000000000) (131002089 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 0) <| besselDerivativeNearFromState (569016070335899 / 4000000000000) 0 (IntervalRat.scale (223 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-66588488386 / 1000000000000) (-66588488211 / 1000000000000), orderedInterval (6651083053 / 1000000000000) (6651083228 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 0) <| besselDerivativeNearFromState (164923035650001 / 800000000000) 0 (IntervalRat.scale (223 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-21973847349 / 1000000000000) (-21973846407 / 1000000000000), orderedInterval (51094826617 / 1000000000000) (51094827559 / 1000000000000)))) (orderedInterval (2521895239 / 1000000000000) (2521895286 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate234_chunkChecks0_2 :
    compactCertificate234.chunkChecks (0 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 0) <| besselDerivativeNearFromState (456185796031747 / 4000000000000) 0 (IntervalRat.scale (223 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (73727436259 / 1000000000000) (73727436609 / 1000000000000), orderedInterval (-12419667333 / 1000000000000) (-12419666983 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 0) <| besselDerivativeNearFromState (386713751415467 / 4000000000000) 0 (IntervalRat.scale (223 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-5932299008 / 1000000000000) (-5932299006 / 1000000000000), orderedInterval (-80900246780 / 1000000000000) (-80900246778 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 0) <| besselDerivativeNearFromState (241987509940601 / 4000000000000) 0 (IntervalRat.scale (223 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-102562005929 / 1000000000000) (-102562005897 / 1000000000000), orderedInterval (2812280605 / 1000000000000) (2812280638 / 1000000000000)))) (orderedInterval (-14791625931 / 1000000000000) (-14791625845 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 0) <| besselDerivativeNearFromState (130141687660167 / 4000000000000) 0 (IntervalRat.scale (223 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (132314836072 / 1000000000000) (132314837748 / 1000000000000), orderedInterval (-47397406668 / 1000000000000) (-47397404993 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 0) <| besselDerivativeNearFromState (353359998161501 / 4000000000000) 0 (IntervalRat.scale (223 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (77806914490 / 1000000000000) (77806914491 / 1000000000000), orderedInterval (33507797324 / 1000000000000) (33507797325 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 0) <| besselDerivativeNearFromState (482482867814077 / 4000000000000) 0 (IntervalRat.scale (223 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (65296884888 / 1000000000000) (65296894687 / 1000000000000), orderedInterval (-32116431529 / 1000000000000) (-32116421730 / 1000000000000)))) (orderedInterval (-9212683922 / 1000000000000) (-9212683126 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 0) <| besselDerivativeNearFromState (204012490059399 / 4000000000000) 0 (IntervalRat.scale (223 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (111579295965 / 1000000000000) (111579295975 / 1000000000000), orderedInterval (4513461919 / 1000000000000) (4513461930 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 0) <| besselDerivativeNearFromState (829299445656679 / 4000000000000) 0 (IntervalRat.scale (223 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (38357405060 / 1000000000000) (38357405061 / 1000000000000), orderedInterval (39899352791 / 1000000000000) (39899352792 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 0) <| besselDerivativeNearFromState (553933596592361 / 4000000000000) 0 (IntervalRat.scale (223 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (58397332869 / 1000000000000) (58397332870 / 1000000000000), orderedInterval (34239420777 / 1000000000000) (34239420778 / 1000000000000)))) (orderedInterval (-13406613107 / 1000000000000) (-13406613075 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate234_chunkChecks0 :
    compactCertificate234.chunkChecks (0 : Fin 5) 0 9 = true :=
  compactCertificate234.chunkChecks_nine_of_three (0 : Fin 5) compactCertificate234_chunkChecks0_0
    compactCertificate234_chunkChecks0_1 compactCertificate234_chunkChecks0_2

theorem compactCertificate234_chunkChecks1_0 :
    compactCertificate234.chunkChecks (1 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 1) <| besselDerivativeNearFromState (223 / 2) 1 (IntervalRat.scale (223 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-54887335618 / 1000000000000) (-54887247610 / 1000000000000), orderedInterval (52178499284 / 1000000000000) (52178587292 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 1) <| besselDerivativeNearFromState (328521581381923 / 4000000000000) 1 (IntervalRat.scale (223 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (83061385748 / 1000000000000) (83061385749 / 1000000000000), orderedInterval (28683798692 / 1000000000000) (28683798693 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 1) <| besselDerivativeNearFromState (106237129517059 / 800000000000) 1 (IntervalRat.scale (223 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (69099985638 / 1000000000000) (69099985742 / 1000000000000), orderedInterval (-4631826019 / 1000000000000) (-4631825915 / 1000000000000)))) (orderedInterval (20554891215 / 1000000000000) (20554926115 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 1) <| besselDerivativeNearFromState (95861778102761 / 4000000000000) 1 (IntervalRat.scale (223 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-61522324603 / 1000000000000) (-61522322522 / 1000000000000), orderedInterval (152224045713 / 1000000000000) (152224047794 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 1) <| besselDerivativeNearFromState (257498220058517 / 4000000000000) 1 (IntervalRat.scale (223 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (72397119624 / 1000000000000) (72397228528 / 1000000000000), orderedInterval (-68738118473 / 1000000000000) (-68738009569 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 1) <| besselDerivativeNearFromState (699157757996289 / 4000000000000) 1 (IntervalRat.scale (223 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-20981025550 / 1000000000000) (-20981024939 / 1000000000000), orderedInterval (56646388926 / 1000000000000) (56646389537 / 1000000000000)))) (orderedInterval (-8116731223 / 1000000000000) (-8116728839 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 1) <| besselDerivativeNearFromState (514996440117257 / 4000000000000) 1 (IntervalRat.scale (223 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-46800545593 / 1000000000000) (-46800545592 / 1000000000000), orderedInterval (-52300314975 / 1000000000000) (-52300314974 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 1) <| besselDerivativeNearFromState (882455177974061 / 4000000000000) 1 (IntervalRat.scale (223 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (53530552742 / 1000000000000) (53530552765 / 1000000000000), orderedInterval (4367318917 / 1000000000000) (4367318940 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 1) <| besselDerivativeNearFromState (650012490059399 / 4000000000000) 1 (IntervalRat.scale (223 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-4694036363 / 1000000000000) (-4694036350 / 1000000000000), orderedInterval (62428938011 / 1000000000000) (62428938024 / 1000000000000)))) (orderedInterval (1932414721 / 1000000000000) (1932414735 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate234_chunkChecks1_1 :
    compactCertificate234.chunkChecks (1 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 1) <| besselDerivativeNearFromState (997286317964777 / 4000000000000) 1 (IntervalRat.scale (223 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-47470061618 / 1000000000000) (-47470055031 / 1000000000000), orderedInterval (17415640699 / 1000000000000) (17415647286 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 1) <| besselDerivativeNearFromState (575783524136033 / 4000000000000) 1 (IntervalRat.scale (223 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (14327751391 / 1000000000000) (14327751392 / 1000000000000), orderedInterval (64891533364 / 1000000000000) (64891533365 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 1) <| besselDerivativeNearFromState (1021737967614997 / 4000000000000) 1 (IntervalRat.scale (223 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-49119914806 / 1000000000000) (-49119913766 / 1000000000000), orderedInterval (9014168138 / 1000000000000) (9014169177 / 1000000000000)))) (orderedInterval (2222973015 / 1000000000000) (2222976063 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 1) <| besselDerivativeNearFromState (954640145709193 / 4000000000000) 1 (IntervalRat.scale (223 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (32630760951 / 1000000000000) (32630760952 / 1000000000000), orderedInterval (39965498591 / 1000000000000) (39965498592 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 1) <| besselDerivativeNearFromState (681276253316569 / 4000000000000) 1 (IntervalRat.scale (223 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (60747060884 / 1000000000000) (60747060894 / 1000000000000), orderedInterval (6719915366 / 1000000000000) (6719915376 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 1) <| besselDerivativeNearFromState (772494660175551 / 4000000000000) 1 (IntervalRat.scale (223 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-43895773509 / 1000000000000) (-43895672562 / 1000000000000), orderedInterval (37121691181 / 1000000000000) (37121792128 / 1000000000000)))) (orderedInterval (-899041317 / 1000000000000) (-899040408 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 1) <| besselDerivativeNearFromState (644025511037519 / 4000000000000) 1 (IntervalRat.scale (223 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-62880682669 / 1000000000000) (-62880682618 / 1000000000000), orderedInterval (131002038 / 1000000000000) (131002089 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 1) <| besselDerivativeNearFromState (569016070335899 / 4000000000000) 1 (IntervalRat.scale (223 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-66588488386 / 1000000000000) (-66588488211 / 1000000000000), orderedInterval (6651083053 / 1000000000000) (6651083228 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 1) <| besselDerivativeNearFromState (164923035650001 / 800000000000) 1 (IntervalRat.scale (223 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-21973847349 / 1000000000000) (-21973846407 / 1000000000000), orderedInterval (51094826617 / 1000000000000) (51094827559 / 1000000000000)))) (orderedInterval (1935384564 / 1000000000000) (1935384639 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate234_chunkChecks1_2 :
    compactCertificate234.chunkChecks (1 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 1) <| besselDerivativeNearFromState (456185796031747 / 4000000000000) 1 (IntervalRat.scale (223 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (73727436259 / 1000000000000) (73727436609 / 1000000000000), orderedInterval (-12419667333 / 1000000000000) (-12419666983 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 1) <| besselDerivativeNearFromState (386713751415467 / 4000000000000) 1 (IntervalRat.scale (223 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-5932299008 / 1000000000000) (-5932299006 / 1000000000000), orderedInterval (-80900246780 / 1000000000000) (-80900246778 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 1) <| besselDerivativeNearFromState (241987509940601 / 4000000000000) 1 (IntervalRat.scale (223 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-102562005929 / 1000000000000) (-102562005897 / 1000000000000), orderedInterval (2812280605 / 1000000000000) (2812280638 / 1000000000000)))) (orderedInterval (6051114039 / 1000000000000) (6051114124 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 1) <| besselDerivativeNearFromState (130141687660167 / 4000000000000) 1 (IntervalRat.scale (223 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (132314836072 / 1000000000000) (132314837748 / 1000000000000), orderedInterval (-47397406668 / 1000000000000) (-47397404993 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 1) <| besselDerivativeNearFromState (353359998161501 / 4000000000000) 1 (IntervalRat.scale (223 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (77806914490 / 1000000000000) (77806914491 / 1000000000000), orderedInterval (33507797324 / 1000000000000) (33507797325 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 1) <| besselDerivativeNearFromState (482482867814077 / 4000000000000) 1 (IntervalRat.scale (223 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (65296884888 / 1000000000000) (65296894687 / 1000000000000), orderedInterval (-32116431529 / 1000000000000) (-32116421730 / 1000000000000)))) (orderedInterval (2315801084 / 1000000000000) (2315801918 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 1) <| besselDerivativeNearFromState (204012490059399 / 4000000000000) 1 (IntervalRat.scale (223 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (111579295965 / 1000000000000) (111579295975 / 1000000000000), orderedInterval (4513461919 / 1000000000000) (4513461930 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 1) <| besselDerivativeNearFromState (829299445656679 / 4000000000000) 1 (IntervalRat.scale (223 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (38357405060 / 1000000000000) (38357405061 / 1000000000000), orderedInterval (39899352791 / 1000000000000) (39899352792 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 1) <| besselDerivativeNearFromState (553933596592361 / 4000000000000) 1 (IntervalRat.scale (223 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (58397332869 / 1000000000000) (58397332870 / 1000000000000), orderedInterval (34239420777 / 1000000000000) (34239420778 / 1000000000000)))) (orderedInterval (-14005618843 / 1000000000000) (-14005618798 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate234_chunkChecks1 :
    compactCertificate234.chunkChecks (1 : Fin 5) 0 9 = true :=
  compactCertificate234.chunkChecks_nine_of_three (1 : Fin 5) compactCertificate234_chunkChecks1_0
    compactCertificate234_chunkChecks1_1 compactCertificate234_chunkChecks1_2

theorem compactCertificate234_chunkChecks2_0 :
    compactCertificate234.chunkChecks (2 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 2) <| besselDerivativeNearFromState (223 / 2) 2 (IntervalRat.scale (223 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-54887335618 / 1000000000000) (-54887247610 / 1000000000000), orderedInterval (52178499284 / 1000000000000) (52178587292 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 2) <| besselDerivativeNearFromState (328521581381923 / 4000000000000) 2 (IntervalRat.scale (223 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (83061385748 / 1000000000000) (83061385749 / 1000000000000), orderedInterval (28683798692 / 1000000000000) (28683798693 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 2) <| besselDerivativeNearFromState (106237129517059 / 800000000000) 2 (IntervalRat.scale (223 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (69099985638 / 1000000000000) (69099985742 / 1000000000000), orderedInterval (-4631826019 / 1000000000000) (-4631825915 / 1000000000000)))) (orderedInterval (15399356068 / 1000000000000) (15399391283 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 2) <| besselDerivativeNearFromState (95861778102761 / 4000000000000) 2 (IntervalRat.scale (223 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-61522324603 / 1000000000000) (-61522322522 / 1000000000000), orderedInterval (152224045713 / 1000000000000) (152224047794 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 2) <| besselDerivativeNearFromState (257498220058517 / 4000000000000) 2 (IntervalRat.scale (223 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (72397119624 / 1000000000000) (72397228528 / 1000000000000), orderedInterval (-68738118473 / 1000000000000) (-68738009569 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 2) <| besselDerivativeNearFromState (699157757996289 / 4000000000000) 2 (IntervalRat.scale (223 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-20981025550 / 1000000000000) (-20981024939 / 1000000000000), orderedInterval (56646388926 / 1000000000000) (56646389537 / 1000000000000)))) (orderedInterval (-4504491489 / 1000000000000) (-4504490012 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 2) <| besselDerivativeNearFromState (514996440117257 / 4000000000000) 2 (IntervalRat.scale (223 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-46800545593 / 1000000000000) (-46800545592 / 1000000000000), orderedInterval (-52300314975 / 1000000000000) (-52300314974 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 2) <| besselDerivativeNearFromState (882455177974061 / 4000000000000) 2 (IntervalRat.scale (223 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (53530552742 / 1000000000000) (53530552765 / 1000000000000), orderedInterval (4367318917 / 1000000000000) (4367318940 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 2) <| besselDerivativeNearFromState (650012490059399 / 4000000000000) 2 (IntervalRat.scale (223 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-4694036363 / 1000000000000) (-4694036350 / 1000000000000), orderedInterval (62428938011 / 1000000000000) (62428938024 / 1000000000000)))) (orderedInterval (6687439792 / 1000000000000) (6687439816 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate234_chunkChecks2_1 :
    compactCertificate234.chunkChecks (2 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 2) <| besselDerivativeNearFromState (997286317964777 / 4000000000000) 2 (IntervalRat.scale (223 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-47470061618 / 1000000000000) (-47470055031 / 1000000000000), orderedInterval (17415640699 / 1000000000000) (17415647286 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 2) <| besselDerivativeNearFromState (575783524136033 / 4000000000000) 2 (IntervalRat.scale (223 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (14327751391 / 1000000000000) (14327751392 / 1000000000000), orderedInterval (64891533364 / 1000000000000) (64891533365 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 2) <| besselDerivativeNearFromState (1021737967614997 / 4000000000000) 2 (IntervalRat.scale (223 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-49119914806 / 1000000000000) (-49119913766 / 1000000000000), orderedInterval (9014168138 / 1000000000000) (9014169177 / 1000000000000)))) (orderedInterval (-7317060580 / 1000000000000) (-7317053728 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 2) <| besselDerivativeNearFromState (954640145709193 / 4000000000000) 2 (IntervalRat.scale (223 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (32630760951 / 1000000000000) (32630760952 / 1000000000000), orderedInterval (39965498591 / 1000000000000) (39965498592 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 2) <| besselDerivativeNearFromState (681276253316569 / 4000000000000) 2 (IntervalRat.scale (223 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (60747060884 / 1000000000000) (60747060894 / 1000000000000), orderedInterval (6719915366 / 1000000000000) (6719915376 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 2) <| besselDerivativeNearFromState (772494660175551 / 4000000000000) 2 (IntervalRat.scale (223 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-43895773509 / 1000000000000) (-43895672562 / 1000000000000), orderedInterval (37121691181 / 1000000000000) (37121792128 / 1000000000000)))) (orderedInterval (-11363078814 / 1000000000000) (-11363077235 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 2) <| besselDerivativeNearFromState (644025511037519 / 4000000000000) 2 (IntervalRat.scale (223 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-62880682669 / 1000000000000) (-62880682618 / 1000000000000), orderedInterval (131002038 / 1000000000000) (131002089 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 2) <| besselDerivativeNearFromState (569016070335899 / 4000000000000) 2 (IntervalRat.scale (223 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-66588488386 / 1000000000000) (-66588488211 / 1000000000000), orderedInterval (6651083053 / 1000000000000) (6651083228 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 2) <| besselDerivativeNearFromState (164923035650001 / 800000000000) 2 (IntervalRat.scale (223 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-21973847349 / 1000000000000) (-21973846407 / 1000000000000), orderedInterval (51094826617 / 1000000000000) (51094827559 / 1000000000000)))) (orderedInterval (-2782631599 / 1000000000000) (-2782631475 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate234_chunkChecks2_2 :
    compactCertificate234.chunkChecks (2 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 2) <| besselDerivativeNearFromState (456185796031747 / 4000000000000) 2 (IntervalRat.scale (223 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (73727436259 / 1000000000000) (73727436609 / 1000000000000), orderedInterval (-12419667333 / 1000000000000) (-12419666983 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 2) <| besselDerivativeNearFromState (386713751415467 / 4000000000000) 2 (IntervalRat.scale (223 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-5932299008 / 1000000000000) (-5932299006 / 1000000000000), orderedInterval (-80900246780 / 1000000000000) (-80900246778 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 2) <| besselDerivativeNearFromState (241987509940601 / 4000000000000) 2 (IntervalRat.scale (223 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-102562005929 / 1000000000000) (-102562005897 / 1000000000000), orderedInterval (2812280605 / 1000000000000) (2812280638 / 1000000000000)))) (orderedInterval (13009289318 / 1000000000000) (13009289403 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 2) <| besselDerivativeNearFromState (130141687660167 / 4000000000000) 2 (IntervalRat.scale (223 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (132314836072 / 1000000000000) (132314837748 / 1000000000000), orderedInterval (-47397406668 / 1000000000000) (-47397404993 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 2) <| besselDerivativeNearFromState (353359998161501 / 4000000000000) 2 (IntervalRat.scale (223 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (77806914490 / 1000000000000) (77806914491 / 1000000000000), orderedInterval (33507797324 / 1000000000000) (33507797325 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 2) <| besselDerivativeNearFromState (482482867814077 / 4000000000000) 2 (IntervalRat.scale (223 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (65296884888 / 1000000000000) (65296894687 / 1000000000000), orderedInterval (-32116431529 / 1000000000000) (-32116421730 / 1000000000000)))) (orderedInterval (7151771187 / 1000000000000) (7151772089 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 2) <| besselDerivativeNearFromState (204012490059399 / 4000000000000) 2 (IntervalRat.scale (223 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (111579295965 / 1000000000000) (111579295975 / 1000000000000), orderedInterval (4513461919 / 1000000000000) (4513461930 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 2) <| besselDerivativeNearFromState (829299445656679 / 4000000000000) 2 (IntervalRat.scale (223 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (38357405060 / 1000000000000) (38357405061 / 1000000000000), orderedInterval (39899352791 / 1000000000000) (39899352792 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 2) <| besselDerivativeNearFromState (553933596592361 / 4000000000000) 2 (IntervalRat.scale (223 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (58397332869 / 1000000000000) (58397332870 / 1000000000000), orderedInterval (34239420777 / 1000000000000) (34239420778 / 1000000000000)))) (orderedInterval (27682003617 / 1000000000000) (27682003682 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate234_chunkChecks2 :
    compactCertificate234.chunkChecks (2 : Fin 5) 0 9 = true :=
  compactCertificate234.chunkChecks_nine_of_three (2 : Fin 5) compactCertificate234_chunkChecks2_0
    compactCertificate234_chunkChecks2_1 compactCertificate234_chunkChecks2_2

theorem compactCertificate234_chunkChecks3_0 :
    compactCertificate234.chunkChecks (3 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 3) <| besselDerivativeNearFromState (223 / 2) 3 (IntervalRat.scale (223 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-54887335618 / 1000000000000) (-54887247610 / 1000000000000), orderedInterval (52178499284 / 1000000000000) (52178587292 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 3) <| besselDerivativeNearFromState (328521581381923 / 4000000000000) 3 (IntervalRat.scale (223 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (83061385748 / 1000000000000) (83061385749 / 1000000000000), orderedInterval (28683798692 / 1000000000000) (28683798693 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 3) <| besselDerivativeNearFromState (106237129517059 / 800000000000) 3 (IntervalRat.scale (223 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (69099985638 / 1000000000000) (69099985742 / 1000000000000), orderedInterval (-4631826019 / 1000000000000) (-4631825915 / 1000000000000)))) (orderedInterval (-20465860009 / 1000000000000) (-20465824796 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 3) <| besselDerivativeNearFromState (95861778102761 / 4000000000000) 3 (IntervalRat.scale (223 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-61522324603 / 1000000000000) (-61522322522 / 1000000000000), orderedInterval (152224045713 / 1000000000000) (152224047794 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 3) <| besselDerivativeNearFromState (257498220058517 / 4000000000000) 3 (IntervalRat.scale (223 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (72397119624 / 1000000000000) (72397228528 / 1000000000000), orderedInterval (-68738118473 / 1000000000000) (-68738009569 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 3) <| besselDerivativeNearFromState (699157757996289 / 4000000000000) 3 (IntervalRat.scale (223 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-20981025550 / 1000000000000) (-20981024939 / 1000000000000), orderedInterval (56646388926 / 1000000000000) (56646389537 / 1000000000000)))) (orderedInterval (16052278760 / 1000000000000) (16052279737 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 3) <| besselDerivativeNearFromState (514996440117257 / 4000000000000) 3 (IntervalRat.scale (223 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-46800545593 / 1000000000000) (-46800545592 / 1000000000000), orderedInterval (-52300314975 / 1000000000000) (-52300314974 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 3) <| besselDerivativeNearFromState (882455177974061 / 4000000000000) 3 (IntervalRat.scale (223 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (53530552742 / 1000000000000) (53530552765 / 1000000000000), orderedInterval (4367318917 / 1000000000000) (4367318940 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 3) <| besselDerivativeNearFromState (650012490059399 / 4000000000000) 3 (IntervalRat.scale (223 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-4694036363 / 1000000000000) (-4694036350 / 1000000000000), orderedInterval (62428938011 / 1000000000000) (62428938024 / 1000000000000)))) (orderedInterval (-3687163289 / 1000000000000) (-3687163246 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate234_chunkChecks3_1 :
    compactCertificate234.chunkChecks (3 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 3) <| besselDerivativeNearFromState (997286317964777 / 4000000000000) 3 (IntervalRat.scale (223 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-47470061618 / 1000000000000) (-47470055031 / 1000000000000), orderedInterval (17415640699 / 1000000000000) (17415647286 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 3) <| besselDerivativeNearFromState (575783524136033 / 4000000000000) 3 (IntervalRat.scale (223 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (14327751391 / 1000000000000) (14327751392 / 1000000000000), orderedInterval (64891533364 / 1000000000000) (64891533365 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 3) <| besselDerivativeNearFromState (1021737967614997 / 4000000000000) 3 (IntervalRat.scale (223 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-49119914806 / 1000000000000) (-49119913766 / 1000000000000), orderedInterval (9014168138 / 1000000000000) (9014169177 / 1000000000000)))) (orderedInterval (8912376254 / 1000000000000) (8912391606 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 3) <| besselDerivativeNearFromState (954640145709193 / 4000000000000) 3 (IntervalRat.scale (223 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (32630760951 / 1000000000000) (32630760952 / 1000000000000), orderedInterval (39965498591 / 1000000000000) (39965498592 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 3) <| besselDerivativeNearFromState (681276253316569 / 4000000000000) 3 (IntervalRat.scale (223 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (60747060884 / 1000000000000) (60747060894 / 1000000000000), orderedInterval (6719915366 / 1000000000000) (6719915376 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 3) <| besselDerivativeNearFromState (772494660175551 / 4000000000000) 3 (IntervalRat.scale (223 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-43895773509 / 1000000000000) (-43895672562 / 1000000000000), orderedInterval (37121691181 / 1000000000000) (37121792128 / 1000000000000)))) (orderedInterval (5888473158 / 1000000000000) (5888475891 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 3) <| besselDerivativeNearFromState (644025511037519 / 4000000000000) 3 (IntervalRat.scale (223 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-62880682669 / 1000000000000) (-62880682618 / 1000000000000), orderedInterval (131002038 / 1000000000000) (131002089 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 3) <| besselDerivativeNearFromState (569016070335899 / 4000000000000) 3 (IntervalRat.scale (223 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-66588488386 / 1000000000000) (-66588488211 / 1000000000000), orderedInterval (6651083053 / 1000000000000) (6651083228 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 3) <| besselDerivativeNearFromState (164923035650001 / 800000000000) 3 (IntervalRat.scale (223 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-21973847349 / 1000000000000) (-21973846407 / 1000000000000), orderedInterval (51094826617 / 1000000000000) (51094827559 / 1000000000000)))) (orderedInterval (-7457644424 / 1000000000000) (-7457644212 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate234_chunkChecks3_2 :
    compactCertificate234.chunkChecks (3 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 3) <| besselDerivativeNearFromState (456185796031747 / 4000000000000) 3 (IntervalRat.scale (223 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (73727436259 / 1000000000000) (73727436609 / 1000000000000), orderedInterval (-12419667333 / 1000000000000) (-12419666983 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 3) <| besselDerivativeNearFromState (386713751415467 / 4000000000000) 3 (IntervalRat.scale (223 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-5932299008 / 1000000000000) (-5932299006 / 1000000000000), orderedInterval (-80900246780 / 1000000000000) (-80900246778 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 3) <| besselDerivativeNearFromState (241987509940601 / 4000000000000) 3 (IntervalRat.scale (223 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-102562005929 / 1000000000000) (-102562005897 / 1000000000000), orderedInterval (2812280605 / 1000000000000) (2812280638 / 1000000000000)))) (orderedInterval (-5240713404 / 1000000000000) (-5240713319 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 3) <| besselDerivativeNearFromState (130141687660167 / 4000000000000) 3 (IntervalRat.scale (223 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (132314836072 / 1000000000000) (132314837748 / 1000000000000), orderedInterval (-47397406668 / 1000000000000) (-47397404993 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 3) <| besselDerivativeNearFromState (353359998161501 / 4000000000000) 3 (IntervalRat.scale (223 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (77806914490 / 1000000000000) (77806914491 / 1000000000000), orderedInterval (33507797324 / 1000000000000) (33507797325 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 3) <| besselDerivativeNearFromState (482482867814077 / 4000000000000) 3 (IntervalRat.scale (223 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (65296884888 / 1000000000000) (65296894687 / 1000000000000), orderedInterval (-32116431529 / 1000000000000) (-32116421730 / 1000000000000)))) (orderedInterval (-2823777362 / 1000000000000) (-2823776390 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 3) <| besselDerivativeNearFromState (204012490059399 / 4000000000000) 3 (IntervalRat.scale (223 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (111579295965 / 1000000000000) (111579295975 / 1000000000000), orderedInterval (4513461919 / 1000000000000) (4513461930 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 3) <| besselDerivativeNearFromState (829299445656679 / 4000000000000) 3 (IntervalRat.scale (223 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (38357405060 / 1000000000000) (38357405061 / 1000000000000), orderedInterval (39899352791 / 1000000000000) (39899352792 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 3) <| besselDerivativeNearFromState (553933596592361 / 4000000000000) 3 (IntervalRat.scale (223 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (58397332869 / 1000000000000) (58397332870 / 1000000000000), orderedInterval (34239420777 / 1000000000000) (34239420778 / 1000000000000)))) (orderedInterval (32935990308 / 1000000000000) (32935990408 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate234_chunkChecks3 :
    compactCertificate234.chunkChecks (3 : Fin 5) 0 9 = true :=
  compactCertificate234.chunkChecks_nine_of_three (3 : Fin 5) compactCertificate234_chunkChecks3_0
    compactCertificate234_chunkChecks3_1 compactCertificate234_chunkChecks3_2

theorem compactCertificate234_chunkChecks4_0 :
    compactCertificate234.chunkChecks (4 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 4) <| besselDerivativeNearFromState (223 / 2) 4 (IntervalRat.scale (223 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-54887335618 / 1000000000000) (-54887247610 / 1000000000000), orderedInterval (52178499284 / 1000000000000) (52178587292 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 4) <| besselDerivativeNearFromState (328521581381923 / 4000000000000) 4 (IntervalRat.scale (223 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (83061385748 / 1000000000000) (83061385749 / 1000000000000), orderedInterval (28683798692 / 1000000000000) (28683798693 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 4) <| besselDerivativeNearFromState (106237129517059 / 800000000000) 4 (IntervalRat.scale (223 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (69099985638 / 1000000000000) (69099985742 / 1000000000000), orderedInterval (-4631826019 / 1000000000000) (-4631825915 / 1000000000000)))) (orderedInterval (-13000522016 / 1000000000000) (-13000486489 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 4) <| besselDerivativeNearFromState (95861778102761 / 4000000000000) 4 (IntervalRat.scale (223 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-61522324603 / 1000000000000) (-61522322522 / 1000000000000), orderedInterval (152224045713 / 1000000000000) (152224047794 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 4) <| besselDerivativeNearFromState (257498220058517 / 4000000000000) 4 (IntervalRat.scale (223 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (72397119624 / 1000000000000) (72397228528 / 1000000000000), orderedInterval (-68738118473 / 1000000000000) (-68738009569 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 4) <| besselDerivativeNearFromState (699157757996289 / 4000000000000) 4 (IntervalRat.scale (223 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-20981025550 / 1000000000000) (-20981024939 / 1000000000000), orderedInterval (56646388926 / 1000000000000) (56646389537 / 1000000000000)))) (orderedInterval (9014133230 / 1000000000000) (9014134000 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 4) <| besselDerivativeNearFromState (514996440117257 / 4000000000000) 4 (IntervalRat.scale (223 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-46800545593 / 1000000000000) (-46800545592 / 1000000000000), orderedInterval (-52300314975 / 1000000000000) (-52300314974 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 4) <| besselDerivativeNearFromState (882455177974061 / 4000000000000) 4 (IntervalRat.scale (223 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (53530552742 / 1000000000000) (53530552765 / 1000000000000), orderedInterval (4367318917 / 1000000000000) (4367318940 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 4) <| besselDerivativeNearFromState (650012490059399 / 4000000000000) 4 (IntervalRat.scale (223 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-4694036363 / 1000000000000) (-4694036350 / 1000000000000), orderedInterval (62428938011 / 1000000000000) (62428938024 / 1000000000000)))) (orderedInterval (-25750008690 / 1000000000000) (-25750008612 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate234_chunkChecks4_1 :
    compactCertificate234.chunkChecks (4 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 4) <| besselDerivativeNearFromState (997286317964777 / 4000000000000) 4 (IntervalRat.scale (223 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-47470061618 / 1000000000000) (-47470055031 / 1000000000000), orderedInterval (17415640699 / 1000000000000) (17415647286 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 4) <| besselDerivativeNearFromState (575783524136033 / 4000000000000) 4 (IntervalRat.scale (223 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (14327751391 / 1000000000000) (14327751392 / 1000000000000), orderedInterval (64891533364 / 1000000000000) (64891533365 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 4) <| besselDerivativeNearFromState (1021737967614997 / 4000000000000) 4 (IntervalRat.scale (223 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-49119914806 / 1000000000000) (-49119913766 / 1000000000000), orderedInterval (9014168138 / 1000000000000) (9014169177 / 1000000000000)))) (orderedInterval (21332336814 / 1000000000000) (21332371368 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 4) <| besselDerivativeNearFromState (954640145709193 / 4000000000000) 4 (IntervalRat.scale (223 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (32630760951 / 1000000000000) (32630760952 / 1000000000000), orderedInterval (39965498591 / 1000000000000) (39965498592 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 4) <| besselDerivativeNearFromState (681276253316569 / 4000000000000) 4 (IntervalRat.scale (223 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (60747060884 / 1000000000000) (60747060894 / 1000000000000), orderedInterval (6719915366 / 1000000000000) (6719915376 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 4) <| besselDerivativeNearFromState (772494660175551 / 4000000000000) 4 (IntervalRat.scale (223 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-43895773509 / 1000000000000) (-43895672562 / 1000000000000), orderedInterval (37121691181 / 1000000000000) (37121792128 / 1000000000000)))) (orderedInterval (20802744678 / 1000000000000) (20802749435 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 4) <| besselDerivativeNearFromState (644025511037519 / 4000000000000) 4 (IntervalRat.scale (223 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-62880682669 / 1000000000000) (-62880682618 / 1000000000000), orderedInterval (131002038 / 1000000000000) (131002089 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 4) <| besselDerivativeNearFromState (569016070335899 / 4000000000000) 4 (IntervalRat.scale (223 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-66588488386 / 1000000000000) (-66588488211 / 1000000000000), orderedInterval (6651083053 / 1000000000000) (6651083228 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 4) <| besselDerivativeNearFromState (164923035650001 / 800000000000) 4 (IntervalRat.scale (223 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-21973847349 / 1000000000000) (-21973846407 / 1000000000000), orderedInterval (51094826617 / 1000000000000) (51094827559 / 1000000000000)))) (orderedInterval (497890533 / 1000000000000) (497890904 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate234_chunkChecks4_2 :
    compactCertificate234.chunkChecks (4 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 4) <| besselDerivativeNearFromState (456185796031747 / 4000000000000) 4 (IntervalRat.scale (223 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (73727436259 / 1000000000000) (73727436609 / 1000000000000), orderedInterval (-12419667333 / 1000000000000) (-12419666983 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 4) <| besselDerivativeNearFromState (386713751415467 / 4000000000000) 4 (IntervalRat.scale (223 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-5932299008 / 1000000000000) (-5932299006 / 1000000000000), orderedInterval (-80900246780 / 1000000000000) (-80900246778 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 4) <| besselDerivativeNearFromState (241987509940601 / 4000000000000) 4 (IntervalRat.scale (223 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-102562005929 / 1000000000000) (-102562005897 / 1000000000000), orderedInterval (2812280605 / 1000000000000) (2812280638 / 1000000000000)))) (orderedInterval (-12907352830 / 1000000000000) (-12907352743 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 4) <| besselDerivativeNearFromState (130141687660167 / 4000000000000) 4 (IntervalRat.scale (223 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (132314836072 / 1000000000000) (132314837748 / 1000000000000), orderedInterval (-47397406668 / 1000000000000) (-47397404993 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 4) <| besselDerivativeNearFromState (353359998161501 / 4000000000000) 4 (IntervalRat.scale (223 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (77806914490 / 1000000000000) (77806914491 / 1000000000000), orderedInterval (33507797324 / 1000000000000) (33507797325 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 4) <| besselDerivativeNearFromState (482482867814077 / 4000000000000) 4 (IntervalRat.scale (223 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (65296884888 / 1000000000000) (65296894687 / 1000000000000), orderedInterval (-32116431529 / 1000000000000) (-32116421730 / 1000000000000)))) (orderedInterval (-7515803389 / 1000000000000) (-7515802330 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 4) <| besselDerivativeNearFromState (204012490059399 / 4000000000000) 4 (IntervalRat.scale (223 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (111579295965 / 1000000000000) (111579295975 / 1000000000000), orderedInterval (4513461919 / 1000000000000) (4513461930 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 4) <| besselDerivativeNearFromState (829299445656679 / 4000000000000) 4 (IntervalRat.scale (223 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (38357405060 / 1000000000000) (38357405061 / 1000000000000), orderedInterval (39899352791 / 1000000000000) (39899352792 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 4) <| besselDerivativeNearFromState (553933596592361 / 4000000000000) 4 (IntervalRat.scale (223 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (58397332869 / 1000000000000) (58397332870 / 1000000000000), orderedInterval (34239420777 / 1000000000000) (34239420778 / 1000000000000)))) (orderedInterval (-63955437470 / 1000000000000) (-63955437309 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate234_chunkChecks4 :
    compactCertificate234.chunkChecks (4 : Fin 5) 0 9 = true :=
  compactCertificate234.chunkChecks_nine_of_three (4 : Fin 5) compactCertificate234_chunkChecks4_0
    compactCertificate234_chunkChecks4_1 compactCertificate234_chunkChecks4_2

theorem compactCertificate234_chunks :
    ∀ r : Fin 5, ∀ b, compactCertificate234.chunkCheck r b = true :=
  compactCertificate234.chunkChecks_all (by
    intro r
    fin_cases r
    · exact compactCertificate234_chunkChecks0
    · exact compactCertificate234_chunkChecks1
    · exact compactCertificate234_chunkChecks2
    · exact compactCertificate234_chunkChecks3
    · exact compactCertificate234_chunkChecks4)

theorem compactCertificate234_coefficient0 :
    compactCertificate234.coefficientCheck (0 : Fin 5) = true := by
  norm_num [CompactCertificate.coefficientCheck, intervalFinSumHull,
    compactCertificate234, rationalIntervalSubset, orderedInterval, Fin.sum_univ_succ]

theorem compactCertificate234_coefficient1 :
    compactCertificate234.coefficientCheck (1 : Fin 5) = true := by
  norm_num [CompactCertificate.coefficientCheck, intervalFinSumHull,
    compactCertificate234, rationalIntervalSubset, orderedInterval, Fin.sum_univ_succ]

theorem compactCertificate234_coefficient2 :
    compactCertificate234.coefficientCheck (2 : Fin 5) = true := by
  norm_num [CompactCertificate.coefficientCheck, intervalFinSumHull,
    compactCertificate234, rationalIntervalSubset, orderedInterval, Fin.sum_univ_succ]

theorem compactCertificate234_coefficient3 :
    compactCertificate234.coefficientCheck (3 : Fin 5) = true := by
  norm_num [CompactCertificate.coefficientCheck, intervalFinSumHull,
    compactCertificate234, rationalIntervalSubset, orderedInterval, Fin.sum_univ_succ]

theorem compactCertificate234_coefficient4 :
    compactCertificate234.coefficientCheck (4 : Fin 5) = true := by
  norm_num [CompactCertificate.coefficientCheck, intervalFinSumHull,
    compactCertificate234, rationalIntervalSubset, orderedInterval, Fin.sum_univ_succ]

theorem compactCertificate234_coefficients : ∀ r : Fin 5,
    compactCertificate234.coefficientCheck r = true := by
  intro r
  fin_cases r
  · exact compactCertificate234_coefficient0
  · exact compactCertificate234_coefficient1
  · exact compactCertificate234_coefficient2
  · exact compactCertificate234_coefficient3
  · exact compactCertificate234_coefficient4

theorem compactCertificate234_lower : (1 : ℚ) ≤ compactCertificate234.output.lo := by
  norm_num [CompactCertificate.output, CompactCertificate.interval,
    CompactCertificate.coefficientTargetNat, compactCertificate234, dualConstant,
    intervalTaylorSum, intervalPow, intervalSub, intervalMaxAbs, widenInterval,
    rationalErrorInterval, orderedInterval, IntervalRat.add, IntervalRat.mul, IntervalRat.scale,
    IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4]

theorem compactCertificate234_proves {t : ℝ} (ht : t ∈ compactCertificate234.interval) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t :=
  compactCertificate234.proves compactCertificate234_states compactCertificate234_chunks
    compactCertificate234_coefficients compactCertificate234_lower ht

end Erdos232
