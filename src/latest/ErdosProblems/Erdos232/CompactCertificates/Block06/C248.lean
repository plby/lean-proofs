/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, OpenAI Codex
-/
import ErdosProblems.Erdos232.CompactBase

open LeanCert.Core
namespace Erdos232

def compactCertificate248 : CompactCertificate where
  left := 123
  right := 124
  center := 247 / 2
  grid := fun i =>
    match i.val with
    | 0 => 39
    | 1 => 29
    | 2 => 47
    | 3 => 8
    | 4 => 23
    | 5 => 62
    | 6 => 45
    | 7 => 78
    | 8 => 57
    | 9 => 88
    | 10 => 51
    | 11 => 90
    | 12 => 84
    | 13 => 60
    | 14 => 68
    | 15 => 57
    | 16 => 50
    | 17 => 73
    | 18 => 40
    | 19 => 34
    | 20 => 21
    | 21 => 11
    | 22 => 31
    | 23 => 43
    | 24 => 18
    | 25 => 73
    | _ => 49
  point := fun i =>
    match i.val with
    | 0 => 247 / 2
    | 1 => 363878164131547 / 4000000000000
    | 2 => 117670721931451 / 800000000000
    | 3 => 106178740768529 / 4000000000000
    | 4 => 285211032979613 / 4000000000000
    | 5 => 774403435986921 / 4000000000000
    | 6 => 570422065959473 / 4000000000000
    | 7 => 977427932554229 / 4000000000000
    | 8 => 719968991231711 / 4000000000000
    | 9 => 1104617580884753 / 4000000000000
    | 10 => 637751257675337 / 4000000000000
    | 11 => 1131700798210333 / 4000000000000
    | 12 => 1057381686054577 / 4000000000000
    | 13 => 754597464435841 / 4000000000000
    | 14 => 855633098938839 / 4000000000000
    | 15 => 713337673660391 / 4000000000000
    | 16 => 630255468040211 / 4000000000000
    | 17 => 182672600024889 / 800000000000
    | 18 => 505282025201083 / 4000000000000
    | 19 => 428333168608163 / 4000000000000
    | 20 => 268031008768289 / 4000000000000
    | 21 => 144147967946463 / 4000000000000
    | 22 => 391389773748389 / 4000000000000
    | 23 => 534409275112453 / 4000000000000
    | 24 => 225968991231711 / 4000000000000
    | 25 => 918551403933631 / 4000000000000
    | _ => 613549768422929 / 4000000000000
  state := fun i =>
    match i.val with
    | 0 => (orderedInterval (-70484621918 / 1000000000000) (-70484621383 / 1000000000000), orderedInterval (13948992013 / 1000000000000) (13948992549 / 1000000000000))
    | 1 => (orderedInterval (-50451732560 / 1000000000000) (-50451732559 / 1000000000000), orderedInterval (-66452128617 / 1000000000000) (-66452128616 / 1000000000000))
    | 2 => (orderedInterval (-14234721778 / 1000000000000) (-14234721777 / 1000000000000), orderedInterval (-64181973160 / 1000000000000) (-64181973159 / 1000000000000))
    | 3 => (orderedInterval (125863749513 / 1000000000000) (125863781510 / 1000000000000), orderedInterval (-92591336280 / 1000000000000) (-92591304283 / 1000000000000))
    | 4 => (orderedInterval (16007071218 / 1000000000000) (16007071324 / 1000000000000), orderedInterval (-93237875643 / 1000000000000) (-93237875538 / 1000000000000))
    | 5 => (orderedInterval (-21967470605 / 1000000000000) (-21967469740 / 1000000000000), orderedInterval (53026051391 / 1000000000000) (53026052257 / 1000000000000))
    | 6 => (orderedInterval (-60233279570 / 1000000000000) (-60233269291 / 1000000000000), orderedInterval (29127214878 / 1000000000000) (29127225158 / 1000000000000))
    | 7 => (orderedInterval (4975961857 / 1000000000000) (4975961859 / 1000000000000), orderedInterval (50788744755 / 1000000000000) (50788744757 / 1000000000000))
    | 8 => (orderedInterval (-58927857087 / 1000000000000) (-58927856710 / 1000000000000), orderedInterval (8190111225 / 1000000000000) (8190111602 / 1000000000000))
    | 9 => (orderedInterval (22137031301 / 1000000000000) (22137031302 / 1000000000000), orderedInterval (42565761576 / 1000000000000) (42565761577 / 1000000000000))
    | 10 => (orderedInterval (-76033134 / 1000000000000) (-76033130 / 1000000000000), orderedInterval (-63189294980 / 1000000000000) (-63189294975 / 1000000000000))
    | 11 => (orderedInterval (39043355567 / 1000000000000) (39043355568 / 1000000000000), orderedInterval (26870742977 / 1000000000000) (26870742978 / 1000000000000))
    | 12 => (orderedInterval (46358609571 / 1000000000000) (46358609572 / 1000000000000), orderedInterval (16010868324 / 1000000000000) (16010868325 / 1000000000000))
    | 13 => (orderedInterval (46862169538 / 1000000000000) (46862169539 / 1000000000000), orderedInterval (34205851644 / 1000000000000) (34205851645 / 1000000000000))
    | 14 => (orderedInterval (47717531723 / 1000000000000) (47717531725 / 1000000000000), orderedInterval (26330234065 / 1000000000000) (26330234066 / 1000000000000))
    | 15 => (orderedInterval (-2886748085 / 1000000000000) (-2886748083 / 1000000000000), orderedInterval (-59670122124 / 1000000000000) (-59670122122 / 1000000000000))
    | 16 => (orderedInterval (60688049302 / 1000000000000) (60688049303 / 1000000000000), orderedInterval (18710748112 / 1000000000000) (18710748113 / 1000000000000))
    | 17 => (orderedInterval (11041268031 / 1000000000000) (11041268092 / 1000000000000), orderedInterval (-51658678441 / 1000000000000) (-51658678379 / 1000000000000))
    | 18 => (orderedInterval (70395458570 / 1000000000000) (70395458575 / 1000000000000), orderedInterval (8895220014 / 1000000000000) (8895220020 / 1000000000000))
    | 19 => (orderedInterval (67010806377 / 1000000000000) (67010806378 / 1000000000000), orderedInterval (37826444478 / 1000000000000) (37826444479 / 1000000000000))
    | 20 => (orderedInterval (-94510900873 / 1000000000000) (-94510900119 / 1000000000000), orderedInterval (24540982412 / 1000000000000) (24540983166 / 1000000000000))
    | 21 => (orderedInterval (-102451928158 / 1000000000000) (-102451867259 / 1000000000000), orderedInterval (86091231337 / 1000000000000) (86091292236 / 1000000000000))
    | 22 => (orderedInterval (-76344928125 / 1000000000000) (-76344928124 / 1000000000000), orderedInterval (-25641274969 / 1000000000000) (-25641274968 / 1000000000000))
    | 23 => (orderedInterval (44559517203 / 1000000000000) (44559547214 / 1000000000000), orderedInterval (-52887632456 / 1000000000000) (-52887602444 / 1000000000000))
    | 24 => (orderedInterval (70534804585 / 1000000000000) (70534804586 / 1000000000000), orderedInterval (78710783679 / 1000000000000) (78710783680 / 1000000000000))
    | 25 => (orderedInterval (-46596038107 / 1000000000000) (-46596038106 / 1000000000000), orderedInterval (-24415532665 / 1000000000000) (-24415532664 / 1000000000000))
    | _ => (orderedInterval (-14936969895 / 1000000000000) (-14936969894 / 1000000000000), orderedInterval (-62619564366 / 1000000000000) (-62619564365 / 1000000000000))
  chunkTarget := fun r b =>
    match r.val with
    | 0 =>
      match b.val with
      | 0 => orderedInterval (-29243058650 / 1000000000000) (-29243058429 / 1000000000000)
      | 1 => orderedInterval (780572856 / 1000000000000) (780573284 / 1000000000000)
      | 2 => orderedInterval (-1577648618 / 1000000000000) (-1577648601 / 1000000000000)
      | 3 => orderedInterval (1611126403 / 1000000000000) (1611126453 / 1000000000000)
      | 4 => orderedInterval (3353026889 / 1000000000000) (3353026905 / 1000000000000)
      | 5 => orderedInterval (-3223610541 / 1000000000000) (-3223610527 / 1000000000000)
      | 6 => orderedInterval (-18125338476 / 1000000000000) (-18125338419 / 1000000000000)
      | 7 => orderedInterval (208819211 / 1000000000000) (208822651 / 1000000000000)
      | _ => orderedInterval (7020779008 / 1000000000000) (7020779043 / 1000000000000)
    | 1 =>
      match b.val with
      | 0 => orderedInterval (587162369 / 1000000000000) (587162592 / 1000000000000)
      | 1 => orderedInterval (-7658844575 / 1000000000000) (-7658844384 / 1000000000000)
      | 2 => orderedInterval (-2811049596 / 1000000000000) (-2811049569 / 1000000000000)
      | 3 => orderedInterval (-14205682788 / 1000000000000) (-14205682684 / 1000000000000)
      | 4 => orderedInterval (4091461882 / 1000000000000) (4091461906 / 1000000000000)
      | 5 => orderedInterval (-4806576654 / 1000000000000) (-4806576633 / 1000000000000)
      | 6 => orderedInterval (-2877656157 / 1000000000000) (-2877656113 / 1000000000000)
      | 7 => orderedInterval (4381825122 / 1000000000000) (4381827953 / 1000000000000)
      | _ => orderedInterval (18504989067 / 1000000000000) (18504989116 / 1000000000000)
    | 2 =>
      match b.val with
      | 0 => orderedInterval (29372821645 / 1000000000000) (29372821871 / 1000000000000)
      | 1 => orderedInterval (-3907380496 / 1000000000000) (-3907380302 / 1000000000000)
      | 2 => orderedInterval (3648678459 / 1000000000000) (3648678501 / 1000000000000)
      | 3 => orderedInterval (-9336885793 / 1000000000000) (-9336885573 / 1000000000000)
      | 4 => orderedInterval (-5814329177 / 1000000000000) (-5814329136 / 1000000000000)
      | 5 => orderedInterval (4795051025 / 1000000000000) (4795051057 / 1000000000000)
      | 6 => orderedInterval (15556245077 / 1000000000000) (15556245113 / 1000000000000)
      | 7 => orderedInterval (2712751558 / 1000000000000) (2712754382 / 1000000000000)
      | _ => orderedInterval (-17676001448 / 1000000000000) (-17676001376 / 1000000000000)
    | 3 =>
      match b.val with
      | 0 => orderedInterval (843546062 / 1000000000000) (843546290 / 1000000000000)
      | 1 => orderedInterval (15197985731 / 1000000000000) (15197986009 / 1000000000000)
      | 2 => orderedInterval (11491722133 / 1000000000000) (11491722202 / 1000000000000)
      | 3 => orderedInterval (48783948978 / 1000000000000) (48783949459 / 1000000000000)
      | 4 => orderedInterval (-7954612219 / 1000000000000) (-7954612151 / 1000000000000)
      | 5 => orderedInterval (12619044492 / 1000000000000) (12619044542 / 1000000000000)
      | 6 => orderedInterval (2663854275 / 1000000000000) (2663854307 / 1000000000000)
      | 7 => orderedInterval (-5402990886 / 1000000000000) (-5402987910 / 1000000000000)
      | _ => orderedInterval (-35187959474 / 1000000000000) (-35187959363 / 1000000000000)
    | _ =>
      match b.val with
      | 0 => orderedInterval (-29768478478 / 1000000000000) (-29768478246 / 1000000000000)
      | 1 => orderedInterval (9246431437 / 1000000000000) (9246431868 / 1000000000000)
      | 2 => orderedInterval (-8963619388 / 1000000000000) (-8963619273 / 1000000000000)
      | 3 => orderedInterval (53729610199 / 1000000000000) (53729611267 / 1000000000000)
      | 4 => orderedInterval (4514612884 / 1000000000000) (4514613002 / 1000000000000)
      | 5 => orderedInterval (-6246880600 / 1000000000000) (-6246880518 / 1000000000000)
      | 6 => orderedInterval (-14772244280 / 1000000000000) (-14772244250 / 1000000000000)
      | 7 => orderedInterval (-3893254436 / 1000000000000) (-3893251215 / 1000000000000)
      | _ => orderedInterval (52596874928 / 1000000000000) (52596875106 / 1000000000000)
  coefficientTarget := fun i =>
    match i.val with
    | 0 => orderedInterval (-39195331918 / 1000000000000) (-39195327640 / 1000000000000)
    | 1 => orderedInterval (-4794371330 / 1000000000000) (-4794367816 / 1000000000000)
    | 2 => orderedInterval (19350950850 / 1000000000000) (19350954537 / 1000000000000)
    | 3 => orderedInterval (43054539092 / 1000000000000) (43054543385 / 1000000000000)
    | _ => orderedInterval (56443052266 / 1000000000000) (56443057741 / 1000000000000)

theorem compactCertificate248_stateChecks0 :
    compactCertificate248.stateChecks 0 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 39 12 (247 / 2)) (orderedInterval (-70484621918 / 1000000000000) (-70484621383 / 1000000000000), orderedInterval (13948992013 / 1000000000000) (13948992549 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 29 12 (363878164131547 / 4000000000000)) (orderedInterval (-50451732560 / 1000000000000) (-50451732559 / 1000000000000), orderedInterval (-66452128617 / 1000000000000) (-66452128616 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 47 12 (117670721931451 / 800000000000)) (orderedInterval (-14234721778 / 1000000000000) (-14234721777 / 1000000000000), orderedInterval (-64181973160 / 1000000000000) (-64181973159 / 1000000000000))) = true
  norm_num [besselStateAtRationalPoint, besselIntervalStepZero,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, besselZeroTransition,
    besselInitial, besselGridStateAt, besselGridStateBlock00, besselGridStateBlock01,
    besselGridStateBlock02, besselGridStateBlock03, besselGridStateBlock04,
    besselGridStateBlock05, besselGridStateBlock06, besselGridStateBlock07,
    besselGridStateBlock08, besselGridStateBlock09, besselGridStateBlock10,
    besselGridStateBlock11, besselGridStateBlock12, besselGridStateBlock13,
    besselGridStateBlock14, besselGridState008, besselGridState011, besselGridState018, besselGridState021, besselGridState023, besselGridState029, besselGridState031, besselGridState034, besselGridState039, besselGridState040, besselGridState043, besselGridState045, besselGridState047, besselGridState049, besselGridState050, besselGridState051, besselGridState057, besselGridState060, besselGridState062, besselGridState068, besselGridState073, besselGridState078, besselGridState084, besselGridState088, besselGridState090, besselStateSubset, linearInterval, widenInterval,
    rationalErrorInterval, rationalIntervalSubset, orderedInterval, Finset.sum_range_succ,
    IntervalRat.add, IntervalRat.mul, IntervalRat.scale, IntervalRat.singleton]

theorem compactCertificate248_stateChecks1 :
    compactCertificate248.stateChecks 3 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 8 12 (106178740768529 / 4000000000000)) (orderedInterval (125863749513 / 1000000000000) (125863781510 / 1000000000000), orderedInterval (-92591336280 / 1000000000000) (-92591304283 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 23 12 (285211032979613 / 4000000000000)) (orderedInterval (16007071218 / 1000000000000) (16007071324 / 1000000000000), orderedInterval (-93237875643 / 1000000000000) (-93237875538 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 62 12 (774403435986921 / 4000000000000)) (orderedInterval (-21967470605 / 1000000000000) (-21967469740 / 1000000000000), orderedInterval (53026051391 / 1000000000000) (53026052257 / 1000000000000))) = true
  norm_num [besselStateAtRationalPoint, besselIntervalStepZero,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, besselZeroTransition,
    besselInitial, besselGridStateAt, besselGridStateBlock00, besselGridStateBlock01,
    besselGridStateBlock02, besselGridStateBlock03, besselGridStateBlock04,
    besselGridStateBlock05, besselGridStateBlock06, besselGridStateBlock07,
    besselGridStateBlock08, besselGridStateBlock09, besselGridStateBlock10,
    besselGridStateBlock11, besselGridStateBlock12, besselGridStateBlock13,
    besselGridStateBlock14, besselGridState008, besselGridState011, besselGridState018, besselGridState021, besselGridState023, besselGridState029, besselGridState031, besselGridState034, besselGridState039, besselGridState040, besselGridState043, besselGridState045, besselGridState047, besselGridState049, besselGridState050, besselGridState051, besselGridState057, besselGridState060, besselGridState062, besselGridState068, besselGridState073, besselGridState078, besselGridState084, besselGridState088, besselGridState090, besselStateSubset, linearInterval, widenInterval,
    rationalErrorInterval, rationalIntervalSubset, orderedInterval, Finset.sum_range_succ,
    IntervalRat.add, IntervalRat.mul, IntervalRat.scale, IntervalRat.singleton]

theorem compactCertificate248_stateChecks2 :
    compactCertificate248.stateChecks 6 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 45 12 (570422065959473 / 4000000000000)) (orderedInterval (-60233279570 / 1000000000000) (-60233269291 / 1000000000000), orderedInterval (29127214878 / 1000000000000) (29127225158 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 78 12 (977427932554229 / 4000000000000)) (orderedInterval (4975961857 / 1000000000000) (4975961859 / 1000000000000), orderedInterval (50788744755 / 1000000000000) (50788744757 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 57 12 (719968991231711 / 4000000000000)) (orderedInterval (-58927857087 / 1000000000000) (-58927856710 / 1000000000000), orderedInterval (8190111225 / 1000000000000) (8190111602 / 1000000000000))) = true
  norm_num [besselStateAtRationalPoint, besselIntervalStepZero,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, besselZeroTransition,
    besselInitial, besselGridStateAt, besselGridStateBlock00, besselGridStateBlock01,
    besselGridStateBlock02, besselGridStateBlock03, besselGridStateBlock04,
    besselGridStateBlock05, besselGridStateBlock06, besselGridStateBlock07,
    besselGridStateBlock08, besselGridStateBlock09, besselGridStateBlock10,
    besselGridStateBlock11, besselGridStateBlock12, besselGridStateBlock13,
    besselGridStateBlock14, besselGridState008, besselGridState011, besselGridState018, besselGridState021, besselGridState023, besselGridState029, besselGridState031, besselGridState034, besselGridState039, besselGridState040, besselGridState043, besselGridState045, besselGridState047, besselGridState049, besselGridState050, besselGridState051, besselGridState057, besselGridState060, besselGridState062, besselGridState068, besselGridState073, besselGridState078, besselGridState084, besselGridState088, besselGridState090, besselStateSubset, linearInterval, widenInterval,
    rationalErrorInterval, rationalIntervalSubset, orderedInterval, Finset.sum_range_succ,
    IntervalRat.add, IntervalRat.mul, IntervalRat.scale, IntervalRat.singleton]

theorem compactCertificate248_stateChecks3 :
    compactCertificate248.stateChecks 9 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 88 12 (1104617580884753 / 4000000000000)) (orderedInterval (22137031301 / 1000000000000) (22137031302 / 1000000000000), orderedInterval (42565761576 / 1000000000000) (42565761577 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 51 12 (637751257675337 / 4000000000000)) (orderedInterval (-76033134 / 1000000000000) (-76033130 / 1000000000000), orderedInterval (-63189294980 / 1000000000000) (-63189294975 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 90 12 (1131700798210333 / 4000000000000)) (orderedInterval (39043355567 / 1000000000000) (39043355568 / 1000000000000), orderedInterval (26870742977 / 1000000000000) (26870742978 / 1000000000000))) = true
  norm_num [besselStateAtRationalPoint, besselIntervalStepZero,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, besselZeroTransition,
    besselInitial, besselGridStateAt, besselGridStateBlock00, besselGridStateBlock01,
    besselGridStateBlock02, besselGridStateBlock03, besselGridStateBlock04,
    besselGridStateBlock05, besselGridStateBlock06, besselGridStateBlock07,
    besselGridStateBlock08, besselGridStateBlock09, besselGridStateBlock10,
    besselGridStateBlock11, besselGridStateBlock12, besselGridStateBlock13,
    besselGridStateBlock14, besselGridState008, besselGridState011, besselGridState018, besselGridState021, besselGridState023, besselGridState029, besselGridState031, besselGridState034, besselGridState039, besselGridState040, besselGridState043, besselGridState045, besselGridState047, besselGridState049, besselGridState050, besselGridState051, besselGridState057, besselGridState060, besselGridState062, besselGridState068, besselGridState073, besselGridState078, besselGridState084, besselGridState088, besselGridState090, besselStateSubset, linearInterval, widenInterval,
    rationalErrorInterval, rationalIntervalSubset, orderedInterval, Finset.sum_range_succ,
    IntervalRat.add, IntervalRat.mul, IntervalRat.scale, IntervalRat.singleton]

theorem compactCertificate248_stateChecks4 :
    compactCertificate248.stateChecks 12 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 84 12 (1057381686054577 / 4000000000000)) (orderedInterval (46358609571 / 1000000000000) (46358609572 / 1000000000000), orderedInterval (16010868324 / 1000000000000) (16010868325 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 60 12 (754597464435841 / 4000000000000)) (orderedInterval (46862169538 / 1000000000000) (46862169539 / 1000000000000), orderedInterval (34205851644 / 1000000000000) (34205851645 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 68 12 (855633098938839 / 4000000000000)) (orderedInterval (47717531723 / 1000000000000) (47717531725 / 1000000000000), orderedInterval (26330234065 / 1000000000000) (26330234066 / 1000000000000))) = true
  norm_num [besselStateAtRationalPoint, besselIntervalStepZero,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, besselZeroTransition,
    besselInitial, besselGridStateAt, besselGridStateBlock00, besselGridStateBlock01,
    besselGridStateBlock02, besselGridStateBlock03, besselGridStateBlock04,
    besselGridStateBlock05, besselGridStateBlock06, besselGridStateBlock07,
    besselGridStateBlock08, besselGridStateBlock09, besselGridStateBlock10,
    besselGridStateBlock11, besselGridStateBlock12, besselGridStateBlock13,
    besselGridStateBlock14, besselGridState008, besselGridState011, besselGridState018, besselGridState021, besselGridState023, besselGridState029, besselGridState031, besselGridState034, besselGridState039, besselGridState040, besselGridState043, besselGridState045, besselGridState047, besselGridState049, besselGridState050, besselGridState051, besselGridState057, besselGridState060, besselGridState062, besselGridState068, besselGridState073, besselGridState078, besselGridState084, besselGridState088, besselGridState090, besselStateSubset, linearInterval, widenInterval,
    rationalErrorInterval, rationalIntervalSubset, orderedInterval, Finset.sum_range_succ,
    IntervalRat.add, IntervalRat.mul, IntervalRat.scale, IntervalRat.singleton]

theorem compactCertificate248_stateChecks5 :
    compactCertificate248.stateChecks 15 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 57 12 (713337673660391 / 4000000000000)) (orderedInterval (-2886748085 / 1000000000000) (-2886748083 / 1000000000000), orderedInterval (-59670122124 / 1000000000000) (-59670122122 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 50 12 (630255468040211 / 4000000000000)) (orderedInterval (60688049302 / 1000000000000) (60688049303 / 1000000000000), orderedInterval (18710748112 / 1000000000000) (18710748113 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 73 12 (182672600024889 / 800000000000)) (orderedInterval (11041268031 / 1000000000000) (11041268092 / 1000000000000), orderedInterval (-51658678441 / 1000000000000) (-51658678379 / 1000000000000))) = true
  norm_num [besselStateAtRationalPoint, besselIntervalStepZero,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, besselZeroTransition,
    besselInitial, besselGridStateAt, besselGridStateBlock00, besselGridStateBlock01,
    besselGridStateBlock02, besselGridStateBlock03, besselGridStateBlock04,
    besselGridStateBlock05, besselGridStateBlock06, besselGridStateBlock07,
    besselGridStateBlock08, besselGridStateBlock09, besselGridStateBlock10,
    besselGridStateBlock11, besselGridStateBlock12, besselGridStateBlock13,
    besselGridStateBlock14, besselGridState008, besselGridState011, besselGridState018, besselGridState021, besselGridState023, besselGridState029, besselGridState031, besselGridState034, besselGridState039, besselGridState040, besselGridState043, besselGridState045, besselGridState047, besselGridState049, besselGridState050, besselGridState051, besselGridState057, besselGridState060, besselGridState062, besselGridState068, besselGridState073, besselGridState078, besselGridState084, besselGridState088, besselGridState090, besselStateSubset, linearInterval, widenInterval,
    rationalErrorInterval, rationalIntervalSubset, orderedInterval, Finset.sum_range_succ,
    IntervalRat.add, IntervalRat.mul, IntervalRat.scale, IntervalRat.singleton]

theorem compactCertificate248_stateChecks6 :
    compactCertificate248.stateChecks 18 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 40 12 (505282025201083 / 4000000000000)) (orderedInterval (70395458570 / 1000000000000) (70395458575 / 1000000000000), orderedInterval (8895220014 / 1000000000000) (8895220020 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 34 12 (428333168608163 / 4000000000000)) (orderedInterval (67010806377 / 1000000000000) (67010806378 / 1000000000000), orderedInterval (37826444478 / 1000000000000) (37826444479 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 21 12 (268031008768289 / 4000000000000)) (orderedInterval (-94510900873 / 1000000000000) (-94510900119 / 1000000000000), orderedInterval (24540982412 / 1000000000000) (24540983166 / 1000000000000))) = true
  norm_num [besselStateAtRationalPoint, besselIntervalStepZero,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, besselZeroTransition,
    besselInitial, besselGridStateAt, besselGridStateBlock00, besselGridStateBlock01,
    besselGridStateBlock02, besselGridStateBlock03, besselGridStateBlock04,
    besselGridStateBlock05, besselGridStateBlock06, besselGridStateBlock07,
    besselGridStateBlock08, besselGridStateBlock09, besselGridStateBlock10,
    besselGridStateBlock11, besselGridStateBlock12, besselGridStateBlock13,
    besselGridStateBlock14, besselGridState008, besselGridState011, besselGridState018, besselGridState021, besselGridState023, besselGridState029, besselGridState031, besselGridState034, besselGridState039, besselGridState040, besselGridState043, besselGridState045, besselGridState047, besselGridState049, besselGridState050, besselGridState051, besselGridState057, besselGridState060, besselGridState062, besselGridState068, besselGridState073, besselGridState078, besselGridState084, besselGridState088, besselGridState090, besselStateSubset, linearInterval, widenInterval,
    rationalErrorInterval, rationalIntervalSubset, orderedInterval, Finset.sum_range_succ,
    IntervalRat.add, IntervalRat.mul, IntervalRat.scale, IntervalRat.singleton]

theorem compactCertificate248_stateChecks7 :
    compactCertificate248.stateChecks 21 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 11 12 (144147967946463 / 4000000000000)) (orderedInterval (-102451928158 / 1000000000000) (-102451867259 / 1000000000000), orderedInterval (86091231337 / 1000000000000) (86091292236 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 31 12 (391389773748389 / 4000000000000)) (orderedInterval (-76344928125 / 1000000000000) (-76344928124 / 1000000000000), orderedInterval (-25641274969 / 1000000000000) (-25641274968 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 43 12 (534409275112453 / 4000000000000)) (orderedInterval (44559517203 / 1000000000000) (44559547214 / 1000000000000), orderedInterval (-52887632456 / 1000000000000) (-52887602444 / 1000000000000))) = true
  norm_num [besselStateAtRationalPoint, besselIntervalStepZero,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, besselZeroTransition,
    besselInitial, besselGridStateAt, besselGridStateBlock00, besselGridStateBlock01,
    besselGridStateBlock02, besselGridStateBlock03, besselGridStateBlock04,
    besselGridStateBlock05, besselGridStateBlock06, besselGridStateBlock07,
    besselGridStateBlock08, besselGridStateBlock09, besselGridStateBlock10,
    besselGridStateBlock11, besselGridStateBlock12, besselGridStateBlock13,
    besselGridStateBlock14, besselGridState008, besselGridState011, besselGridState018, besselGridState021, besselGridState023, besselGridState029, besselGridState031, besselGridState034, besselGridState039, besselGridState040, besselGridState043, besselGridState045, besselGridState047, besselGridState049, besselGridState050, besselGridState051, besselGridState057, besselGridState060, besselGridState062, besselGridState068, besselGridState073, besselGridState078, besselGridState084, besselGridState088, besselGridState090, besselStateSubset, linearInterval, widenInterval,
    rationalErrorInterval, rationalIntervalSubset, orderedInterval, Finset.sum_range_succ,
    IntervalRat.add, IntervalRat.mul, IntervalRat.scale, IntervalRat.singleton]

theorem compactCertificate248_stateChecks8 :
    compactCertificate248.stateChecks 24 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 18 12 (225968991231711 / 4000000000000)) (orderedInterval (70534804585 / 1000000000000) (70534804586 / 1000000000000), orderedInterval (78710783679 / 1000000000000) (78710783680 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 73 12 (918551403933631 / 4000000000000)) (orderedInterval (-46596038107 / 1000000000000) (-46596038106 / 1000000000000), orderedInterval (-24415532665 / 1000000000000) (-24415532664 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 49 12 (613549768422929 / 4000000000000)) (orderedInterval (-14936969895 / 1000000000000) (-14936969894 / 1000000000000), orderedInterval (-62619564366 / 1000000000000) (-62619564365 / 1000000000000))) = true
  norm_num [besselStateAtRationalPoint, besselIntervalStepZero,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, besselZeroTransition,
    besselInitial, besselGridStateAt, besselGridStateBlock00, besselGridStateBlock01,
    besselGridStateBlock02, besselGridStateBlock03, besselGridStateBlock04,
    besselGridStateBlock05, besselGridStateBlock06, besselGridStateBlock07,
    besselGridStateBlock08, besselGridStateBlock09, besselGridStateBlock10,
    besselGridStateBlock11, besselGridStateBlock12, besselGridStateBlock13,
    besselGridStateBlock14, besselGridState008, besselGridState011, besselGridState018, besselGridState021, besselGridState023, besselGridState029, besselGridState031, besselGridState034, besselGridState039, besselGridState040, besselGridState043, besselGridState045, besselGridState047, besselGridState049, besselGridState050, besselGridState051, besselGridState057, besselGridState060, besselGridState062, besselGridState068, besselGridState073, besselGridState078, besselGridState084, besselGridState088, besselGridState090, besselStateSubset, linearInterval, widenInterval,
    rationalErrorInterval, rationalIntervalSubset, orderedInterval, Finset.sum_range_succ,
    IntervalRat.add, IntervalRat.mul, IntervalRat.scale, IntervalRat.singleton]

theorem compactCertificate248_states : ∀ j,
    BesselStateValid (compactCertificate248.point j) (compactCertificate248.state j) :=
  compactCertificate248.statesValid_of_checks3 compactCertificate248_stateChecks0
    compactCertificate248_stateChecks1 compactCertificate248_stateChecks2
    compactCertificate248_stateChecks3 compactCertificate248_stateChecks4
    compactCertificate248_stateChecks5 compactCertificate248_stateChecks6
    compactCertificate248_stateChecks7 compactCertificate248_stateChecks8

theorem compactCertificate248_chunkChecks0_0 :
    compactCertificate248.chunkChecks (0 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 0) <| besselDerivativeNearFromState (247 / 2) 0 (IntervalRat.scale (247 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-70484621918 / 1000000000000) (-70484621383 / 1000000000000), orderedInterval (13948992013 / 1000000000000) (13948992549 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 0) <| besselDerivativeNearFromState (363878164131547 / 4000000000000) 0 (IntervalRat.scale (247 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-50451732560 / 1000000000000) (-50451732559 / 1000000000000), orderedInterval (-66452128617 / 1000000000000) (-66452128616 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 0) <| besselDerivativeNearFromState (117670721931451 / 800000000000) 0 (IntervalRat.scale (247 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-14234721778 / 1000000000000) (-14234721777 / 1000000000000), orderedInterval (-64181973160 / 1000000000000) (-64181973159 / 1000000000000)))) (orderedInterval (-29243058650 / 1000000000000) (-29243058429 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 0) <| besselDerivativeNearFromState (106178740768529 / 4000000000000) 0 (IntervalRat.scale (247 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (125863749513 / 1000000000000) (125863781510 / 1000000000000), orderedInterval (-92591336280 / 1000000000000) (-92591304283 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 0) <| besselDerivativeNearFromState (285211032979613 / 4000000000000) 0 (IntervalRat.scale (247 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (16007071218 / 1000000000000) (16007071324 / 1000000000000), orderedInterval (-93237875643 / 1000000000000) (-93237875538 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 0) <| besselDerivativeNearFromState (774403435986921 / 4000000000000) 0 (IntervalRat.scale (247 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-21967470605 / 1000000000000) (-21967469740 / 1000000000000), orderedInterval (53026051391 / 1000000000000) (53026052257 / 1000000000000)))) (orderedInterval (780572856 / 1000000000000) (780573284 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 0) <| besselDerivativeNearFromState (570422065959473 / 4000000000000) 0 (IntervalRat.scale (247 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-60233279570 / 1000000000000) (-60233269291 / 1000000000000), orderedInterval (29127214878 / 1000000000000) (29127225158 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 0) <| besselDerivativeNearFromState (977427932554229 / 4000000000000) 0 (IntervalRat.scale (247 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (4975961857 / 1000000000000) (4975961859 / 1000000000000), orderedInterval (50788744755 / 1000000000000) (50788744757 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 0) <| besselDerivativeNearFromState (719968991231711 / 4000000000000) 0 (IntervalRat.scale (247 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-58927857087 / 1000000000000) (-58927856710 / 1000000000000), orderedInterval (8190111225 / 1000000000000) (8190111602 / 1000000000000)))) (orderedInterval (-1577648618 / 1000000000000) (-1577648601 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate248_chunkChecks0_1 :
    compactCertificate248.chunkChecks (0 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 0) <| besselDerivativeNearFromState (1104617580884753 / 4000000000000) 0 (IntervalRat.scale (247 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (22137031301 / 1000000000000) (22137031302 / 1000000000000), orderedInterval (42565761576 / 1000000000000) (42565761577 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 0) <| besselDerivativeNearFromState (637751257675337 / 4000000000000) 0 (IntervalRat.scale (247 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-76033134 / 1000000000000) (-76033130 / 1000000000000), orderedInterval (-63189294980 / 1000000000000) (-63189294975 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 0) <| besselDerivativeNearFromState (1131700798210333 / 4000000000000) 0 (IntervalRat.scale (247 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (39043355567 / 1000000000000) (39043355568 / 1000000000000), orderedInterval (26870742977 / 1000000000000) (26870742978 / 1000000000000)))) (orderedInterval (1611126403 / 1000000000000) (1611126453 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 0) <| besselDerivativeNearFromState (1057381686054577 / 4000000000000) 0 (IntervalRat.scale (247 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (46358609571 / 1000000000000) (46358609572 / 1000000000000), orderedInterval (16010868324 / 1000000000000) (16010868325 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 0) <| besselDerivativeNearFromState (754597464435841 / 4000000000000) 0 (IntervalRat.scale (247 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (46862169538 / 1000000000000) (46862169539 / 1000000000000), orderedInterval (34205851644 / 1000000000000) (34205851645 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 0) <| besselDerivativeNearFromState (855633098938839 / 4000000000000) 0 (IntervalRat.scale (247 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (47717531723 / 1000000000000) (47717531725 / 1000000000000), orderedInterval (26330234065 / 1000000000000) (26330234066 / 1000000000000)))) (orderedInterval (3353026889 / 1000000000000) (3353026905 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 0) <| besselDerivativeNearFromState (713337673660391 / 4000000000000) 0 (IntervalRat.scale (247 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-2886748085 / 1000000000000) (-2886748083 / 1000000000000), orderedInterval (-59670122124 / 1000000000000) (-59670122122 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 0) <| besselDerivativeNearFromState (630255468040211 / 4000000000000) 0 (IntervalRat.scale (247 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (60688049302 / 1000000000000) (60688049303 / 1000000000000), orderedInterval (18710748112 / 1000000000000) (18710748113 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 0) <| besselDerivativeNearFromState (182672600024889 / 800000000000) 0 (IntervalRat.scale (247 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (11041268031 / 1000000000000) (11041268092 / 1000000000000), orderedInterval (-51658678441 / 1000000000000) (-51658678379 / 1000000000000)))) (orderedInterval (-3223610541 / 1000000000000) (-3223610527 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate248_chunkChecks0_2 :
    compactCertificate248.chunkChecks (0 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 0) <| besselDerivativeNearFromState (505282025201083 / 4000000000000) 0 (IntervalRat.scale (247 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (70395458570 / 1000000000000) (70395458575 / 1000000000000), orderedInterval (8895220014 / 1000000000000) (8895220020 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 0) <| besselDerivativeNearFromState (428333168608163 / 4000000000000) 0 (IntervalRat.scale (247 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (67010806377 / 1000000000000) (67010806378 / 1000000000000), orderedInterval (37826444478 / 1000000000000) (37826444479 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 0) <| besselDerivativeNearFromState (268031008768289 / 4000000000000) 0 (IntervalRat.scale (247 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-94510900873 / 1000000000000) (-94510900119 / 1000000000000), orderedInterval (24540982412 / 1000000000000) (24540983166 / 1000000000000)))) (orderedInterval (-18125338476 / 1000000000000) (-18125338419 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 0) <| besselDerivativeNearFromState (144147967946463 / 4000000000000) 0 (IntervalRat.scale (247 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-102451928158 / 1000000000000) (-102451867259 / 1000000000000), orderedInterval (86091231337 / 1000000000000) (86091292236 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 0) <| besselDerivativeNearFromState (391389773748389 / 4000000000000) 0 (IntervalRat.scale (247 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-76344928125 / 1000000000000) (-76344928124 / 1000000000000), orderedInterval (-25641274969 / 1000000000000) (-25641274968 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 0) <| besselDerivativeNearFromState (534409275112453 / 4000000000000) 0 (IntervalRat.scale (247 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (44559517203 / 1000000000000) (44559547214 / 1000000000000), orderedInterval (-52887632456 / 1000000000000) (-52887602444 / 1000000000000)))) (orderedInterval (208819211 / 1000000000000) (208822651 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 0) <| besselDerivativeNearFromState (225968991231711 / 4000000000000) 0 (IntervalRat.scale (247 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (70534804585 / 1000000000000) (70534804586 / 1000000000000), orderedInterval (78710783679 / 1000000000000) (78710783680 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 0) <| besselDerivativeNearFromState (918551403933631 / 4000000000000) 0 (IntervalRat.scale (247 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-46596038107 / 1000000000000) (-46596038106 / 1000000000000), orderedInterval (-24415532665 / 1000000000000) (-24415532664 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 0) <| besselDerivativeNearFromState (613549768422929 / 4000000000000) 0 (IntervalRat.scale (247 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-14936969895 / 1000000000000) (-14936969894 / 1000000000000), orderedInterval (-62619564366 / 1000000000000) (-62619564365 / 1000000000000)))) (orderedInterval (7020779008 / 1000000000000) (7020779043 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate248_chunkChecks0 :
    compactCertificate248.chunkChecks (0 : Fin 5) 0 9 = true :=
  compactCertificate248.chunkChecks_nine_of_three (0 : Fin 5) compactCertificate248_chunkChecks0_0
    compactCertificate248_chunkChecks0_1 compactCertificate248_chunkChecks0_2

theorem compactCertificate248_chunkChecks1_0 :
    compactCertificate248.chunkChecks (1 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 1) <| besselDerivativeNearFromState (247 / 2) 1 (IntervalRat.scale (247 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-70484621918 / 1000000000000) (-70484621383 / 1000000000000), orderedInterval (13948992013 / 1000000000000) (13948992549 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 1) <| besselDerivativeNearFromState (363878164131547 / 4000000000000) 1 (IntervalRat.scale (247 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-50451732560 / 1000000000000) (-50451732559 / 1000000000000), orderedInterval (-66452128617 / 1000000000000) (-66452128616 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 1) <| besselDerivativeNearFromState (117670721931451 / 800000000000) 1 (IntervalRat.scale (247 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-14234721778 / 1000000000000) (-14234721777 / 1000000000000), orderedInterval (-64181973160 / 1000000000000) (-64181973159 / 1000000000000)))) (orderedInterval (587162369 / 1000000000000) (587162592 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 1) <| besselDerivativeNearFromState (106178740768529 / 4000000000000) 1 (IntervalRat.scale (247 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (125863749513 / 1000000000000) (125863781510 / 1000000000000), orderedInterval (-92591336280 / 1000000000000) (-92591304283 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 1) <| besselDerivativeNearFromState (285211032979613 / 4000000000000) 1 (IntervalRat.scale (247 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (16007071218 / 1000000000000) (16007071324 / 1000000000000), orderedInterval (-93237875643 / 1000000000000) (-93237875538 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 1) <| besselDerivativeNearFromState (774403435986921 / 4000000000000) 1 (IntervalRat.scale (247 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-21967470605 / 1000000000000) (-21967469740 / 1000000000000), orderedInterval (53026051391 / 1000000000000) (53026052257 / 1000000000000)))) (orderedInterval (-7658844575 / 1000000000000) (-7658844384 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 1) <| besselDerivativeNearFromState (570422065959473 / 4000000000000) 1 (IntervalRat.scale (247 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-60233279570 / 1000000000000) (-60233269291 / 1000000000000), orderedInterval (29127214878 / 1000000000000) (29127225158 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 1) <| besselDerivativeNearFromState (977427932554229 / 4000000000000) 1 (IntervalRat.scale (247 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (4975961857 / 1000000000000) (4975961859 / 1000000000000), orderedInterval (50788744755 / 1000000000000) (50788744757 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 1) <| besselDerivativeNearFromState (719968991231711 / 4000000000000) 1 (IntervalRat.scale (247 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-58927857087 / 1000000000000) (-58927856710 / 1000000000000), orderedInterval (8190111225 / 1000000000000) (8190111602 / 1000000000000)))) (orderedInterval (-2811049596 / 1000000000000) (-2811049569 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate248_chunkChecks1_1 :
    compactCertificate248.chunkChecks (1 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 1) <| besselDerivativeNearFromState (1104617580884753 / 4000000000000) 1 (IntervalRat.scale (247 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (22137031301 / 1000000000000) (22137031302 / 1000000000000), orderedInterval (42565761576 / 1000000000000) (42565761577 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 1) <| besselDerivativeNearFromState (637751257675337 / 4000000000000) 1 (IntervalRat.scale (247 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-76033134 / 1000000000000) (-76033130 / 1000000000000), orderedInterval (-63189294980 / 1000000000000) (-63189294975 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 1) <| besselDerivativeNearFromState (1131700798210333 / 4000000000000) 1 (IntervalRat.scale (247 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (39043355567 / 1000000000000) (39043355568 / 1000000000000), orderedInterval (26870742977 / 1000000000000) (26870742978 / 1000000000000)))) (orderedInterval (-14205682788 / 1000000000000) (-14205682684 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 1) <| besselDerivativeNearFromState (1057381686054577 / 4000000000000) 1 (IntervalRat.scale (247 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (46358609571 / 1000000000000) (46358609572 / 1000000000000), orderedInterval (16010868324 / 1000000000000) (16010868325 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 1) <| besselDerivativeNearFromState (754597464435841 / 4000000000000) 1 (IntervalRat.scale (247 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (46862169538 / 1000000000000) (46862169539 / 1000000000000), orderedInterval (34205851644 / 1000000000000) (34205851645 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 1) <| besselDerivativeNearFromState (855633098938839 / 4000000000000) 1 (IntervalRat.scale (247 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (47717531723 / 1000000000000) (47717531725 / 1000000000000), orderedInterval (26330234065 / 1000000000000) (26330234066 / 1000000000000)))) (orderedInterval (4091461882 / 1000000000000) (4091461906 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 1) <| besselDerivativeNearFromState (713337673660391 / 4000000000000) 1 (IntervalRat.scale (247 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-2886748085 / 1000000000000) (-2886748083 / 1000000000000), orderedInterval (-59670122124 / 1000000000000) (-59670122122 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 1) <| besselDerivativeNearFromState (630255468040211 / 4000000000000) 1 (IntervalRat.scale (247 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (60688049302 / 1000000000000) (60688049303 / 1000000000000), orderedInterval (18710748112 / 1000000000000) (18710748113 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 1) <| besselDerivativeNearFromState (182672600024889 / 800000000000) 1 (IntervalRat.scale (247 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (11041268031 / 1000000000000) (11041268092 / 1000000000000), orderedInterval (-51658678441 / 1000000000000) (-51658678379 / 1000000000000)))) (orderedInterval (-4806576654 / 1000000000000) (-4806576633 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate248_chunkChecks1_2 :
    compactCertificate248.chunkChecks (1 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 1) <| besselDerivativeNearFromState (505282025201083 / 4000000000000) 1 (IntervalRat.scale (247 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (70395458570 / 1000000000000) (70395458575 / 1000000000000), orderedInterval (8895220014 / 1000000000000) (8895220020 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 1) <| besselDerivativeNearFromState (428333168608163 / 4000000000000) 1 (IntervalRat.scale (247 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (67010806377 / 1000000000000) (67010806378 / 1000000000000), orderedInterval (37826444478 / 1000000000000) (37826444479 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 1) <| besselDerivativeNearFromState (268031008768289 / 4000000000000) 1 (IntervalRat.scale (247 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-94510900873 / 1000000000000) (-94510900119 / 1000000000000), orderedInterval (24540982412 / 1000000000000) (24540983166 / 1000000000000)))) (orderedInterval (-2877656157 / 1000000000000) (-2877656113 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 1) <| besselDerivativeNearFromState (144147967946463 / 4000000000000) 1 (IntervalRat.scale (247 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-102451928158 / 1000000000000) (-102451867259 / 1000000000000), orderedInterval (86091231337 / 1000000000000) (86091292236 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 1) <| besselDerivativeNearFromState (391389773748389 / 4000000000000) 1 (IntervalRat.scale (247 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-76344928125 / 1000000000000) (-76344928124 / 1000000000000), orderedInterval (-25641274969 / 1000000000000) (-25641274968 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 1) <| besselDerivativeNearFromState (534409275112453 / 4000000000000) 1 (IntervalRat.scale (247 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (44559517203 / 1000000000000) (44559547214 / 1000000000000), orderedInterval (-52887632456 / 1000000000000) (-52887602444 / 1000000000000)))) (orderedInterval (4381825122 / 1000000000000) (4381827953 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 1) <| besselDerivativeNearFromState (225968991231711 / 4000000000000) 1 (IntervalRat.scale (247 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (70534804585 / 1000000000000) (70534804586 / 1000000000000), orderedInterval (78710783679 / 1000000000000) (78710783680 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 1) <| besselDerivativeNearFromState (918551403933631 / 4000000000000) 1 (IntervalRat.scale (247 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-46596038107 / 1000000000000) (-46596038106 / 1000000000000), orderedInterval (-24415532665 / 1000000000000) (-24415532664 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 1) <| besselDerivativeNearFromState (613549768422929 / 4000000000000) 1 (IntervalRat.scale (247 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-14936969895 / 1000000000000) (-14936969894 / 1000000000000), orderedInterval (-62619564366 / 1000000000000) (-62619564365 / 1000000000000)))) (orderedInterval (18504989067 / 1000000000000) (18504989116 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate248_chunkChecks1 :
    compactCertificate248.chunkChecks (1 : Fin 5) 0 9 = true :=
  compactCertificate248.chunkChecks_nine_of_three (1 : Fin 5) compactCertificate248_chunkChecks1_0
    compactCertificate248_chunkChecks1_1 compactCertificate248_chunkChecks1_2

theorem compactCertificate248_chunkChecks2_0 :
    compactCertificate248.chunkChecks (2 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 2) <| besselDerivativeNearFromState (247 / 2) 2 (IntervalRat.scale (247 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-70484621918 / 1000000000000) (-70484621383 / 1000000000000), orderedInterval (13948992013 / 1000000000000) (13948992549 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 2) <| besselDerivativeNearFromState (363878164131547 / 4000000000000) 2 (IntervalRat.scale (247 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-50451732560 / 1000000000000) (-50451732559 / 1000000000000), orderedInterval (-66452128617 / 1000000000000) (-66452128616 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 2) <| besselDerivativeNearFromState (117670721931451 / 800000000000) 2 (IntervalRat.scale (247 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-14234721778 / 1000000000000) (-14234721777 / 1000000000000), orderedInterval (-64181973160 / 1000000000000) (-64181973159 / 1000000000000)))) (orderedInterval (29372821645 / 1000000000000) (29372821871 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 2) <| besselDerivativeNearFromState (106178740768529 / 4000000000000) 2 (IntervalRat.scale (247 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (125863749513 / 1000000000000) (125863781510 / 1000000000000), orderedInterval (-92591336280 / 1000000000000) (-92591304283 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 2) <| besselDerivativeNearFromState (285211032979613 / 4000000000000) 2 (IntervalRat.scale (247 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (16007071218 / 1000000000000) (16007071324 / 1000000000000), orderedInterval (-93237875643 / 1000000000000) (-93237875538 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 2) <| besselDerivativeNearFromState (774403435986921 / 4000000000000) 2 (IntervalRat.scale (247 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-21967470605 / 1000000000000) (-21967469740 / 1000000000000), orderedInterval (53026051391 / 1000000000000) (53026052257 / 1000000000000)))) (orderedInterval (-3907380496 / 1000000000000) (-3907380302 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 2) <| besselDerivativeNearFromState (570422065959473 / 4000000000000) 2 (IntervalRat.scale (247 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-60233279570 / 1000000000000) (-60233269291 / 1000000000000), orderedInterval (29127214878 / 1000000000000) (29127225158 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 2) <| besselDerivativeNearFromState (977427932554229 / 4000000000000) 2 (IntervalRat.scale (247 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (4975961857 / 1000000000000) (4975961859 / 1000000000000), orderedInterval (50788744755 / 1000000000000) (50788744757 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 2) <| besselDerivativeNearFromState (719968991231711 / 4000000000000) 2 (IntervalRat.scale (247 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-58927857087 / 1000000000000) (-58927856710 / 1000000000000), orderedInterval (8190111225 / 1000000000000) (8190111602 / 1000000000000)))) (orderedInterval (3648678459 / 1000000000000) (3648678501 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate248_chunkChecks2_1 :
    compactCertificate248.chunkChecks (2 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 2) <| besselDerivativeNearFromState (1104617580884753 / 4000000000000) 2 (IntervalRat.scale (247 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (22137031301 / 1000000000000) (22137031302 / 1000000000000), orderedInterval (42565761576 / 1000000000000) (42565761577 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 2) <| besselDerivativeNearFromState (637751257675337 / 4000000000000) 2 (IntervalRat.scale (247 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-76033134 / 1000000000000) (-76033130 / 1000000000000), orderedInterval (-63189294980 / 1000000000000) (-63189294975 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 2) <| besselDerivativeNearFromState (1131700798210333 / 4000000000000) 2 (IntervalRat.scale (247 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (39043355567 / 1000000000000) (39043355568 / 1000000000000), orderedInterval (26870742977 / 1000000000000) (26870742978 / 1000000000000)))) (orderedInterval (-9336885793 / 1000000000000) (-9336885573 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 2) <| besselDerivativeNearFromState (1057381686054577 / 4000000000000) 2 (IntervalRat.scale (247 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (46358609571 / 1000000000000) (46358609572 / 1000000000000), orderedInterval (16010868324 / 1000000000000) (16010868325 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 2) <| besselDerivativeNearFromState (754597464435841 / 4000000000000) 2 (IntervalRat.scale (247 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (46862169538 / 1000000000000) (46862169539 / 1000000000000), orderedInterval (34205851644 / 1000000000000) (34205851645 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 2) <| besselDerivativeNearFromState (855633098938839 / 4000000000000) 2 (IntervalRat.scale (247 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (47717531723 / 1000000000000) (47717531725 / 1000000000000), orderedInterval (26330234065 / 1000000000000) (26330234066 / 1000000000000)))) (orderedInterval (-5814329177 / 1000000000000) (-5814329136 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 2) <| besselDerivativeNearFromState (713337673660391 / 4000000000000) 2 (IntervalRat.scale (247 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-2886748085 / 1000000000000) (-2886748083 / 1000000000000), orderedInterval (-59670122124 / 1000000000000) (-59670122122 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 2) <| besselDerivativeNearFromState (630255468040211 / 4000000000000) 2 (IntervalRat.scale (247 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (60688049302 / 1000000000000) (60688049303 / 1000000000000), orderedInterval (18710748112 / 1000000000000) (18710748113 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 2) <| besselDerivativeNearFromState (182672600024889 / 800000000000) 2 (IntervalRat.scale (247 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (11041268031 / 1000000000000) (11041268092 / 1000000000000), orderedInterval (-51658678441 / 1000000000000) (-51658678379 / 1000000000000)))) (orderedInterval (4795051025 / 1000000000000) (4795051057 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate248_chunkChecks2_2 :
    compactCertificate248.chunkChecks (2 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 2) <| besselDerivativeNearFromState (505282025201083 / 4000000000000) 2 (IntervalRat.scale (247 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (70395458570 / 1000000000000) (70395458575 / 1000000000000), orderedInterval (8895220014 / 1000000000000) (8895220020 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 2) <| besselDerivativeNearFromState (428333168608163 / 4000000000000) 2 (IntervalRat.scale (247 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (67010806377 / 1000000000000) (67010806378 / 1000000000000), orderedInterval (37826444478 / 1000000000000) (37826444479 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 2) <| besselDerivativeNearFromState (268031008768289 / 4000000000000) 2 (IntervalRat.scale (247 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-94510900873 / 1000000000000) (-94510900119 / 1000000000000), orderedInterval (24540982412 / 1000000000000) (24540983166 / 1000000000000)))) (orderedInterval (15556245077 / 1000000000000) (15556245113 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 2) <| besselDerivativeNearFromState (144147967946463 / 4000000000000) 2 (IntervalRat.scale (247 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-102451928158 / 1000000000000) (-102451867259 / 1000000000000), orderedInterval (86091231337 / 1000000000000) (86091292236 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 2) <| besselDerivativeNearFromState (391389773748389 / 4000000000000) 2 (IntervalRat.scale (247 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-76344928125 / 1000000000000) (-76344928124 / 1000000000000), orderedInterval (-25641274969 / 1000000000000) (-25641274968 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 2) <| besselDerivativeNearFromState (534409275112453 / 4000000000000) 2 (IntervalRat.scale (247 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (44559517203 / 1000000000000) (44559547214 / 1000000000000), orderedInterval (-52887632456 / 1000000000000) (-52887602444 / 1000000000000)))) (orderedInterval (2712751558 / 1000000000000) (2712754382 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 2) <| besselDerivativeNearFromState (225968991231711 / 4000000000000) 2 (IntervalRat.scale (247 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (70534804585 / 1000000000000) (70534804586 / 1000000000000), orderedInterval (78710783679 / 1000000000000) (78710783680 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 2) <| besselDerivativeNearFromState (918551403933631 / 4000000000000) 2 (IntervalRat.scale (247 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-46596038107 / 1000000000000) (-46596038106 / 1000000000000), orderedInterval (-24415532665 / 1000000000000) (-24415532664 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 2) <| besselDerivativeNearFromState (613549768422929 / 4000000000000) 2 (IntervalRat.scale (247 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-14936969895 / 1000000000000) (-14936969894 / 1000000000000), orderedInterval (-62619564366 / 1000000000000) (-62619564365 / 1000000000000)))) (orderedInterval (-17676001448 / 1000000000000) (-17676001376 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate248_chunkChecks2 :
    compactCertificate248.chunkChecks (2 : Fin 5) 0 9 = true :=
  compactCertificate248.chunkChecks_nine_of_three (2 : Fin 5) compactCertificate248_chunkChecks2_0
    compactCertificate248_chunkChecks2_1 compactCertificate248_chunkChecks2_2

theorem compactCertificate248_chunkChecks3_0 :
    compactCertificate248.chunkChecks (3 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 3) <| besselDerivativeNearFromState (247 / 2) 3 (IntervalRat.scale (247 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-70484621918 / 1000000000000) (-70484621383 / 1000000000000), orderedInterval (13948992013 / 1000000000000) (13948992549 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 3) <| besselDerivativeNearFromState (363878164131547 / 4000000000000) 3 (IntervalRat.scale (247 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-50451732560 / 1000000000000) (-50451732559 / 1000000000000), orderedInterval (-66452128617 / 1000000000000) (-66452128616 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 3) <| besselDerivativeNearFromState (117670721931451 / 800000000000) 3 (IntervalRat.scale (247 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-14234721778 / 1000000000000) (-14234721777 / 1000000000000), orderedInterval (-64181973160 / 1000000000000) (-64181973159 / 1000000000000)))) (orderedInterval (843546062 / 1000000000000) (843546290 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 3) <| besselDerivativeNearFromState (106178740768529 / 4000000000000) 3 (IntervalRat.scale (247 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (125863749513 / 1000000000000) (125863781510 / 1000000000000), orderedInterval (-92591336280 / 1000000000000) (-92591304283 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 3) <| besselDerivativeNearFromState (285211032979613 / 4000000000000) 3 (IntervalRat.scale (247 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (16007071218 / 1000000000000) (16007071324 / 1000000000000), orderedInterval (-93237875643 / 1000000000000) (-93237875538 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 3) <| besselDerivativeNearFromState (774403435986921 / 4000000000000) 3 (IntervalRat.scale (247 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-21967470605 / 1000000000000) (-21967469740 / 1000000000000), orderedInterval (53026051391 / 1000000000000) (53026052257 / 1000000000000)))) (orderedInterval (15197985731 / 1000000000000) (15197986009 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 3) <| besselDerivativeNearFromState (570422065959473 / 4000000000000) 3 (IntervalRat.scale (247 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-60233279570 / 1000000000000) (-60233269291 / 1000000000000), orderedInterval (29127214878 / 1000000000000) (29127225158 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 3) <| besselDerivativeNearFromState (977427932554229 / 4000000000000) 3 (IntervalRat.scale (247 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (4975961857 / 1000000000000) (4975961859 / 1000000000000), orderedInterval (50788744755 / 1000000000000) (50788744757 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 3) <| besselDerivativeNearFromState (719968991231711 / 4000000000000) 3 (IntervalRat.scale (247 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-58927857087 / 1000000000000) (-58927856710 / 1000000000000), orderedInterval (8190111225 / 1000000000000) (8190111602 / 1000000000000)))) (orderedInterval (11491722133 / 1000000000000) (11491722202 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate248_chunkChecks3_1 :
    compactCertificate248.chunkChecks (3 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 3) <| besselDerivativeNearFromState (1104617580884753 / 4000000000000) 3 (IntervalRat.scale (247 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (22137031301 / 1000000000000) (22137031302 / 1000000000000), orderedInterval (42565761576 / 1000000000000) (42565761577 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 3) <| besselDerivativeNearFromState (637751257675337 / 4000000000000) 3 (IntervalRat.scale (247 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-76033134 / 1000000000000) (-76033130 / 1000000000000), orderedInterval (-63189294980 / 1000000000000) (-63189294975 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 3) <| besselDerivativeNearFromState (1131700798210333 / 4000000000000) 3 (IntervalRat.scale (247 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (39043355567 / 1000000000000) (39043355568 / 1000000000000), orderedInterval (26870742977 / 1000000000000) (26870742978 / 1000000000000)))) (orderedInterval (48783948978 / 1000000000000) (48783949459 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 3) <| besselDerivativeNearFromState (1057381686054577 / 4000000000000) 3 (IntervalRat.scale (247 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (46358609571 / 1000000000000) (46358609572 / 1000000000000), orderedInterval (16010868324 / 1000000000000) (16010868325 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 3) <| besselDerivativeNearFromState (754597464435841 / 4000000000000) 3 (IntervalRat.scale (247 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (46862169538 / 1000000000000) (46862169539 / 1000000000000), orderedInterval (34205851644 / 1000000000000) (34205851645 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 3) <| besselDerivativeNearFromState (855633098938839 / 4000000000000) 3 (IntervalRat.scale (247 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (47717531723 / 1000000000000) (47717531725 / 1000000000000), orderedInterval (26330234065 / 1000000000000) (26330234066 / 1000000000000)))) (orderedInterval (-7954612219 / 1000000000000) (-7954612151 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 3) <| besselDerivativeNearFromState (713337673660391 / 4000000000000) 3 (IntervalRat.scale (247 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-2886748085 / 1000000000000) (-2886748083 / 1000000000000), orderedInterval (-59670122124 / 1000000000000) (-59670122122 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 3) <| besselDerivativeNearFromState (630255468040211 / 4000000000000) 3 (IntervalRat.scale (247 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (60688049302 / 1000000000000) (60688049303 / 1000000000000), orderedInterval (18710748112 / 1000000000000) (18710748113 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 3) <| besselDerivativeNearFromState (182672600024889 / 800000000000) 3 (IntervalRat.scale (247 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (11041268031 / 1000000000000) (11041268092 / 1000000000000), orderedInterval (-51658678441 / 1000000000000) (-51658678379 / 1000000000000)))) (orderedInterval (12619044492 / 1000000000000) (12619044542 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate248_chunkChecks3_2 :
    compactCertificate248.chunkChecks (3 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 3) <| besselDerivativeNearFromState (505282025201083 / 4000000000000) 3 (IntervalRat.scale (247 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (70395458570 / 1000000000000) (70395458575 / 1000000000000), orderedInterval (8895220014 / 1000000000000) (8895220020 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 3) <| besselDerivativeNearFromState (428333168608163 / 4000000000000) 3 (IntervalRat.scale (247 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (67010806377 / 1000000000000) (67010806378 / 1000000000000), orderedInterval (37826444478 / 1000000000000) (37826444479 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 3) <| besselDerivativeNearFromState (268031008768289 / 4000000000000) 3 (IntervalRat.scale (247 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-94510900873 / 1000000000000) (-94510900119 / 1000000000000), orderedInterval (24540982412 / 1000000000000) (24540983166 / 1000000000000)))) (orderedInterval (2663854275 / 1000000000000) (2663854307 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 3) <| besselDerivativeNearFromState (144147967946463 / 4000000000000) 3 (IntervalRat.scale (247 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-102451928158 / 1000000000000) (-102451867259 / 1000000000000), orderedInterval (86091231337 / 1000000000000) (86091292236 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 3) <| besselDerivativeNearFromState (391389773748389 / 4000000000000) 3 (IntervalRat.scale (247 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-76344928125 / 1000000000000) (-76344928124 / 1000000000000), orderedInterval (-25641274969 / 1000000000000) (-25641274968 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 3) <| besselDerivativeNearFromState (534409275112453 / 4000000000000) 3 (IntervalRat.scale (247 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (44559517203 / 1000000000000) (44559547214 / 1000000000000), orderedInterval (-52887632456 / 1000000000000) (-52887602444 / 1000000000000)))) (orderedInterval (-5402990886 / 1000000000000) (-5402987910 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 3) <| besselDerivativeNearFromState (225968991231711 / 4000000000000) 3 (IntervalRat.scale (247 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (70534804585 / 1000000000000) (70534804586 / 1000000000000), orderedInterval (78710783679 / 1000000000000) (78710783680 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 3) <| besselDerivativeNearFromState (918551403933631 / 4000000000000) 3 (IntervalRat.scale (247 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-46596038107 / 1000000000000) (-46596038106 / 1000000000000), orderedInterval (-24415532665 / 1000000000000) (-24415532664 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 3) <| besselDerivativeNearFromState (613549768422929 / 4000000000000) 3 (IntervalRat.scale (247 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-14936969895 / 1000000000000) (-14936969894 / 1000000000000), orderedInterval (-62619564366 / 1000000000000) (-62619564365 / 1000000000000)))) (orderedInterval (-35187959474 / 1000000000000) (-35187959363 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate248_chunkChecks3 :
    compactCertificate248.chunkChecks (3 : Fin 5) 0 9 = true :=
  compactCertificate248.chunkChecks_nine_of_three (3 : Fin 5) compactCertificate248_chunkChecks3_0
    compactCertificate248_chunkChecks3_1 compactCertificate248_chunkChecks3_2

theorem compactCertificate248_chunkChecks4_0 :
    compactCertificate248.chunkChecks (4 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 4) <| besselDerivativeNearFromState (247 / 2) 4 (IntervalRat.scale (247 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-70484621918 / 1000000000000) (-70484621383 / 1000000000000), orderedInterval (13948992013 / 1000000000000) (13948992549 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 4) <| besselDerivativeNearFromState (363878164131547 / 4000000000000) 4 (IntervalRat.scale (247 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-50451732560 / 1000000000000) (-50451732559 / 1000000000000), orderedInterval (-66452128617 / 1000000000000) (-66452128616 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 4) <| besselDerivativeNearFromState (117670721931451 / 800000000000) 4 (IntervalRat.scale (247 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-14234721778 / 1000000000000) (-14234721777 / 1000000000000), orderedInterval (-64181973160 / 1000000000000) (-64181973159 / 1000000000000)))) (orderedInterval (-29768478478 / 1000000000000) (-29768478246 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 4) <| besselDerivativeNearFromState (106178740768529 / 4000000000000) 4 (IntervalRat.scale (247 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (125863749513 / 1000000000000) (125863781510 / 1000000000000), orderedInterval (-92591336280 / 1000000000000) (-92591304283 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 4) <| besselDerivativeNearFromState (285211032979613 / 4000000000000) 4 (IntervalRat.scale (247 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (16007071218 / 1000000000000) (16007071324 / 1000000000000), orderedInterval (-93237875643 / 1000000000000) (-93237875538 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 4) <| besselDerivativeNearFromState (774403435986921 / 4000000000000) 4 (IntervalRat.scale (247 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-21967470605 / 1000000000000) (-21967469740 / 1000000000000), orderedInterval (53026051391 / 1000000000000) (53026052257 / 1000000000000)))) (orderedInterval (9246431437 / 1000000000000) (9246431868 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 4) <| besselDerivativeNearFromState (570422065959473 / 4000000000000) 4 (IntervalRat.scale (247 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-60233279570 / 1000000000000) (-60233269291 / 1000000000000), orderedInterval (29127214878 / 1000000000000) (29127225158 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 4) <| besselDerivativeNearFromState (977427932554229 / 4000000000000) 4 (IntervalRat.scale (247 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (4975961857 / 1000000000000) (4975961859 / 1000000000000), orderedInterval (50788744755 / 1000000000000) (50788744757 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 4) <| besselDerivativeNearFromState (719968991231711 / 4000000000000) 4 (IntervalRat.scale (247 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-58927857087 / 1000000000000) (-58927856710 / 1000000000000), orderedInterval (8190111225 / 1000000000000) (8190111602 / 1000000000000)))) (orderedInterval (-8963619388 / 1000000000000) (-8963619273 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate248_chunkChecks4_1 :
    compactCertificate248.chunkChecks (4 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 4) <| besselDerivativeNearFromState (1104617580884753 / 4000000000000) 4 (IntervalRat.scale (247 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (22137031301 / 1000000000000) (22137031302 / 1000000000000), orderedInterval (42565761576 / 1000000000000) (42565761577 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 4) <| besselDerivativeNearFromState (637751257675337 / 4000000000000) 4 (IntervalRat.scale (247 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-76033134 / 1000000000000) (-76033130 / 1000000000000), orderedInterval (-63189294980 / 1000000000000) (-63189294975 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 4) <| besselDerivativeNearFromState (1131700798210333 / 4000000000000) 4 (IntervalRat.scale (247 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (39043355567 / 1000000000000) (39043355568 / 1000000000000), orderedInterval (26870742977 / 1000000000000) (26870742978 / 1000000000000)))) (orderedInterval (53729610199 / 1000000000000) (53729611267 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 4) <| besselDerivativeNearFromState (1057381686054577 / 4000000000000) 4 (IntervalRat.scale (247 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (46358609571 / 1000000000000) (46358609572 / 1000000000000), orderedInterval (16010868324 / 1000000000000) (16010868325 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 4) <| besselDerivativeNearFromState (754597464435841 / 4000000000000) 4 (IntervalRat.scale (247 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (46862169538 / 1000000000000) (46862169539 / 1000000000000), orderedInterval (34205851644 / 1000000000000) (34205851645 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 4) <| besselDerivativeNearFromState (855633098938839 / 4000000000000) 4 (IntervalRat.scale (247 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (47717531723 / 1000000000000) (47717531725 / 1000000000000), orderedInterval (26330234065 / 1000000000000) (26330234066 / 1000000000000)))) (orderedInterval (4514612884 / 1000000000000) (4514613002 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 4) <| besselDerivativeNearFromState (713337673660391 / 4000000000000) 4 (IntervalRat.scale (247 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-2886748085 / 1000000000000) (-2886748083 / 1000000000000), orderedInterval (-59670122124 / 1000000000000) (-59670122122 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 4) <| besselDerivativeNearFromState (630255468040211 / 4000000000000) 4 (IntervalRat.scale (247 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (60688049302 / 1000000000000) (60688049303 / 1000000000000), orderedInterval (18710748112 / 1000000000000) (18710748113 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 4) <| besselDerivativeNearFromState (182672600024889 / 800000000000) 4 (IntervalRat.scale (247 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (11041268031 / 1000000000000) (11041268092 / 1000000000000), orderedInterval (-51658678441 / 1000000000000) (-51658678379 / 1000000000000)))) (orderedInterval (-6246880600 / 1000000000000) (-6246880518 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate248_chunkChecks4_2 :
    compactCertificate248.chunkChecks (4 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 4) <| besselDerivativeNearFromState (505282025201083 / 4000000000000) 4 (IntervalRat.scale (247 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (70395458570 / 1000000000000) (70395458575 / 1000000000000), orderedInterval (8895220014 / 1000000000000) (8895220020 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 4) <| besselDerivativeNearFromState (428333168608163 / 4000000000000) 4 (IntervalRat.scale (247 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (67010806377 / 1000000000000) (67010806378 / 1000000000000), orderedInterval (37826444478 / 1000000000000) (37826444479 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 4) <| besselDerivativeNearFromState (268031008768289 / 4000000000000) 4 (IntervalRat.scale (247 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-94510900873 / 1000000000000) (-94510900119 / 1000000000000), orderedInterval (24540982412 / 1000000000000) (24540983166 / 1000000000000)))) (orderedInterval (-14772244280 / 1000000000000) (-14772244250 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 4) <| besselDerivativeNearFromState (144147967946463 / 4000000000000) 4 (IntervalRat.scale (247 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-102451928158 / 1000000000000) (-102451867259 / 1000000000000), orderedInterval (86091231337 / 1000000000000) (86091292236 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 4) <| besselDerivativeNearFromState (391389773748389 / 4000000000000) 4 (IntervalRat.scale (247 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-76344928125 / 1000000000000) (-76344928124 / 1000000000000), orderedInterval (-25641274969 / 1000000000000) (-25641274968 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 4) <| besselDerivativeNearFromState (534409275112453 / 4000000000000) 4 (IntervalRat.scale (247 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (44559517203 / 1000000000000) (44559547214 / 1000000000000), orderedInterval (-52887632456 / 1000000000000) (-52887602444 / 1000000000000)))) (orderedInterval (-3893254436 / 1000000000000) (-3893251215 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 4) <| besselDerivativeNearFromState (225968991231711 / 4000000000000) 4 (IntervalRat.scale (247 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (70534804585 / 1000000000000) (70534804586 / 1000000000000), orderedInterval (78710783679 / 1000000000000) (78710783680 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 4) <| besselDerivativeNearFromState (918551403933631 / 4000000000000) 4 (IntervalRat.scale (247 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-46596038107 / 1000000000000) (-46596038106 / 1000000000000), orderedInterval (-24415532665 / 1000000000000) (-24415532664 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 4) <| besselDerivativeNearFromState (613549768422929 / 4000000000000) 4 (IntervalRat.scale (247 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-14936969895 / 1000000000000) (-14936969894 / 1000000000000), orderedInterval (-62619564366 / 1000000000000) (-62619564365 / 1000000000000)))) (orderedInterval (52596874928 / 1000000000000) (52596875106 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate248_chunkChecks4 :
    compactCertificate248.chunkChecks (4 : Fin 5) 0 9 = true :=
  compactCertificate248.chunkChecks_nine_of_three (4 : Fin 5) compactCertificate248_chunkChecks4_0
    compactCertificate248_chunkChecks4_1 compactCertificate248_chunkChecks4_2

theorem compactCertificate248_chunks :
    ∀ r : Fin 5, ∀ b, compactCertificate248.chunkCheck r b = true :=
  compactCertificate248.chunkChecks_all (by
    intro r
    fin_cases r
    · exact compactCertificate248_chunkChecks0
    · exact compactCertificate248_chunkChecks1
    · exact compactCertificate248_chunkChecks2
    · exact compactCertificate248_chunkChecks3
    · exact compactCertificate248_chunkChecks4)

theorem compactCertificate248_coefficient0 :
    compactCertificate248.coefficientCheck (0 : Fin 5) = true := by
  norm_num [CompactCertificate.coefficientCheck, intervalFinSumHull,
    compactCertificate248, rationalIntervalSubset, orderedInterval, Fin.sum_univ_succ]

theorem compactCertificate248_coefficient1 :
    compactCertificate248.coefficientCheck (1 : Fin 5) = true := by
  norm_num [CompactCertificate.coefficientCheck, intervalFinSumHull,
    compactCertificate248, rationalIntervalSubset, orderedInterval, Fin.sum_univ_succ]

theorem compactCertificate248_coefficient2 :
    compactCertificate248.coefficientCheck (2 : Fin 5) = true := by
  norm_num [CompactCertificate.coefficientCheck, intervalFinSumHull,
    compactCertificate248, rationalIntervalSubset, orderedInterval, Fin.sum_univ_succ]

theorem compactCertificate248_coefficient3 :
    compactCertificate248.coefficientCheck (3 : Fin 5) = true := by
  norm_num [CompactCertificate.coefficientCheck, intervalFinSumHull,
    compactCertificate248, rationalIntervalSubset, orderedInterval, Fin.sum_univ_succ]

theorem compactCertificate248_coefficient4 :
    compactCertificate248.coefficientCheck (4 : Fin 5) = true := by
  norm_num [CompactCertificate.coefficientCheck, intervalFinSumHull,
    compactCertificate248, rationalIntervalSubset, orderedInterval, Fin.sum_univ_succ]

theorem compactCertificate248_coefficients : ∀ r : Fin 5,
    compactCertificate248.coefficientCheck r = true := by
  intro r
  fin_cases r
  · exact compactCertificate248_coefficient0
  · exact compactCertificate248_coefficient1
  · exact compactCertificate248_coefficient2
  · exact compactCertificate248_coefficient3
  · exact compactCertificate248_coefficient4

theorem compactCertificate248_lower : (1 : ℚ) ≤ compactCertificate248.output.lo := by
  norm_num [CompactCertificate.output, CompactCertificate.interval,
    CompactCertificate.coefficientTargetNat, compactCertificate248, dualConstant,
    intervalTaylorSum, intervalPow, intervalSub, intervalMaxAbs, widenInterval,
    rationalErrorInterval, orderedInterval, IntervalRat.add, IntervalRat.mul, IntervalRat.scale,
    IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4]

theorem compactCertificate248_proves {t : ℝ} (ht : t ∈ compactCertificate248.interval) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t :=
  compactCertificate248.proves compactCertificate248_states compactCertificate248_chunks
    compactCertificate248_coefficients compactCertificate248_lower ht

end Erdos232
