/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, OpenAI Codex
-/
import ErdosProblems.Erdos232.CompactBase

open LeanCert.Core
namespace Erdos232

def compactCertificate252 : CompactCertificate where
  left := 127
  right := 128
  center := 255 / 2
  grid := fun i =>
    match i.val with
    | 0 => 41
    | 1 => 30
    | 2 => 48
    | 3 => 9
    | 4 => 23
    | 5 => 64
    | 6 => 47
    | 7 => 80
    | 8 => 59
    | 9 => 91
    | 10 => 52
    | 11 => 93
    | 12 => 87
    | 13 => 62
    | 14 => 70
    | 15 => 59
    | 16 => 52
    | 17 => 75
    | 18 => 42
    | 19 => 35
    | 20 => 22
    | 21 => 12
    | 22 => 32
    | 23 => 44
    | 24 => 19
    | 25 => 76
    | _ => 50
  point := fun i =>
    match i.val with
    | 0 => 255 / 2
    | 1 => 75132738342951 / 800000000000
    | 2 => 24296383880583 / 160000000000
    | 3 => 21923545664757 / 800000000000
    | 4 => 58889727457329 / 800000000000
    | 5 => 159897065730093 / 800000000000
    | 6 => 117779454914709 / 800000000000
    | 7 => 201817103482857 / 800000000000
    | 8 => 148657564991163 / 800000000000
    | 9 => 228078933704949 / 800000000000
    | 10 => 131681433771021 / 800000000000
    | 11 => 233671015015089 / 800000000000
    | 12 => 218325773233941 / 800000000000
    | 13 => 155807573628453 / 800000000000
    | 14 => 176669182371987 / 800000000000
    | 15 => 147288345573603 / 800000000000
    | 16 => 130133720121663 / 800000000000
    | 17 => 37717824296637 / 160000000000
    | 18 => 104329486984839 / 800000000000
    | 19 => 88441261534479 / 800000000000
    | 20 => 55342435008837 / 800000000000
    | 21 => 29763345608379 / 800000000000
    | 22 => 80813273122137 / 800000000000
    | 23 => 110343615509049 / 800000000000
    | 24 => 46657564991163 / 800000000000
    | 25 => 189660411338523 / 800000000000
    | _ => 126684365139957 / 800000000000
  state := fun i =>
    match i.val with
    | 0 => (orderedInterval (35164339482 / 1000000000000) (35164344746 / 1000000000000), orderedInterval (-61428883314 / 1000000000000) (-61428878050 / 1000000000000))
    | 1 => (orderedInterval (35975270443 / 1000000000000) (35975270444 / 1000000000000), orderedInterval (73865569819 / 1000000000000) (73865569820 / 1000000000000))
    | 2 => (orderedInterval (62407131958 / 1000000000000) (62407133576 / 1000000000000), orderedInterval (-17459158981 / 1000000000000) (-17459157363 / 1000000000000))
    | 3 => (orderedInterval (13555350203 / 1000000000000) (13555350246 / 1000000000000), orderedInterval (-152071448116 / 1000000000000) (-152071448073 / 1000000000000))
    | 4 => (orderedInterval (-78371295228 / 1000000000000) (-78371271530 / 1000000000000), orderedInterval (50593794434 / 1000000000000) (50593818133 / 1000000000000))
    | 5 => (orderedInterval (-22280028960 / 1000000000000) (-22280027990 / 1000000000000), orderedInterval (51908943100 / 1000000000000) (51908944070 / 1000000000000))
    | 6 => (orderedInterval (-22796006784 / 1000000000000) (-22796006783 / 1000000000000), orderedInterval (-61603285356 / 1000000000000) (-61603285355 / 1000000000000))
    | 7 => (orderedInterval (49608602206 / 1000000000000) (49608602994 / 1000000000000), orderedInterval (-8006114708 / 1000000000000) (-8006113920 / 1000000000000))
    | 8 => (orderedInterval (-55595542072 / 1000000000000) (-55595542071 / 1000000000000), orderedInterval (-18155928350 / 1000000000000) (-18155928349 / 1000000000000))
    | 9 => (orderedInterval (61649188 / 1000000000000) (61649190 / 1000000000000), orderedInterval (-47254527614 / 1000000000000) (-47254527612 / 1000000000000))
    | 10 => (orderedInterval (55922542120 / 1000000000000) (55922554196 / 1000000000000), orderedInterval (-27378207771 / 1000000000000) (-27378195696 / 1000000000000))
    | 11 => (orderedInterval (-30275921436 / 1000000000000) (-30275921435 / 1000000000000), orderedInterval (-35485635528 / 1000000000000) (-35485635527 / 1000000000000))
    | 12 => (orderedInterval (-17627230200 / 1000000000000) (-17627230199 / 1000000000000), orderedInterval (-44934548200 / 1000000000000) (-44934548199 / 1000000000000))
    | 13 => (orderedInterval (39614079224 / 1000000000000) (39614079225 / 1000000000000), orderedInterval (41122977093 / 1000000000000) (41122977094 / 1000000000000))
    | 14 => (orderedInterval (53173262973 / 1000000000000) (53173263485 / 1000000000000), orderedInterval (-7560984136 / 1000000000000) (-7560983623 / 1000000000000))
    | 15 => (orderedInterval (26043076621 / 1000000000000) (26043078588 / 1000000000000), orderedInterval (-52792455492 / 1000000000000) (-52792453524 / 1000000000000))
    | 16 => (orderedInterval (5558020859 / 1000000000000) (5558020861 / 1000000000000), orderedInterval (62294721662 / 1000000000000) (62294721663 / 1000000000000))
    | 17 => (orderedInterval (-40765766804 / 1000000000000) (-40765766803 / 1000000000000), orderedInterval (-32142538567 / 1000000000000) (-32142538566 / 1000000000000))
    | 18 => (orderedInterval (-47655244313 / 1000000000000) (-47655197026 / 1000000000000), orderedInterval (51276634288 / 1000000000000) (51276681575 / 1000000000000))
    | 19 => (orderedInterval (-74509318775 / 1000000000000) (-74509318773 / 1000000000000), orderedInterval (-14046473584 / 1000000000000) (-14046473582 / 1000000000000))
    | 20 => (orderedInterval (71853755508 / 1000000000000) (71853755509 / 1000000000000), orderedInterval (63038819058 / 1000000000000) (63038819059 / 1000000000000))
    | 21 => (orderedInterval (37041574048 / 1000000000000) (37041574049 / 1000000000000), orderedInterval (124964336568 / 1000000000000) (124964336569 / 1000000000000))
    | 22 => (orderedInterval (75816130303 / 1000000000000) (75816130304 / 1000000000000), orderedInterval (23161556605 / 1000000000000) (23161556606 / 1000000000000))
    | 23 => (orderedInterval (31609010155 / 1000000000000) (31609010156 / 1000000000000), orderedInterval (60022192699 / 1000000000000) (60022192700 / 1000000000000))
    | 24 => (orderedInterval (57695774376 / 1000000000000) (57695788530 / 1000000000000), orderedInterval (-87597781572 / 1000000000000) (-87597767418 / 1000000000000))
    | 25 => (orderedInterval (-40613082945 / 1000000000000) (-40612974905 / 1000000000000), orderedInterval (32270751696 / 1000000000000) (32270859736 / 1000000000000))
    | _ => (orderedInterval (55955022729 / 1000000000000) (55955039474 / 1000000000000), orderedInterval (-29996440468 / 1000000000000) (-29996423723 / 1000000000000))
  chunkTarget := fun r b =>
    match r.val with
    | 0 =>
      match b.val with
      | 0 => orderedInterval (17935254544 / 1000000000000) (17935256735 / 1000000000000)
      | 1 => orderedInterval (-1424659581 / 1000000000000) (-1424658630 / 1000000000000)
      | 2 => orderedInterval (-2873762366 / 1000000000000) (-2873762334 / 1000000000000)
      | 3 => orderedInterval (-171454776 / 1000000000000) (-171453829 / 1000000000000)
      | 4 => orderedInterval (3795159419 / 1000000000000) (3795159438 / 1000000000000)
      | 5 => orderedInterval (-1061094871 / 1000000000000) (-1061094836 / 1000000000000)
      | 6 => orderedInterval (14176148457 / 1000000000000) (14176156051 / 1000000000000)
      | 7 => orderedInterval (-4826485912 / 1000000000000) (-4826485896 / 1000000000000)
      | _ => orderedInterval (-6844872364 / 1000000000000) (-6844860306 / 1000000000000)
    | 1 =>
      match b.val with
      | 0 => orderedInterval (-25061478673 / 1000000000000) (-25061476463 / 1000000000000)
      | 1 => orderedInterval (-4363668894 / 1000000000000) (-4363668268 / 1000000000000)
      | 2 => orderedInterval (-150912362 / 1000000000000) (-150912300 / 1000000000000)
      | 3 => orderedInterval (4600106256 / 1000000000000) (4600107517 / 1000000000000)
      | 4 => orderedInterval (7742718316 / 1000000000000) (7742718346 / 1000000000000)
      | 5 => orderedInterval (-6950117408 / 1000000000000) (-6950117357 / 1000000000000)
      | 6 => orderedInterval (-6583157489 / 1000000000000) (-6583149725 / 1000000000000)
      | 7 => orderedInterval (-6065951190 / 1000000000000) (-6065951175 / 1000000000000)
      | _ => orderedInterval (1864089175 / 1000000000000) (1864109520 / 1000000000000)
    | 2 =>
      match b.val with
      | 0 => orderedInterval (-19117879022 / 1000000000000) (-19117876771 / 1000000000000)
      | 1 => orderedInterval (-2897424884 / 1000000000000) (-2897424397 / 1000000000000)
      | 2 => orderedInterval (8845416597 / 1000000000000) (8845416715 / 1000000000000)
      | 3 => orderedInterval (15700701363 / 1000000000000) (15700703091 / 1000000000000)
      | 4 => orderedInterval (-9452139180 / 1000000000000) (-9452139130 / 1000000000000)
      | 5 => orderedInterval (3513241857 / 1000000000000) (3513241932 / 1000000000000)
      | 6 => orderedInterval (-11779288081 / 1000000000000) (-11779280081 / 1000000000000)
      | 7 => orderedInterval (4020515387 / 1000000000000) (4020515402 / 1000000000000)
      | _ => orderedInterval (4677356773 / 1000000000000) (4677392278 / 1000000000000)
    | 3 =>
      match b.val with
      | 0 => orderedInterval (25952419313 / 1000000000000) (25952421591 / 1000000000000)
      | 1 => orderedInterval (13866306994 / 1000000000000) (13866307467 / 1000000000000)
      | 2 => orderedInterval (-623792437 / 1000000000000) (-623792207 / 1000000000000)
      | 3 => orderedInterval (-28984515532 / 1000000000000) (-28984513097 / 1000000000000)
      | 4 => orderedInterval (-21939549332 / 1000000000000) (-21939549248 / 1000000000000)
      | 5 => orderedInterval (14412370582 / 1000000000000) (14412370692 / 1000000000000)
      | 6 => orderedInterval (8019329925 / 1000000000000) (8019338105 / 1000000000000)
      | 7 => orderedInterval (6110494961 / 1000000000000) (6110494976 / 1000000000000)
      | _ => orderedInterval (6118926052 / 1000000000000) (6118989006 / 1000000000000)
    | _ =>
      match b.val with
      | 0 => orderedInterval (20996828928 / 1000000000000) (20996831257 / 1000000000000)
      | 1 => orderedInterval (9029021898 / 1000000000000) (9029022473 / 1000000000000)
      | 2 => orderedInterval (-29502713311 / 1000000000000) (-29502712861 / 1000000000000)
      | 3 => orderedInterval (-106853159385 / 1000000000000) (-106853155763 / 1000000000000)
      | 4 => orderedInterval (24996448826 / 1000000000000) (24996448972 / 1000000000000)
      | 5 => orderedInterval (-11958445114 / 1000000000000) (-11958444949 / 1000000000000)
      | 6 => orderedInterval (10799871088 / 1000000000000) (10799879516 / 1000000000000)
      | 7 => orderedInterval (-4096088334 / 1000000000000) (-4096088319 / 1000000000000)
      | _ => orderedInterval (14456557750 / 1000000000000) (14456671516 / 1000000000000)
  coefficientTarget := fun i =>
    match i.val with
    | 0 => orderedInterval (18704232550 / 1000000000000) (18704256393 / 1000000000000)
    | 1 => orderedInterval (-34968372269 / 1000000000000) (-34968339905 / 1000000000000)
    | 2 => orderedInterval (-6489499190 / 1000000000000) (-6489450961 / 1000000000000)
    | 3 => orderedInterval (22931990526 / 1000000000000) (22932067285 / 1000000000000)
    | _ => orderedInterval (-72131677654 / 1000000000000) (-72131548158 / 1000000000000)

theorem compactCertificate252_stateChecks0 :
    compactCertificate252.stateChecks 0 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 41 12 (255 / 2)) (orderedInterval (35164339482 / 1000000000000) (35164344746 / 1000000000000), orderedInterval (-61428883314 / 1000000000000) (-61428878050 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 30 12 (75132738342951 / 800000000000)) (orderedInterval (35975270443 / 1000000000000) (35975270444 / 1000000000000), orderedInterval (73865569819 / 1000000000000) (73865569820 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 48 12 (24296383880583 / 160000000000)) (orderedInterval (62407131958 / 1000000000000) (62407133576 / 1000000000000), orderedInterval (-17459158981 / 1000000000000) (-17459157363 / 1000000000000))) = true
  norm_num [besselStateAtRationalPoint, besselIntervalStepZero,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, besselZeroTransition,
    besselInitial, besselGridStateAt, besselGridStateBlock00, besselGridStateBlock01,
    besselGridStateBlock02, besselGridStateBlock03, besselGridStateBlock04,
    besselGridStateBlock05, besselGridStateBlock06, besselGridStateBlock07,
    besselGridStateBlock08, besselGridStateBlock09, besselGridStateBlock10,
    besselGridStateBlock11, besselGridStateBlock12, besselGridStateBlock13,
    besselGridStateBlock14, besselGridState009, besselGridState012, besselGridState019, besselGridState022, besselGridState023, besselGridState030, besselGridState032, besselGridState035, besselGridState041, besselGridState042, besselGridState044, besselGridState047, besselGridState048, besselGridState050, besselGridState052, besselGridState059, besselGridState062, besselGridState064, besselGridState070, besselGridState075, besselGridState076, besselGridState080, besselGridState087, besselGridState091, besselGridState093, besselStateSubset, linearInterval, widenInterval,
    rationalErrorInterval, rationalIntervalSubset, orderedInterval, Finset.sum_range_succ,
    IntervalRat.add, IntervalRat.mul, IntervalRat.scale, IntervalRat.singleton]

theorem compactCertificate252_stateChecks1 :
    compactCertificate252.stateChecks 3 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 9 12 (21923545664757 / 800000000000)) (orderedInterval (13555350203 / 1000000000000) (13555350246 / 1000000000000), orderedInterval (-152071448116 / 1000000000000) (-152071448073 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 23 12 (58889727457329 / 800000000000)) (orderedInterval (-78371295228 / 1000000000000) (-78371271530 / 1000000000000), orderedInterval (50593794434 / 1000000000000) (50593818133 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 64 12 (159897065730093 / 800000000000)) (orderedInterval (-22280028960 / 1000000000000) (-22280027990 / 1000000000000), orderedInterval (51908943100 / 1000000000000) (51908944070 / 1000000000000))) = true
  norm_num [besselStateAtRationalPoint, besselIntervalStepZero,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, besselZeroTransition,
    besselInitial, besselGridStateAt, besselGridStateBlock00, besselGridStateBlock01,
    besselGridStateBlock02, besselGridStateBlock03, besselGridStateBlock04,
    besselGridStateBlock05, besselGridStateBlock06, besselGridStateBlock07,
    besselGridStateBlock08, besselGridStateBlock09, besselGridStateBlock10,
    besselGridStateBlock11, besselGridStateBlock12, besselGridStateBlock13,
    besselGridStateBlock14, besselGridState009, besselGridState012, besselGridState019, besselGridState022, besselGridState023, besselGridState030, besselGridState032, besselGridState035, besselGridState041, besselGridState042, besselGridState044, besselGridState047, besselGridState048, besselGridState050, besselGridState052, besselGridState059, besselGridState062, besselGridState064, besselGridState070, besselGridState075, besselGridState076, besselGridState080, besselGridState087, besselGridState091, besselGridState093, besselStateSubset, linearInterval, widenInterval,
    rationalErrorInterval, rationalIntervalSubset, orderedInterval, Finset.sum_range_succ,
    IntervalRat.add, IntervalRat.mul, IntervalRat.scale, IntervalRat.singleton]

theorem compactCertificate252_stateChecks2 :
    compactCertificate252.stateChecks 6 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 47 12 (117779454914709 / 800000000000)) (orderedInterval (-22796006784 / 1000000000000) (-22796006783 / 1000000000000), orderedInterval (-61603285356 / 1000000000000) (-61603285355 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 80 12 (201817103482857 / 800000000000)) (orderedInterval (49608602206 / 1000000000000) (49608602994 / 1000000000000), orderedInterval (-8006114708 / 1000000000000) (-8006113920 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 59 12 (148657564991163 / 800000000000)) (orderedInterval (-55595542072 / 1000000000000) (-55595542071 / 1000000000000), orderedInterval (-18155928350 / 1000000000000) (-18155928349 / 1000000000000))) = true
  norm_num [besselStateAtRationalPoint, besselIntervalStepZero,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, besselZeroTransition,
    besselInitial, besselGridStateAt, besselGridStateBlock00, besselGridStateBlock01,
    besselGridStateBlock02, besselGridStateBlock03, besselGridStateBlock04,
    besselGridStateBlock05, besselGridStateBlock06, besselGridStateBlock07,
    besselGridStateBlock08, besselGridStateBlock09, besselGridStateBlock10,
    besselGridStateBlock11, besselGridStateBlock12, besselGridStateBlock13,
    besselGridStateBlock14, besselGridState009, besselGridState012, besselGridState019, besselGridState022, besselGridState023, besselGridState030, besselGridState032, besselGridState035, besselGridState041, besselGridState042, besselGridState044, besselGridState047, besselGridState048, besselGridState050, besselGridState052, besselGridState059, besselGridState062, besselGridState064, besselGridState070, besselGridState075, besselGridState076, besselGridState080, besselGridState087, besselGridState091, besselGridState093, besselStateSubset, linearInterval, widenInterval,
    rationalErrorInterval, rationalIntervalSubset, orderedInterval, Finset.sum_range_succ,
    IntervalRat.add, IntervalRat.mul, IntervalRat.scale, IntervalRat.singleton]

theorem compactCertificate252_stateChecks3 :
    compactCertificate252.stateChecks 9 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 91 12 (228078933704949 / 800000000000)) (orderedInterval (61649188 / 1000000000000) (61649190 / 1000000000000), orderedInterval (-47254527614 / 1000000000000) (-47254527612 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 52 12 (131681433771021 / 800000000000)) (orderedInterval (55922542120 / 1000000000000) (55922554196 / 1000000000000), orderedInterval (-27378207771 / 1000000000000) (-27378195696 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 93 12 (233671015015089 / 800000000000)) (orderedInterval (-30275921436 / 1000000000000) (-30275921435 / 1000000000000), orderedInterval (-35485635528 / 1000000000000) (-35485635527 / 1000000000000))) = true
  norm_num [besselStateAtRationalPoint, besselIntervalStepZero,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, besselZeroTransition,
    besselInitial, besselGridStateAt, besselGridStateBlock00, besselGridStateBlock01,
    besselGridStateBlock02, besselGridStateBlock03, besselGridStateBlock04,
    besselGridStateBlock05, besselGridStateBlock06, besselGridStateBlock07,
    besselGridStateBlock08, besselGridStateBlock09, besselGridStateBlock10,
    besselGridStateBlock11, besselGridStateBlock12, besselGridStateBlock13,
    besselGridStateBlock14, besselGridState009, besselGridState012, besselGridState019, besselGridState022, besselGridState023, besselGridState030, besselGridState032, besselGridState035, besselGridState041, besselGridState042, besselGridState044, besselGridState047, besselGridState048, besselGridState050, besselGridState052, besselGridState059, besselGridState062, besselGridState064, besselGridState070, besselGridState075, besselGridState076, besselGridState080, besselGridState087, besselGridState091, besselGridState093, besselStateSubset, linearInterval, widenInterval,
    rationalErrorInterval, rationalIntervalSubset, orderedInterval, Finset.sum_range_succ,
    IntervalRat.add, IntervalRat.mul, IntervalRat.scale, IntervalRat.singleton]

theorem compactCertificate252_stateChecks4 :
    compactCertificate252.stateChecks 12 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 87 12 (218325773233941 / 800000000000)) (orderedInterval (-17627230200 / 1000000000000) (-17627230199 / 1000000000000), orderedInterval (-44934548200 / 1000000000000) (-44934548199 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 62 12 (155807573628453 / 800000000000)) (orderedInterval (39614079224 / 1000000000000) (39614079225 / 1000000000000), orderedInterval (41122977093 / 1000000000000) (41122977094 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 70 12 (176669182371987 / 800000000000)) (orderedInterval (53173262973 / 1000000000000) (53173263485 / 1000000000000), orderedInterval (-7560984136 / 1000000000000) (-7560983623 / 1000000000000))) = true
  norm_num [besselStateAtRationalPoint, besselIntervalStepZero,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, besselZeroTransition,
    besselInitial, besselGridStateAt, besselGridStateBlock00, besselGridStateBlock01,
    besselGridStateBlock02, besselGridStateBlock03, besselGridStateBlock04,
    besselGridStateBlock05, besselGridStateBlock06, besselGridStateBlock07,
    besselGridStateBlock08, besselGridStateBlock09, besselGridStateBlock10,
    besselGridStateBlock11, besselGridStateBlock12, besselGridStateBlock13,
    besselGridStateBlock14, besselGridState009, besselGridState012, besselGridState019, besselGridState022, besselGridState023, besselGridState030, besselGridState032, besselGridState035, besselGridState041, besselGridState042, besselGridState044, besselGridState047, besselGridState048, besselGridState050, besselGridState052, besselGridState059, besselGridState062, besselGridState064, besselGridState070, besselGridState075, besselGridState076, besselGridState080, besselGridState087, besselGridState091, besselGridState093, besselStateSubset, linearInterval, widenInterval,
    rationalErrorInterval, rationalIntervalSubset, orderedInterval, Finset.sum_range_succ,
    IntervalRat.add, IntervalRat.mul, IntervalRat.scale, IntervalRat.singleton]

theorem compactCertificate252_stateChecks5 :
    compactCertificate252.stateChecks 15 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 59 12 (147288345573603 / 800000000000)) (orderedInterval (26043076621 / 1000000000000) (26043078588 / 1000000000000), orderedInterval (-52792455492 / 1000000000000) (-52792453524 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 52 12 (130133720121663 / 800000000000)) (orderedInterval (5558020859 / 1000000000000) (5558020861 / 1000000000000), orderedInterval (62294721662 / 1000000000000) (62294721663 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 75 12 (37717824296637 / 160000000000)) (orderedInterval (-40765766804 / 1000000000000) (-40765766803 / 1000000000000), orderedInterval (-32142538567 / 1000000000000) (-32142538566 / 1000000000000))) = true
  norm_num [besselStateAtRationalPoint, besselIntervalStepZero,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, besselZeroTransition,
    besselInitial, besselGridStateAt, besselGridStateBlock00, besselGridStateBlock01,
    besselGridStateBlock02, besselGridStateBlock03, besselGridStateBlock04,
    besselGridStateBlock05, besselGridStateBlock06, besselGridStateBlock07,
    besselGridStateBlock08, besselGridStateBlock09, besselGridStateBlock10,
    besselGridStateBlock11, besselGridStateBlock12, besselGridStateBlock13,
    besselGridStateBlock14, besselGridState009, besselGridState012, besselGridState019, besselGridState022, besselGridState023, besselGridState030, besselGridState032, besselGridState035, besselGridState041, besselGridState042, besselGridState044, besselGridState047, besselGridState048, besselGridState050, besselGridState052, besselGridState059, besselGridState062, besselGridState064, besselGridState070, besselGridState075, besselGridState076, besselGridState080, besselGridState087, besselGridState091, besselGridState093, besselStateSubset, linearInterval, widenInterval,
    rationalErrorInterval, rationalIntervalSubset, orderedInterval, Finset.sum_range_succ,
    IntervalRat.add, IntervalRat.mul, IntervalRat.scale, IntervalRat.singleton]

theorem compactCertificate252_stateChecks6 :
    compactCertificate252.stateChecks 18 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 42 12 (104329486984839 / 800000000000)) (orderedInterval (-47655244313 / 1000000000000) (-47655197026 / 1000000000000), orderedInterval (51276634288 / 1000000000000) (51276681575 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 35 12 (88441261534479 / 800000000000)) (orderedInterval (-74509318775 / 1000000000000) (-74509318773 / 1000000000000), orderedInterval (-14046473584 / 1000000000000) (-14046473582 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 22 12 (55342435008837 / 800000000000)) (orderedInterval (71853755508 / 1000000000000) (71853755509 / 1000000000000), orderedInterval (63038819058 / 1000000000000) (63038819059 / 1000000000000))) = true
  norm_num [besselStateAtRationalPoint, besselIntervalStepZero,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, besselZeroTransition,
    besselInitial, besselGridStateAt, besselGridStateBlock00, besselGridStateBlock01,
    besselGridStateBlock02, besselGridStateBlock03, besselGridStateBlock04,
    besselGridStateBlock05, besselGridStateBlock06, besselGridStateBlock07,
    besselGridStateBlock08, besselGridStateBlock09, besselGridStateBlock10,
    besselGridStateBlock11, besselGridStateBlock12, besselGridStateBlock13,
    besselGridStateBlock14, besselGridState009, besselGridState012, besselGridState019, besselGridState022, besselGridState023, besselGridState030, besselGridState032, besselGridState035, besselGridState041, besselGridState042, besselGridState044, besselGridState047, besselGridState048, besselGridState050, besselGridState052, besselGridState059, besselGridState062, besselGridState064, besselGridState070, besselGridState075, besselGridState076, besselGridState080, besselGridState087, besselGridState091, besselGridState093, besselStateSubset, linearInterval, widenInterval,
    rationalErrorInterval, rationalIntervalSubset, orderedInterval, Finset.sum_range_succ,
    IntervalRat.add, IntervalRat.mul, IntervalRat.scale, IntervalRat.singleton]

theorem compactCertificate252_stateChecks7 :
    compactCertificate252.stateChecks 21 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 12 12 (29763345608379 / 800000000000)) (orderedInterval (37041574048 / 1000000000000) (37041574049 / 1000000000000), orderedInterval (124964336568 / 1000000000000) (124964336569 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 32 12 (80813273122137 / 800000000000)) (orderedInterval (75816130303 / 1000000000000) (75816130304 / 1000000000000), orderedInterval (23161556605 / 1000000000000) (23161556606 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 44 12 (110343615509049 / 800000000000)) (orderedInterval (31609010155 / 1000000000000) (31609010156 / 1000000000000), orderedInterval (60022192699 / 1000000000000) (60022192700 / 1000000000000))) = true
  norm_num [besselStateAtRationalPoint, besselIntervalStepZero,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, besselZeroTransition,
    besselInitial, besselGridStateAt, besselGridStateBlock00, besselGridStateBlock01,
    besselGridStateBlock02, besselGridStateBlock03, besselGridStateBlock04,
    besselGridStateBlock05, besselGridStateBlock06, besselGridStateBlock07,
    besselGridStateBlock08, besselGridStateBlock09, besselGridStateBlock10,
    besselGridStateBlock11, besselGridStateBlock12, besselGridStateBlock13,
    besselGridStateBlock14, besselGridState009, besselGridState012, besselGridState019, besselGridState022, besselGridState023, besselGridState030, besselGridState032, besselGridState035, besselGridState041, besselGridState042, besselGridState044, besselGridState047, besselGridState048, besselGridState050, besselGridState052, besselGridState059, besselGridState062, besselGridState064, besselGridState070, besselGridState075, besselGridState076, besselGridState080, besselGridState087, besselGridState091, besselGridState093, besselStateSubset, linearInterval, widenInterval,
    rationalErrorInterval, rationalIntervalSubset, orderedInterval, Finset.sum_range_succ,
    IntervalRat.add, IntervalRat.mul, IntervalRat.scale, IntervalRat.singleton]

theorem compactCertificate252_stateChecks8 :
    compactCertificate252.stateChecks 24 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 19 12 (46657564991163 / 800000000000)) (orderedInterval (57695774376 / 1000000000000) (57695788530 / 1000000000000), orderedInterval (-87597781572 / 1000000000000) (-87597767418 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 76 12 (189660411338523 / 800000000000)) (orderedInterval (-40613082945 / 1000000000000) (-40612974905 / 1000000000000), orderedInterval (32270751696 / 1000000000000) (32270859736 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 50 12 (126684365139957 / 800000000000)) (orderedInterval (55955022729 / 1000000000000) (55955039474 / 1000000000000), orderedInterval (-29996440468 / 1000000000000) (-29996423723 / 1000000000000))) = true
  norm_num [besselStateAtRationalPoint, besselIntervalStepZero,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, besselZeroTransition,
    besselInitial, besselGridStateAt, besselGridStateBlock00, besselGridStateBlock01,
    besselGridStateBlock02, besselGridStateBlock03, besselGridStateBlock04,
    besselGridStateBlock05, besselGridStateBlock06, besselGridStateBlock07,
    besselGridStateBlock08, besselGridStateBlock09, besselGridStateBlock10,
    besselGridStateBlock11, besselGridStateBlock12, besselGridStateBlock13,
    besselGridStateBlock14, besselGridState009, besselGridState012, besselGridState019, besselGridState022, besselGridState023, besselGridState030, besselGridState032, besselGridState035, besselGridState041, besselGridState042, besselGridState044, besselGridState047, besselGridState048, besselGridState050, besselGridState052, besselGridState059, besselGridState062, besselGridState064, besselGridState070, besselGridState075, besselGridState076, besselGridState080, besselGridState087, besselGridState091, besselGridState093, besselStateSubset, linearInterval, widenInterval,
    rationalErrorInterval, rationalIntervalSubset, orderedInterval, Finset.sum_range_succ,
    IntervalRat.add, IntervalRat.mul, IntervalRat.scale, IntervalRat.singleton]

theorem compactCertificate252_states : ∀ j,
    BesselStateValid (compactCertificate252.point j) (compactCertificate252.state j) :=
  compactCertificate252.statesValid_of_checks3 compactCertificate252_stateChecks0
    compactCertificate252_stateChecks1 compactCertificate252_stateChecks2
    compactCertificate252_stateChecks3 compactCertificate252_stateChecks4
    compactCertificate252_stateChecks5 compactCertificate252_stateChecks6
    compactCertificate252_stateChecks7 compactCertificate252_stateChecks8

theorem compactCertificate252_chunkChecks0_0 :
    compactCertificate252.chunkChecks (0 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 0) <| besselDerivativeNearFromState (255 / 2) 0 (IntervalRat.scale (255 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (35164339482 / 1000000000000) (35164344746 / 1000000000000), orderedInterval (-61428883314 / 1000000000000) (-61428878050 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 0) <| besselDerivativeNearFromState (75132738342951 / 800000000000) 0 (IntervalRat.scale (255 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (35975270443 / 1000000000000) (35975270444 / 1000000000000), orderedInterval (73865569819 / 1000000000000) (73865569820 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 0) <| besselDerivativeNearFromState (24296383880583 / 160000000000) 0 (IntervalRat.scale (255 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (62407131958 / 1000000000000) (62407133576 / 1000000000000), orderedInterval (-17459158981 / 1000000000000) (-17459157363 / 1000000000000)))) (orderedInterval (17935254544 / 1000000000000) (17935256735 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 0) <| besselDerivativeNearFromState (21923545664757 / 800000000000) 0 (IntervalRat.scale (255 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (13555350203 / 1000000000000) (13555350246 / 1000000000000), orderedInterval (-152071448116 / 1000000000000) (-152071448073 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 0) <| besselDerivativeNearFromState (58889727457329 / 800000000000) 0 (IntervalRat.scale (255 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-78371295228 / 1000000000000) (-78371271530 / 1000000000000), orderedInterval (50593794434 / 1000000000000) (50593818133 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 0) <| besselDerivativeNearFromState (159897065730093 / 800000000000) 0 (IntervalRat.scale (255 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-22280028960 / 1000000000000) (-22280027990 / 1000000000000), orderedInterval (51908943100 / 1000000000000) (51908944070 / 1000000000000)))) (orderedInterval (-1424659581 / 1000000000000) (-1424658630 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 0) <| besselDerivativeNearFromState (117779454914709 / 800000000000) 0 (IntervalRat.scale (255 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-22796006784 / 1000000000000) (-22796006783 / 1000000000000), orderedInterval (-61603285356 / 1000000000000) (-61603285355 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 0) <| besselDerivativeNearFromState (201817103482857 / 800000000000) 0 (IntervalRat.scale (255 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (49608602206 / 1000000000000) (49608602994 / 1000000000000), orderedInterval (-8006114708 / 1000000000000) (-8006113920 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 0) <| besselDerivativeNearFromState (148657564991163 / 800000000000) 0 (IntervalRat.scale (255 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-55595542072 / 1000000000000) (-55595542071 / 1000000000000), orderedInterval (-18155928350 / 1000000000000) (-18155928349 / 1000000000000)))) (orderedInterval (-2873762366 / 1000000000000) (-2873762334 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate252_chunkChecks0_1 :
    compactCertificate252.chunkChecks (0 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 0) <| besselDerivativeNearFromState (228078933704949 / 800000000000) 0 (IntervalRat.scale (255 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (61649188 / 1000000000000) (61649190 / 1000000000000), orderedInterval (-47254527614 / 1000000000000) (-47254527612 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 0) <| besselDerivativeNearFromState (131681433771021 / 800000000000) 0 (IntervalRat.scale (255 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (55922542120 / 1000000000000) (55922554196 / 1000000000000), orderedInterval (-27378207771 / 1000000000000) (-27378195696 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 0) <| besselDerivativeNearFromState (233671015015089 / 800000000000) 0 (IntervalRat.scale (255 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-30275921436 / 1000000000000) (-30275921435 / 1000000000000), orderedInterval (-35485635528 / 1000000000000) (-35485635527 / 1000000000000)))) (orderedInterval (-171454776 / 1000000000000) (-171453829 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 0) <| besselDerivativeNearFromState (218325773233941 / 800000000000) 0 (IntervalRat.scale (255 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-17627230200 / 1000000000000) (-17627230199 / 1000000000000), orderedInterval (-44934548200 / 1000000000000) (-44934548199 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 0) <| besselDerivativeNearFromState (155807573628453 / 800000000000) 0 (IntervalRat.scale (255 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (39614079224 / 1000000000000) (39614079225 / 1000000000000), orderedInterval (41122977093 / 1000000000000) (41122977094 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 0) <| besselDerivativeNearFromState (176669182371987 / 800000000000) 0 (IntervalRat.scale (255 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (53173262973 / 1000000000000) (53173263485 / 1000000000000), orderedInterval (-7560984136 / 1000000000000) (-7560983623 / 1000000000000)))) (orderedInterval (3795159419 / 1000000000000) (3795159438 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 0) <| besselDerivativeNearFromState (147288345573603 / 800000000000) 0 (IntervalRat.scale (255 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (26043076621 / 1000000000000) (26043078588 / 1000000000000), orderedInterval (-52792455492 / 1000000000000) (-52792453524 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 0) <| besselDerivativeNearFromState (130133720121663 / 800000000000) 0 (IntervalRat.scale (255 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (5558020859 / 1000000000000) (5558020861 / 1000000000000), orderedInterval (62294721662 / 1000000000000) (62294721663 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 0) <| besselDerivativeNearFromState (37717824296637 / 160000000000) 0 (IntervalRat.scale (255 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-40765766804 / 1000000000000) (-40765766803 / 1000000000000), orderedInterval (-32142538567 / 1000000000000) (-32142538566 / 1000000000000)))) (orderedInterval (-1061094871 / 1000000000000) (-1061094836 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate252_chunkChecks0_2 :
    compactCertificate252.chunkChecks (0 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 0) <| besselDerivativeNearFromState (104329486984839 / 800000000000) 0 (IntervalRat.scale (255 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-47655244313 / 1000000000000) (-47655197026 / 1000000000000), orderedInterval (51276634288 / 1000000000000) (51276681575 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 0) <| besselDerivativeNearFromState (88441261534479 / 800000000000) 0 (IntervalRat.scale (255 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-74509318775 / 1000000000000) (-74509318773 / 1000000000000), orderedInterval (-14046473584 / 1000000000000) (-14046473582 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 0) <| besselDerivativeNearFromState (55342435008837 / 800000000000) 0 (IntervalRat.scale (255 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (71853755508 / 1000000000000) (71853755509 / 1000000000000), orderedInterval (63038819058 / 1000000000000) (63038819059 / 1000000000000)))) (orderedInterval (14176148457 / 1000000000000) (14176156051 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 0) <| besselDerivativeNearFromState (29763345608379 / 800000000000) 0 (IntervalRat.scale (255 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (37041574048 / 1000000000000) (37041574049 / 1000000000000), orderedInterval (124964336568 / 1000000000000) (124964336569 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 0) <| besselDerivativeNearFromState (80813273122137 / 800000000000) 0 (IntervalRat.scale (255 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (75816130303 / 1000000000000) (75816130304 / 1000000000000), orderedInterval (23161556605 / 1000000000000) (23161556606 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 0) <| besselDerivativeNearFromState (110343615509049 / 800000000000) 0 (IntervalRat.scale (255 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (31609010155 / 1000000000000) (31609010156 / 1000000000000), orderedInterval (60022192699 / 1000000000000) (60022192700 / 1000000000000)))) (orderedInterval (-4826485912 / 1000000000000) (-4826485896 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 0) <| besselDerivativeNearFromState (46657564991163 / 800000000000) 0 (IntervalRat.scale (255 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (57695774376 / 1000000000000) (57695788530 / 1000000000000), orderedInterval (-87597781572 / 1000000000000) (-87597767418 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 0) <| besselDerivativeNearFromState (189660411338523 / 800000000000) 0 (IntervalRat.scale (255 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-40613082945 / 1000000000000) (-40612974905 / 1000000000000), orderedInterval (32270751696 / 1000000000000) (32270859736 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 0) <| besselDerivativeNearFromState (126684365139957 / 800000000000) 0 (IntervalRat.scale (255 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (55955022729 / 1000000000000) (55955039474 / 1000000000000), orderedInterval (-29996440468 / 1000000000000) (-29996423723 / 1000000000000)))) (orderedInterval (-6844872364 / 1000000000000) (-6844860306 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate252_chunkChecks0 :
    compactCertificate252.chunkChecks (0 : Fin 5) 0 9 = true :=
  compactCertificate252.chunkChecks_nine_of_three (0 : Fin 5) compactCertificate252_chunkChecks0_0
    compactCertificate252_chunkChecks0_1 compactCertificate252_chunkChecks0_2

theorem compactCertificate252_chunkChecks1_0 :
    compactCertificate252.chunkChecks (1 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 1) <| besselDerivativeNearFromState (255 / 2) 1 (IntervalRat.scale (255 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (35164339482 / 1000000000000) (35164344746 / 1000000000000), orderedInterval (-61428883314 / 1000000000000) (-61428878050 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 1) <| besselDerivativeNearFromState (75132738342951 / 800000000000) 1 (IntervalRat.scale (255 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (35975270443 / 1000000000000) (35975270444 / 1000000000000), orderedInterval (73865569819 / 1000000000000) (73865569820 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 1) <| besselDerivativeNearFromState (24296383880583 / 160000000000) 1 (IntervalRat.scale (255 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (62407131958 / 1000000000000) (62407133576 / 1000000000000), orderedInterval (-17459158981 / 1000000000000) (-17459157363 / 1000000000000)))) (orderedInterval (-25061478673 / 1000000000000) (-25061476463 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 1) <| besselDerivativeNearFromState (21923545664757 / 800000000000) 1 (IntervalRat.scale (255 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (13555350203 / 1000000000000) (13555350246 / 1000000000000), orderedInterval (-152071448116 / 1000000000000) (-152071448073 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 1) <| besselDerivativeNearFromState (58889727457329 / 800000000000) 1 (IntervalRat.scale (255 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-78371295228 / 1000000000000) (-78371271530 / 1000000000000), orderedInterval (50593794434 / 1000000000000) (50593818133 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 1) <| besselDerivativeNearFromState (159897065730093 / 800000000000) 1 (IntervalRat.scale (255 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-22280028960 / 1000000000000) (-22280027990 / 1000000000000), orderedInterval (51908943100 / 1000000000000) (51908944070 / 1000000000000)))) (orderedInterval (-4363668894 / 1000000000000) (-4363668268 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 1) <| besselDerivativeNearFromState (117779454914709 / 800000000000) 1 (IntervalRat.scale (255 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-22796006784 / 1000000000000) (-22796006783 / 1000000000000), orderedInterval (-61603285356 / 1000000000000) (-61603285355 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 1) <| besselDerivativeNearFromState (201817103482857 / 800000000000) 1 (IntervalRat.scale (255 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (49608602206 / 1000000000000) (49608602994 / 1000000000000), orderedInterval (-8006114708 / 1000000000000) (-8006113920 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 1) <| besselDerivativeNearFromState (148657564991163 / 800000000000) 1 (IntervalRat.scale (255 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-55595542072 / 1000000000000) (-55595542071 / 1000000000000), orderedInterval (-18155928350 / 1000000000000) (-18155928349 / 1000000000000)))) (orderedInterval (-150912362 / 1000000000000) (-150912300 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate252_chunkChecks1_1 :
    compactCertificate252.chunkChecks (1 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 1) <| besselDerivativeNearFromState (228078933704949 / 800000000000) 1 (IntervalRat.scale (255 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (61649188 / 1000000000000) (61649190 / 1000000000000), orderedInterval (-47254527614 / 1000000000000) (-47254527612 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 1) <| besselDerivativeNearFromState (131681433771021 / 800000000000) 1 (IntervalRat.scale (255 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (55922542120 / 1000000000000) (55922554196 / 1000000000000), orderedInterval (-27378207771 / 1000000000000) (-27378195696 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 1) <| besselDerivativeNearFromState (233671015015089 / 800000000000) 1 (IntervalRat.scale (255 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-30275921436 / 1000000000000) (-30275921435 / 1000000000000), orderedInterval (-35485635528 / 1000000000000) (-35485635527 / 1000000000000)))) (orderedInterval (4600106256 / 1000000000000) (4600107517 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 1) <| besselDerivativeNearFromState (218325773233941 / 800000000000) 1 (IntervalRat.scale (255 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-17627230200 / 1000000000000) (-17627230199 / 1000000000000), orderedInterval (-44934548200 / 1000000000000) (-44934548199 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 1) <| besselDerivativeNearFromState (155807573628453 / 800000000000) 1 (IntervalRat.scale (255 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (39614079224 / 1000000000000) (39614079225 / 1000000000000), orderedInterval (41122977093 / 1000000000000) (41122977094 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 1) <| besselDerivativeNearFromState (176669182371987 / 800000000000) 1 (IntervalRat.scale (255 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (53173262973 / 1000000000000) (53173263485 / 1000000000000), orderedInterval (-7560984136 / 1000000000000) (-7560983623 / 1000000000000)))) (orderedInterval (7742718316 / 1000000000000) (7742718346 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 1) <| besselDerivativeNearFromState (147288345573603 / 800000000000) 1 (IntervalRat.scale (255 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (26043076621 / 1000000000000) (26043078588 / 1000000000000), orderedInterval (-52792455492 / 1000000000000) (-52792453524 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 1) <| besselDerivativeNearFromState (130133720121663 / 800000000000) 1 (IntervalRat.scale (255 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (5558020859 / 1000000000000) (5558020861 / 1000000000000), orderedInterval (62294721662 / 1000000000000) (62294721663 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 1) <| besselDerivativeNearFromState (37717824296637 / 160000000000) 1 (IntervalRat.scale (255 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-40765766804 / 1000000000000) (-40765766803 / 1000000000000), orderedInterval (-32142538567 / 1000000000000) (-32142538566 / 1000000000000)))) (orderedInterval (-6950117408 / 1000000000000) (-6950117357 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate252_chunkChecks1_2 :
    compactCertificate252.chunkChecks (1 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 1) <| besselDerivativeNearFromState (104329486984839 / 800000000000) 1 (IntervalRat.scale (255 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-47655244313 / 1000000000000) (-47655197026 / 1000000000000), orderedInterval (51276634288 / 1000000000000) (51276681575 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 1) <| besselDerivativeNearFromState (88441261534479 / 800000000000) 1 (IntervalRat.scale (255 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-74509318775 / 1000000000000) (-74509318773 / 1000000000000), orderedInterval (-14046473584 / 1000000000000) (-14046473582 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 1) <| besselDerivativeNearFromState (55342435008837 / 800000000000) 1 (IntervalRat.scale (255 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (71853755508 / 1000000000000) (71853755509 / 1000000000000), orderedInterval (63038819058 / 1000000000000) (63038819059 / 1000000000000)))) (orderedInterval (-6583157489 / 1000000000000) (-6583149725 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 1) <| besselDerivativeNearFromState (29763345608379 / 800000000000) 1 (IntervalRat.scale (255 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (37041574048 / 1000000000000) (37041574049 / 1000000000000), orderedInterval (124964336568 / 1000000000000) (124964336569 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 1) <| besselDerivativeNearFromState (80813273122137 / 800000000000) 1 (IntervalRat.scale (255 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (75816130303 / 1000000000000) (75816130304 / 1000000000000), orderedInterval (23161556605 / 1000000000000) (23161556606 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 1) <| besselDerivativeNearFromState (110343615509049 / 800000000000) 1 (IntervalRat.scale (255 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (31609010155 / 1000000000000) (31609010156 / 1000000000000), orderedInterval (60022192699 / 1000000000000) (60022192700 / 1000000000000)))) (orderedInterval (-6065951190 / 1000000000000) (-6065951175 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 1) <| besselDerivativeNearFromState (46657564991163 / 800000000000) 1 (IntervalRat.scale (255 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (57695774376 / 1000000000000) (57695788530 / 1000000000000), orderedInterval (-87597781572 / 1000000000000) (-87597767418 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 1) <| besselDerivativeNearFromState (189660411338523 / 800000000000) 1 (IntervalRat.scale (255 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-40613082945 / 1000000000000) (-40612974905 / 1000000000000), orderedInterval (32270751696 / 1000000000000) (32270859736 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 1) <| besselDerivativeNearFromState (126684365139957 / 800000000000) 1 (IntervalRat.scale (255 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (55955022729 / 1000000000000) (55955039474 / 1000000000000), orderedInterval (-29996440468 / 1000000000000) (-29996423723 / 1000000000000)))) (orderedInterval (1864089175 / 1000000000000) (1864109520 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate252_chunkChecks1 :
    compactCertificate252.chunkChecks (1 : Fin 5) 0 9 = true :=
  compactCertificate252.chunkChecks_nine_of_three (1 : Fin 5) compactCertificate252_chunkChecks1_0
    compactCertificate252_chunkChecks1_1 compactCertificate252_chunkChecks1_2

theorem compactCertificate252_chunkChecks2_0 :
    compactCertificate252.chunkChecks (2 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 2) <| besselDerivativeNearFromState (255 / 2) 2 (IntervalRat.scale (255 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (35164339482 / 1000000000000) (35164344746 / 1000000000000), orderedInterval (-61428883314 / 1000000000000) (-61428878050 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 2) <| besselDerivativeNearFromState (75132738342951 / 800000000000) 2 (IntervalRat.scale (255 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (35975270443 / 1000000000000) (35975270444 / 1000000000000), orderedInterval (73865569819 / 1000000000000) (73865569820 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 2) <| besselDerivativeNearFromState (24296383880583 / 160000000000) 2 (IntervalRat.scale (255 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (62407131958 / 1000000000000) (62407133576 / 1000000000000), orderedInterval (-17459158981 / 1000000000000) (-17459157363 / 1000000000000)))) (orderedInterval (-19117879022 / 1000000000000) (-19117876771 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 2) <| besselDerivativeNearFromState (21923545664757 / 800000000000) 2 (IntervalRat.scale (255 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (13555350203 / 1000000000000) (13555350246 / 1000000000000), orderedInterval (-152071448116 / 1000000000000) (-152071448073 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 2) <| besselDerivativeNearFromState (58889727457329 / 800000000000) 2 (IntervalRat.scale (255 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-78371295228 / 1000000000000) (-78371271530 / 1000000000000), orderedInterval (50593794434 / 1000000000000) (50593818133 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 2) <| besselDerivativeNearFromState (159897065730093 / 800000000000) 2 (IntervalRat.scale (255 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-22280028960 / 1000000000000) (-22280027990 / 1000000000000), orderedInterval (51908943100 / 1000000000000) (51908944070 / 1000000000000)))) (orderedInterval (-2897424884 / 1000000000000) (-2897424397 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 2) <| besselDerivativeNearFromState (117779454914709 / 800000000000) 2 (IntervalRat.scale (255 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-22796006784 / 1000000000000) (-22796006783 / 1000000000000), orderedInterval (-61603285356 / 1000000000000) (-61603285355 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 2) <| besselDerivativeNearFromState (201817103482857 / 800000000000) 2 (IntervalRat.scale (255 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (49608602206 / 1000000000000) (49608602994 / 1000000000000), orderedInterval (-8006114708 / 1000000000000) (-8006113920 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 2) <| besselDerivativeNearFromState (148657564991163 / 800000000000) 2 (IntervalRat.scale (255 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-55595542072 / 1000000000000) (-55595542071 / 1000000000000), orderedInterval (-18155928350 / 1000000000000) (-18155928349 / 1000000000000)))) (orderedInterval (8845416597 / 1000000000000) (8845416715 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate252_chunkChecks2_1 :
    compactCertificate252.chunkChecks (2 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 2) <| besselDerivativeNearFromState (228078933704949 / 800000000000) 2 (IntervalRat.scale (255 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (61649188 / 1000000000000) (61649190 / 1000000000000), orderedInterval (-47254527614 / 1000000000000) (-47254527612 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 2) <| besselDerivativeNearFromState (131681433771021 / 800000000000) 2 (IntervalRat.scale (255 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (55922542120 / 1000000000000) (55922554196 / 1000000000000), orderedInterval (-27378207771 / 1000000000000) (-27378195696 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 2) <| besselDerivativeNearFromState (233671015015089 / 800000000000) 2 (IntervalRat.scale (255 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-30275921436 / 1000000000000) (-30275921435 / 1000000000000), orderedInterval (-35485635528 / 1000000000000) (-35485635527 / 1000000000000)))) (orderedInterval (15700701363 / 1000000000000) (15700703091 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 2) <| besselDerivativeNearFromState (218325773233941 / 800000000000) 2 (IntervalRat.scale (255 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-17627230200 / 1000000000000) (-17627230199 / 1000000000000), orderedInterval (-44934548200 / 1000000000000) (-44934548199 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 2) <| besselDerivativeNearFromState (155807573628453 / 800000000000) 2 (IntervalRat.scale (255 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (39614079224 / 1000000000000) (39614079225 / 1000000000000), orderedInterval (41122977093 / 1000000000000) (41122977094 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 2) <| besselDerivativeNearFromState (176669182371987 / 800000000000) 2 (IntervalRat.scale (255 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (53173262973 / 1000000000000) (53173263485 / 1000000000000), orderedInterval (-7560984136 / 1000000000000) (-7560983623 / 1000000000000)))) (orderedInterval (-9452139180 / 1000000000000) (-9452139130 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 2) <| besselDerivativeNearFromState (147288345573603 / 800000000000) 2 (IntervalRat.scale (255 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (26043076621 / 1000000000000) (26043078588 / 1000000000000), orderedInterval (-52792455492 / 1000000000000) (-52792453524 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 2) <| besselDerivativeNearFromState (130133720121663 / 800000000000) 2 (IntervalRat.scale (255 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (5558020859 / 1000000000000) (5558020861 / 1000000000000), orderedInterval (62294721662 / 1000000000000) (62294721663 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 2) <| besselDerivativeNearFromState (37717824296637 / 160000000000) 2 (IntervalRat.scale (255 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-40765766804 / 1000000000000) (-40765766803 / 1000000000000), orderedInterval (-32142538567 / 1000000000000) (-32142538566 / 1000000000000)))) (orderedInterval (3513241857 / 1000000000000) (3513241932 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate252_chunkChecks2_2 :
    compactCertificate252.chunkChecks (2 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 2) <| besselDerivativeNearFromState (104329486984839 / 800000000000) 2 (IntervalRat.scale (255 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-47655244313 / 1000000000000) (-47655197026 / 1000000000000), orderedInterval (51276634288 / 1000000000000) (51276681575 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 2) <| besselDerivativeNearFromState (88441261534479 / 800000000000) 2 (IntervalRat.scale (255 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-74509318775 / 1000000000000) (-74509318773 / 1000000000000), orderedInterval (-14046473584 / 1000000000000) (-14046473582 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 2) <| besselDerivativeNearFromState (55342435008837 / 800000000000) 2 (IntervalRat.scale (255 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (71853755508 / 1000000000000) (71853755509 / 1000000000000), orderedInterval (63038819058 / 1000000000000) (63038819059 / 1000000000000)))) (orderedInterval (-11779288081 / 1000000000000) (-11779280081 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 2) <| besselDerivativeNearFromState (29763345608379 / 800000000000) 2 (IntervalRat.scale (255 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (37041574048 / 1000000000000) (37041574049 / 1000000000000), orderedInterval (124964336568 / 1000000000000) (124964336569 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 2) <| besselDerivativeNearFromState (80813273122137 / 800000000000) 2 (IntervalRat.scale (255 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (75816130303 / 1000000000000) (75816130304 / 1000000000000), orderedInterval (23161556605 / 1000000000000) (23161556606 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 2) <| besselDerivativeNearFromState (110343615509049 / 800000000000) 2 (IntervalRat.scale (255 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (31609010155 / 1000000000000) (31609010156 / 1000000000000), orderedInterval (60022192699 / 1000000000000) (60022192700 / 1000000000000)))) (orderedInterval (4020515387 / 1000000000000) (4020515402 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 2) <| besselDerivativeNearFromState (46657564991163 / 800000000000) 2 (IntervalRat.scale (255 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (57695774376 / 1000000000000) (57695788530 / 1000000000000), orderedInterval (-87597781572 / 1000000000000) (-87597767418 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 2) <| besselDerivativeNearFromState (189660411338523 / 800000000000) 2 (IntervalRat.scale (255 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-40613082945 / 1000000000000) (-40612974905 / 1000000000000), orderedInterval (32270751696 / 1000000000000) (32270859736 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 2) <| besselDerivativeNearFromState (126684365139957 / 800000000000) 2 (IntervalRat.scale (255 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (55955022729 / 1000000000000) (55955039474 / 1000000000000), orderedInterval (-29996440468 / 1000000000000) (-29996423723 / 1000000000000)))) (orderedInterval (4677356773 / 1000000000000) (4677392278 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate252_chunkChecks2 :
    compactCertificate252.chunkChecks (2 : Fin 5) 0 9 = true :=
  compactCertificate252.chunkChecks_nine_of_three (2 : Fin 5) compactCertificate252_chunkChecks2_0
    compactCertificate252_chunkChecks2_1 compactCertificate252_chunkChecks2_2

theorem compactCertificate252_chunkChecks3_0 :
    compactCertificate252.chunkChecks (3 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 3) <| besselDerivativeNearFromState (255 / 2) 3 (IntervalRat.scale (255 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (35164339482 / 1000000000000) (35164344746 / 1000000000000), orderedInterval (-61428883314 / 1000000000000) (-61428878050 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 3) <| besselDerivativeNearFromState (75132738342951 / 800000000000) 3 (IntervalRat.scale (255 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (35975270443 / 1000000000000) (35975270444 / 1000000000000), orderedInterval (73865569819 / 1000000000000) (73865569820 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 3) <| besselDerivativeNearFromState (24296383880583 / 160000000000) 3 (IntervalRat.scale (255 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (62407131958 / 1000000000000) (62407133576 / 1000000000000), orderedInterval (-17459158981 / 1000000000000) (-17459157363 / 1000000000000)))) (orderedInterval (25952419313 / 1000000000000) (25952421591 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 3) <| besselDerivativeNearFromState (21923545664757 / 800000000000) 3 (IntervalRat.scale (255 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (13555350203 / 1000000000000) (13555350246 / 1000000000000), orderedInterval (-152071448116 / 1000000000000) (-152071448073 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 3) <| besselDerivativeNearFromState (58889727457329 / 800000000000) 3 (IntervalRat.scale (255 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-78371295228 / 1000000000000) (-78371271530 / 1000000000000), orderedInterval (50593794434 / 1000000000000) (50593818133 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 3) <| besselDerivativeNearFromState (159897065730093 / 800000000000) 3 (IntervalRat.scale (255 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-22280028960 / 1000000000000) (-22280027990 / 1000000000000), orderedInterval (51908943100 / 1000000000000) (51908944070 / 1000000000000)))) (orderedInterval (13866306994 / 1000000000000) (13866307467 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 3) <| besselDerivativeNearFromState (117779454914709 / 800000000000) 3 (IntervalRat.scale (255 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-22796006784 / 1000000000000) (-22796006783 / 1000000000000), orderedInterval (-61603285356 / 1000000000000) (-61603285355 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 3) <| besselDerivativeNearFromState (201817103482857 / 800000000000) 3 (IntervalRat.scale (255 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (49608602206 / 1000000000000) (49608602994 / 1000000000000), orderedInterval (-8006114708 / 1000000000000) (-8006113920 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 3) <| besselDerivativeNearFromState (148657564991163 / 800000000000) 3 (IntervalRat.scale (255 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-55595542072 / 1000000000000) (-55595542071 / 1000000000000), orderedInterval (-18155928350 / 1000000000000) (-18155928349 / 1000000000000)))) (orderedInterval (-623792437 / 1000000000000) (-623792207 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate252_chunkChecks3_1 :
    compactCertificate252.chunkChecks (3 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 3) <| besselDerivativeNearFromState (228078933704949 / 800000000000) 3 (IntervalRat.scale (255 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (61649188 / 1000000000000) (61649190 / 1000000000000), orderedInterval (-47254527614 / 1000000000000) (-47254527612 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 3) <| besselDerivativeNearFromState (131681433771021 / 800000000000) 3 (IntervalRat.scale (255 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (55922542120 / 1000000000000) (55922554196 / 1000000000000), orderedInterval (-27378207771 / 1000000000000) (-27378195696 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 3) <| besselDerivativeNearFromState (233671015015089 / 800000000000) 3 (IntervalRat.scale (255 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-30275921436 / 1000000000000) (-30275921435 / 1000000000000), orderedInterval (-35485635528 / 1000000000000) (-35485635527 / 1000000000000)))) (orderedInterval (-28984515532 / 1000000000000) (-28984513097 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 3) <| besselDerivativeNearFromState (218325773233941 / 800000000000) 3 (IntervalRat.scale (255 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-17627230200 / 1000000000000) (-17627230199 / 1000000000000), orderedInterval (-44934548200 / 1000000000000) (-44934548199 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 3) <| besselDerivativeNearFromState (155807573628453 / 800000000000) 3 (IntervalRat.scale (255 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (39614079224 / 1000000000000) (39614079225 / 1000000000000), orderedInterval (41122977093 / 1000000000000) (41122977094 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 3) <| besselDerivativeNearFromState (176669182371987 / 800000000000) 3 (IntervalRat.scale (255 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (53173262973 / 1000000000000) (53173263485 / 1000000000000), orderedInterval (-7560984136 / 1000000000000) (-7560983623 / 1000000000000)))) (orderedInterval (-21939549332 / 1000000000000) (-21939549248 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 3) <| besselDerivativeNearFromState (147288345573603 / 800000000000) 3 (IntervalRat.scale (255 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (26043076621 / 1000000000000) (26043078588 / 1000000000000), orderedInterval (-52792455492 / 1000000000000) (-52792453524 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 3) <| besselDerivativeNearFromState (130133720121663 / 800000000000) 3 (IntervalRat.scale (255 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (5558020859 / 1000000000000) (5558020861 / 1000000000000), orderedInterval (62294721662 / 1000000000000) (62294721663 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 3) <| besselDerivativeNearFromState (37717824296637 / 160000000000) 3 (IntervalRat.scale (255 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-40765766804 / 1000000000000) (-40765766803 / 1000000000000), orderedInterval (-32142538567 / 1000000000000) (-32142538566 / 1000000000000)))) (orderedInterval (14412370582 / 1000000000000) (14412370692 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate252_chunkChecks3_2 :
    compactCertificate252.chunkChecks (3 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 3) <| besselDerivativeNearFromState (104329486984839 / 800000000000) 3 (IntervalRat.scale (255 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-47655244313 / 1000000000000) (-47655197026 / 1000000000000), orderedInterval (51276634288 / 1000000000000) (51276681575 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 3) <| besselDerivativeNearFromState (88441261534479 / 800000000000) 3 (IntervalRat.scale (255 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-74509318775 / 1000000000000) (-74509318773 / 1000000000000), orderedInterval (-14046473584 / 1000000000000) (-14046473582 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 3) <| besselDerivativeNearFromState (55342435008837 / 800000000000) 3 (IntervalRat.scale (255 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (71853755508 / 1000000000000) (71853755509 / 1000000000000), orderedInterval (63038819058 / 1000000000000) (63038819059 / 1000000000000)))) (orderedInterval (8019329925 / 1000000000000) (8019338105 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 3) <| besselDerivativeNearFromState (29763345608379 / 800000000000) 3 (IntervalRat.scale (255 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (37041574048 / 1000000000000) (37041574049 / 1000000000000), orderedInterval (124964336568 / 1000000000000) (124964336569 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 3) <| besselDerivativeNearFromState (80813273122137 / 800000000000) 3 (IntervalRat.scale (255 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (75816130303 / 1000000000000) (75816130304 / 1000000000000), orderedInterval (23161556605 / 1000000000000) (23161556606 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 3) <| besselDerivativeNearFromState (110343615509049 / 800000000000) 3 (IntervalRat.scale (255 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (31609010155 / 1000000000000) (31609010156 / 1000000000000), orderedInterval (60022192699 / 1000000000000) (60022192700 / 1000000000000)))) (orderedInterval (6110494961 / 1000000000000) (6110494976 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 3) <| besselDerivativeNearFromState (46657564991163 / 800000000000) 3 (IntervalRat.scale (255 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (57695774376 / 1000000000000) (57695788530 / 1000000000000), orderedInterval (-87597781572 / 1000000000000) (-87597767418 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 3) <| besselDerivativeNearFromState (189660411338523 / 800000000000) 3 (IntervalRat.scale (255 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-40613082945 / 1000000000000) (-40612974905 / 1000000000000), orderedInterval (32270751696 / 1000000000000) (32270859736 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 3) <| besselDerivativeNearFromState (126684365139957 / 800000000000) 3 (IntervalRat.scale (255 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (55955022729 / 1000000000000) (55955039474 / 1000000000000), orderedInterval (-29996440468 / 1000000000000) (-29996423723 / 1000000000000)))) (orderedInterval (6118926052 / 1000000000000) (6118989006 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate252_chunkChecks3 :
    compactCertificate252.chunkChecks (3 : Fin 5) 0 9 = true :=
  compactCertificate252.chunkChecks_nine_of_three (3 : Fin 5) compactCertificate252_chunkChecks3_0
    compactCertificate252_chunkChecks3_1 compactCertificate252_chunkChecks3_2

theorem compactCertificate252_chunkChecks4_0 :
    compactCertificate252.chunkChecks (4 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 4) <| besselDerivativeNearFromState (255 / 2) 4 (IntervalRat.scale (255 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (35164339482 / 1000000000000) (35164344746 / 1000000000000), orderedInterval (-61428883314 / 1000000000000) (-61428878050 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 4) <| besselDerivativeNearFromState (75132738342951 / 800000000000) 4 (IntervalRat.scale (255 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (35975270443 / 1000000000000) (35975270444 / 1000000000000), orderedInterval (73865569819 / 1000000000000) (73865569820 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 4) <| besselDerivativeNearFromState (24296383880583 / 160000000000) 4 (IntervalRat.scale (255 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (62407131958 / 1000000000000) (62407133576 / 1000000000000), orderedInterval (-17459158981 / 1000000000000) (-17459157363 / 1000000000000)))) (orderedInterval (20996828928 / 1000000000000) (20996831257 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 4) <| besselDerivativeNearFromState (21923545664757 / 800000000000) 4 (IntervalRat.scale (255 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (13555350203 / 1000000000000) (13555350246 / 1000000000000), orderedInterval (-152071448116 / 1000000000000) (-152071448073 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 4) <| besselDerivativeNearFromState (58889727457329 / 800000000000) 4 (IntervalRat.scale (255 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-78371295228 / 1000000000000) (-78371271530 / 1000000000000), orderedInterval (50593794434 / 1000000000000) (50593818133 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 4) <| besselDerivativeNearFromState (159897065730093 / 800000000000) 4 (IntervalRat.scale (255 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-22280028960 / 1000000000000) (-22280027990 / 1000000000000), orderedInterval (51908943100 / 1000000000000) (51908944070 / 1000000000000)))) (orderedInterval (9029021898 / 1000000000000) (9029022473 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 4) <| besselDerivativeNearFromState (117779454914709 / 800000000000) 4 (IntervalRat.scale (255 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-22796006784 / 1000000000000) (-22796006783 / 1000000000000), orderedInterval (-61603285356 / 1000000000000) (-61603285355 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 4) <| besselDerivativeNearFromState (201817103482857 / 800000000000) 4 (IntervalRat.scale (255 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (49608602206 / 1000000000000) (49608602994 / 1000000000000), orderedInterval (-8006114708 / 1000000000000) (-8006113920 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 4) <| besselDerivativeNearFromState (148657564991163 / 800000000000) 4 (IntervalRat.scale (255 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-55595542072 / 1000000000000) (-55595542071 / 1000000000000), orderedInterval (-18155928350 / 1000000000000) (-18155928349 / 1000000000000)))) (orderedInterval (-29502713311 / 1000000000000) (-29502712861 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate252_chunkChecks4_1 :
    compactCertificate252.chunkChecks (4 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 4) <| besselDerivativeNearFromState (228078933704949 / 800000000000) 4 (IntervalRat.scale (255 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (61649188 / 1000000000000) (61649190 / 1000000000000), orderedInterval (-47254527614 / 1000000000000) (-47254527612 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 4) <| besselDerivativeNearFromState (131681433771021 / 800000000000) 4 (IntervalRat.scale (255 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (55922542120 / 1000000000000) (55922554196 / 1000000000000), orderedInterval (-27378207771 / 1000000000000) (-27378195696 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 4) <| besselDerivativeNearFromState (233671015015089 / 800000000000) 4 (IntervalRat.scale (255 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-30275921436 / 1000000000000) (-30275921435 / 1000000000000), orderedInterval (-35485635528 / 1000000000000) (-35485635527 / 1000000000000)))) (orderedInterval (-106853159385 / 1000000000000) (-106853155763 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 4) <| besselDerivativeNearFromState (218325773233941 / 800000000000) 4 (IntervalRat.scale (255 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-17627230200 / 1000000000000) (-17627230199 / 1000000000000), orderedInterval (-44934548200 / 1000000000000) (-44934548199 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 4) <| besselDerivativeNearFromState (155807573628453 / 800000000000) 4 (IntervalRat.scale (255 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (39614079224 / 1000000000000) (39614079225 / 1000000000000), orderedInterval (41122977093 / 1000000000000) (41122977094 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 4) <| besselDerivativeNearFromState (176669182371987 / 800000000000) 4 (IntervalRat.scale (255 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (53173262973 / 1000000000000) (53173263485 / 1000000000000), orderedInterval (-7560984136 / 1000000000000) (-7560983623 / 1000000000000)))) (orderedInterval (24996448826 / 1000000000000) (24996448972 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 4) <| besselDerivativeNearFromState (147288345573603 / 800000000000) 4 (IntervalRat.scale (255 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (26043076621 / 1000000000000) (26043078588 / 1000000000000), orderedInterval (-52792455492 / 1000000000000) (-52792453524 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 4) <| besselDerivativeNearFromState (130133720121663 / 800000000000) 4 (IntervalRat.scale (255 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (5558020859 / 1000000000000) (5558020861 / 1000000000000), orderedInterval (62294721662 / 1000000000000) (62294721663 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 4) <| besselDerivativeNearFromState (37717824296637 / 160000000000) 4 (IntervalRat.scale (255 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-40765766804 / 1000000000000) (-40765766803 / 1000000000000), orderedInterval (-32142538567 / 1000000000000) (-32142538566 / 1000000000000)))) (orderedInterval (-11958445114 / 1000000000000) (-11958444949 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate252_chunkChecks4_2 :
    compactCertificate252.chunkChecks (4 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 4) <| besselDerivativeNearFromState (104329486984839 / 800000000000) 4 (IntervalRat.scale (255 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-47655244313 / 1000000000000) (-47655197026 / 1000000000000), orderedInterval (51276634288 / 1000000000000) (51276681575 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 4) <| besselDerivativeNearFromState (88441261534479 / 800000000000) 4 (IntervalRat.scale (255 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-74509318775 / 1000000000000) (-74509318773 / 1000000000000), orderedInterval (-14046473584 / 1000000000000) (-14046473582 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 4) <| besselDerivativeNearFromState (55342435008837 / 800000000000) 4 (IntervalRat.scale (255 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (71853755508 / 1000000000000) (71853755509 / 1000000000000), orderedInterval (63038819058 / 1000000000000) (63038819059 / 1000000000000)))) (orderedInterval (10799871088 / 1000000000000) (10799879516 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 4) <| besselDerivativeNearFromState (29763345608379 / 800000000000) 4 (IntervalRat.scale (255 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (37041574048 / 1000000000000) (37041574049 / 1000000000000), orderedInterval (124964336568 / 1000000000000) (124964336569 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 4) <| besselDerivativeNearFromState (80813273122137 / 800000000000) 4 (IntervalRat.scale (255 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (75816130303 / 1000000000000) (75816130304 / 1000000000000), orderedInterval (23161556605 / 1000000000000) (23161556606 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 4) <| besselDerivativeNearFromState (110343615509049 / 800000000000) 4 (IntervalRat.scale (255 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (31609010155 / 1000000000000) (31609010156 / 1000000000000), orderedInterval (60022192699 / 1000000000000) (60022192700 / 1000000000000)))) (orderedInterval (-4096088334 / 1000000000000) (-4096088319 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 4) <| besselDerivativeNearFromState (46657564991163 / 800000000000) 4 (IntervalRat.scale (255 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (57695774376 / 1000000000000) (57695788530 / 1000000000000), orderedInterval (-87597781572 / 1000000000000) (-87597767418 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 4) <| besselDerivativeNearFromState (189660411338523 / 800000000000) 4 (IntervalRat.scale (255 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-40613082945 / 1000000000000) (-40612974905 / 1000000000000), orderedInterval (32270751696 / 1000000000000) (32270859736 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 4) <| besselDerivativeNearFromState (126684365139957 / 800000000000) 4 (IntervalRat.scale (255 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (55955022729 / 1000000000000) (55955039474 / 1000000000000), orderedInterval (-29996440468 / 1000000000000) (-29996423723 / 1000000000000)))) (orderedInterval (14456557750 / 1000000000000) (14456671516 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate252_chunkChecks4 :
    compactCertificate252.chunkChecks (4 : Fin 5) 0 9 = true :=
  compactCertificate252.chunkChecks_nine_of_three (4 : Fin 5) compactCertificate252_chunkChecks4_0
    compactCertificate252_chunkChecks4_1 compactCertificate252_chunkChecks4_2

theorem compactCertificate252_chunks :
    ∀ r : Fin 5, ∀ b, compactCertificate252.chunkCheck r b = true :=
  compactCertificate252.chunkChecks_all (by
    intro r
    fin_cases r
    · exact compactCertificate252_chunkChecks0
    · exact compactCertificate252_chunkChecks1
    · exact compactCertificate252_chunkChecks2
    · exact compactCertificate252_chunkChecks3
    · exact compactCertificate252_chunkChecks4)

theorem compactCertificate252_coefficient0 :
    compactCertificate252.coefficientCheck (0 : Fin 5) = true := by
  norm_num [CompactCertificate.coefficientCheck, intervalFinSumHull,
    compactCertificate252, rationalIntervalSubset, orderedInterval, Fin.sum_univ_succ]

theorem compactCertificate252_coefficient1 :
    compactCertificate252.coefficientCheck (1 : Fin 5) = true := by
  norm_num [CompactCertificate.coefficientCheck, intervalFinSumHull,
    compactCertificate252, rationalIntervalSubset, orderedInterval, Fin.sum_univ_succ]

theorem compactCertificate252_coefficient2 :
    compactCertificate252.coefficientCheck (2 : Fin 5) = true := by
  norm_num [CompactCertificate.coefficientCheck, intervalFinSumHull,
    compactCertificate252, rationalIntervalSubset, orderedInterval, Fin.sum_univ_succ]

theorem compactCertificate252_coefficient3 :
    compactCertificate252.coefficientCheck (3 : Fin 5) = true := by
  norm_num [CompactCertificate.coefficientCheck, intervalFinSumHull,
    compactCertificate252, rationalIntervalSubset, orderedInterval, Fin.sum_univ_succ]

theorem compactCertificate252_coefficient4 :
    compactCertificate252.coefficientCheck (4 : Fin 5) = true := by
  norm_num [CompactCertificate.coefficientCheck, intervalFinSumHull,
    compactCertificate252, rationalIntervalSubset, orderedInterval, Fin.sum_univ_succ]

theorem compactCertificate252_coefficients : ∀ r : Fin 5,
    compactCertificate252.coefficientCheck r = true := by
  intro r
  fin_cases r
  · exact compactCertificate252_coefficient0
  · exact compactCertificate252_coefficient1
  · exact compactCertificate252_coefficient2
  · exact compactCertificate252_coefficient3
  · exact compactCertificate252_coefficient4

theorem compactCertificate252_lower : (1 : ℚ) ≤ compactCertificate252.output.lo := by
  norm_num [CompactCertificate.output, CompactCertificate.interval,
    CompactCertificate.coefficientTargetNat, compactCertificate252, dualConstant,
    intervalTaylorSum, intervalPow, intervalSub, intervalMaxAbs, widenInterval,
    rationalErrorInterval, orderedInterval, IntervalRat.add, IntervalRat.mul, IntervalRat.scale,
    IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4]

theorem compactCertificate252_proves {t : ℝ} (ht : t ∈ compactCertificate252.interval) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t :=
  compactCertificate252.proves compactCertificate252_states compactCertificate252_chunks
    compactCertificate252_coefficients compactCertificate252_lower ht

end Erdos232
