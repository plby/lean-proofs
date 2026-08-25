/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, OpenAI Codex
-/
import ErdosProblems.Erdos232.CompactBase

open LeanCert.Core
namespace Erdos232

def compactCertificate275 : CompactCertificate where
  left := 149
  right := 150
  center := 299 / 2
  grid := fun i =>
    match i.val with
    | 0 => 48
    | 1 => 35
    | 2 => 57
    | 3 => 10
    | 4 => 27
    | 5 => 75
    | 6 => 55
    | 7 => 94
    | 8 => 69
    | 9 => 106
    | 10 => 61
    | 11 => 109
    | 12 => 102
    | 13 => 73
    | 14 => 82
    | 15 => 69
    | 16 => 61
    | 17 => 88
    | 18 => 49
    | 19 => 41
    | 20 => 26
    | 21 => 14
    | 22 => 38
    | 23 => 52
    | 24 => 22
    | 25 => 89
    | _ => 59
  point := fun i =>
    match i.val with
    | 0 => 299 / 2
    | 1 => 440484093422399 / 4000000000000
    | 2 => 142443505495967 / 800000000000
    | 3 => 128532159877693 / 4000000000000
    | 4 => 345255460975321 / 4000000000000
    | 5 => 937435738299957 / 4000000000000
    | 6 => 690510921950941 / 4000000000000
    | 7 => 1183202234144593 / 4000000000000
    | 8 => 871541410438387 / 4000000000000
    | 9 => 1337168650544701 / 4000000000000
    | 10 => 772014680343829 / 4000000000000
    | 11 => 1369953597833561 / 4000000000000
    | 12 => 1279988356802909 / 4000000000000
    | 13 => 913460088527597 / 4000000000000
    | 14 => 1035766382925963 / 4000000000000
    | 15 => 863514026009947 / 4000000000000
    | 16 => 762940829732887 / 4000000000000
    | 17 => 221129989503813 / 800000000000
    | 18 => 611657188401311 / 4000000000000
    | 19 => 518508572525671 / 4000000000000
    | 20 => 324458589561613 / 4000000000000
    | 21 => 174494908566771 / 4000000000000
    | 22 => 473787620853313 / 4000000000000
    | 23 => 646916490925601 / 4000000000000
    | 24 => 273541410438387 / 4000000000000
    | 25 => 1111930646867027 / 4000000000000
    | _ => 742718140722493 / 4000000000000
  state := fun i =>
    match i.val with
    | 0 => (orderedInterval (-31963649775 / 1000000000000) (-31963645514 / 1000000000000), orderedInterval (56998583629 / 1000000000000) (56998587890 / 1000000000000))
    | 1 => (orderedInterval (-61826310599 / 1000000000000) (-61826310598 / 1000000000000), orderedInterval (-43975134769 / 1000000000000) (-43975134768 / 1000000000000))
    | 2 => (orderedInterval (13730996396 / 1000000000000) (13730996514 / 1000000000000), orderedInterval (-58235599107 / 1000000000000) (-58235598988 / 1000000000000))
    | 3 => (orderedInterval (140380188520 / 1000000000000) (140380188527 / 1000000000000), orderedInterval (7966661842 / 1000000000000) (7966661849 / 1000000000000))
    | 4 => (orderedInterval (-65462514763 / 1000000000000) (-65462431205 / 1000000000000), orderedInterval (55969456641 / 1000000000000) (55969540200 / 1000000000000))
    | 5 => (orderedInterval (23866277347 / 1000000000000) (23866279134 / 1000000000000), orderedInterval (-46384868745 / 1000000000000) (-46384866958 / 1000000000000))
    | 6 => (orderedInterval (-35521943358 / 1000000000000) (-35521943357 / 1000000000000), orderedInterval (-49151709822 / 1000000000000) (-49151709821 / 1000000000000))
    | 7 => (orderedInterval (44388057231 / 1000000000000) (44388057233 / 1000000000000), orderedInterval (13411645391 / 1000000000000) (13411645393 / 1000000000000))
    | 8 => (orderedInterval (-51146063807 / 1000000000000) (-51146059296 / 1000000000000), orderedInterval (17606936803 / 1000000000000) (17606941313 / 1000000000000))
    | 9 => (orderedInterval (38347716473 / 1000000000000) (38347757490 / 1000000000000), orderedInterval (-20885992418 / 1000000000000) (-20885951401 / 1000000000000))
    | 10 => (orderedInterval (-48025159299 / 1000000000000) (-48025113850 / 1000000000000), orderedInterval (31621486964 / 1000000000000) (31621532413 / 1000000000000))
    | 11 => (orderedInterval (-32099643987 / 1000000000000) (-32099643986 / 1000000000000), orderedInterval (-28735414554 / 1000000000000) (-28735414553 / 1000000000000))
    | 12 => (orderedInterval (14859734049 / 1000000000000) (14859734050 / 1000000000000), orderedInterval (42032043710 / 1000000000000) (42032043711 / 1000000000000))
    | 13 => (orderedInterval (9784341011 / 1000000000000) (9784341054 / 1000000000000), orderedInterval (-51905926894 / 1000000000000) (-51905926851 / 1000000000000))
    | 14 => (orderedInterval (42397319900 / 1000000000000) (42397364518 / 1000000000000), orderedInterval (-25791982889 / 1000000000000) (-25791938271 / 1000000000000))
    | 15 => (orderedInterval (5776131051 / 1000000000000) (5776131065 / 1000000000000), orderedInterval (-54009827181 / 1000000000000) (-54009827167 / 1000000000000))
    | 16 => (orderedInterval (6755582261 / 1000000000000) (6755582281 / 1000000000000), orderedInterval (-57394431947 / 1000000000000) (-57394431927 / 1000000000000))
    | 17 => (orderedInterval (32263290655 / 1000000000000) (32263290656 / 1000000000000), orderedInterval (35469539950 / 1000000000000) (35469539951 / 1000000000000))
    | 18 => (orderedInterval (15284783489 / 1000000000000) (15284783645 / 1000000000000), orderedInterval (-62736824384 / 1000000000000) (-62736824228 / 1000000000000))
    | 19 => (orderedInterval (-70035306478 / 1000000000000) (-70035306409 / 1000000000000), orderedInterval (2756184659 / 1000000000000) (2756184727 / 1000000000000))
    | 20 => (orderedInterval (19081856571 / 1000000000000) (19081856572 / 1000000000000), orderedInterval (86394882156 / 1000000000000) (86394882157 / 1000000000000))
    | 21 => (orderedInterval (49693968996 / 1000000000000) (49693968997 / 1000000000000), orderedInterval (109542135046 / 1000000000000) (109542135047 / 1000000000000))
    | 22 => (orderedInterval (-10902917859 / 1000000000000) (-10902917803 / 1000000000000), orderedInterval (72543603509 / 1000000000000) (72543603565 / 1000000000000))
    | 23 => (orderedInterval (-47096890861 / 1000000000000) (-47096794420 / 1000000000000), orderedInterval (41596950157 / 1000000000000) (41597046598 / 1000000000000))
    | 24 => (orderedInterval (5196466865 / 1000000000000) (5196466868 / 1000000000000), orderedInterval (96307968868 / 1000000000000) (96307968872 / 1000000000000))
    | 25 => (orderedInterval (35447240743 / 1000000000000) (35447292028 / 1000000000000), orderedInterval (-32213944346 / 1000000000000) (-32213893060 / 1000000000000))
    | _ => (orderedInterval (-52454465507 / 1000000000000) (-52454465506 / 1000000000000), orderedInterval (-25880197975 / 1000000000000) (-25880197974 / 1000000000000))
  chunkTarget := fun r b =>
    match r.val with
    | 0 =>
      match b.val with
      | 0 => orderedInterval (-12439622575 / 1000000000000) (-12439620868 / 1000000000000)
      | 1 => orderedInterval (-5609821453 / 1000000000000) (-5609818256 / 1000000000000)
      | 2 => orderedInterval (-2605204737 / 1000000000000) (-2605204619 / 1000000000000)
      | 3 => orderedInterval (-14935356154 / 1000000000000) (-14935345438 / 1000000000000)
      | 4 => orderedInterval (442416177 / 1000000000000) (442416425 / 1000000000000)
      | 5 => orderedInterval (506169003 / 1000000000000) (506169020 / 1000000000000)
      | 6 => orderedInterval (2141288871 / 1000000000000) (2141288939 / 1000000000000)
      | 7 => orderedInterval (2939193136 / 1000000000000) (2939200547 / 1000000000000)
      | _ => orderedInterval (6987702613 / 1000000000000) (6987706830 / 1000000000000)
    | 1 =>
      match b.val with
      | 0 => orderedInterval (18220374734 / 1000000000000) (18220376444 / 1000000000000)
      | 1 => orderedInterval (6330457817 / 1000000000000) (6330459799 / 1000000000000)
      | 2 => orderedInterval (-198313152 / 1000000000000) (-198312978 / 1000000000000)
      | 3 => orderedInterval (1965028907 / 1000000000000) (1965049675 / 1000000000000)
      | 4 => orderedInterval (-8895782947 / 1000000000000) (-8895782520 / 1000000000000)
      | 5 => orderedInterval (4968926240 / 1000000000000) (4968926263 / 1000000000000)
      | 6 => orderedInterval (11651018602 / 1000000000000) (11651018667 / 1000000000000)
      | 7 => orderedInterval (-5342882163 / 1000000000000) (-5342874149 / 1000000000000)
      | _ => orderedInterval (11172393455 / 1000000000000) (11172401277 / 1000000000000)
    | 2 =>
      match b.val with
      | 0 => orderedInterval (11717031330 / 1000000000000) (11717033054 / 1000000000000)
      | 1 => orderedInterval (4994113713 / 1000000000000) (4994115084 / 1000000000000)
      | 2 => orderedInterval (7986764995 / 1000000000000) (7986765255 / 1000000000000)
      | 3 => orderedInterval (63935215161 / 1000000000000) (63935257617 / 1000000000000)
      | 4 => orderedInterval (-226656947 / 1000000000000) (-226656209 / 1000000000000)
      | 5 => orderedInterval (-2366937839 / 1000000000000) (-2366937805 / 1000000000000)
      | 6 => orderedInterval (-684165709 / 1000000000000) (-684165646 / 1000000000000)
      | 7 => orderedInterval (-4265511444 / 1000000000000) (-4265502724 / 1000000000000)
      | _ => orderedInterval (-5286759615 / 1000000000000) (-5286745043 / 1000000000000)
    | 3 =>
      match b.val with
      | 0 => orderedInterval (-16732774740 / 1000000000000) (-16732773011 / 1000000000000)
      | 1 => orderedInterval (-13128466202 / 1000000000000) (-13128465074 / 1000000000000)
      | 2 => orderedInterval (1833513332 / 1000000000000) (1833513719 / 1000000000000)
      | 3 => orderedInterval (2151955515 / 1000000000000) (2152045104 / 1000000000000)
      | 4 => orderedInterval (24258713201 / 1000000000000) (24258714475 / 1000000000000)
      | 5 => orderedInterval (-10666879990 / 1000000000000) (-10666879939 / 1000000000000)
      | 6 => orderedInterval (-11076691986 / 1000000000000) (-11076691924 / 1000000000000)
      | 7 => orderedInterval (4933057204 / 1000000000000) (4933066637 / 1000000000000)
      | _ => orderedInterval (-26180912965 / 1000000000000) (-26180885896 / 1000000000000)
    | _ =>
      match b.val with
      | 0 => orderedInterval (-10993262066 / 1000000000000) (-10993260322 / 1000000000000)
      | 1 => orderedInterval (-10338921852 / 1000000000000) (-10338920665 / 1000000000000)
      | 2 => orderedInterval (-26584194970 / 1000000000000) (-26584194384 / 1000000000000)
      | 3 => orderedInterval (-305943442558 / 1000000000000) (-305943248532 / 1000000000000)
      | 4 => orderedInterval (-2849094316 / 1000000000000) (-2849092104 / 1000000000000)
      | 5 => orderedInterval (9061740865 / 1000000000000) (9061740945 / 1000000000000)
      | 6 => orderedInterval (-232422421 / 1000000000000) (-232422359 / 1000000000000)
      | 7 => orderedInterval (4968061097 / 1000000000000) (4968071363 / 1000000000000)
      | _ => orderedInterval (-10722004296 / 1000000000000) (-10721953822 / 1000000000000)
  coefficientTarget := fun i =>
    match i.val with
    | 0 => orderedInterval (-22573235119 / 1000000000000) (-22573207420 / 1000000000000)
    | 1 => orderedInterval (39871221493 / 1000000000000) (39871262478 / 1000000000000)
    | 2 => orderedInterval (75803093645 / 1000000000000) (75803163583 / 1000000000000)
    | 3 => orderedInterval (-44608486631 / 1000000000000) (-44608355909 / 1000000000000)
    | _ => orderedInterval (-353633540517 / 1000000000000) (-353633279880 / 1000000000000)

theorem compactCertificate275_stateChecks0 :
    compactCertificate275.stateChecks 0 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 48 12 (299 / 2)) (orderedInterval (-31963649775 / 1000000000000) (-31963645514 / 1000000000000), orderedInterval (56998583629 / 1000000000000) (56998587890 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 35 12 (440484093422399 / 4000000000000)) (orderedInterval (-61826310599 / 1000000000000) (-61826310598 / 1000000000000), orderedInterval (-43975134769 / 1000000000000) (-43975134768 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 57 12 (142443505495967 / 800000000000)) (orderedInterval (13730996396 / 1000000000000) (13730996514 / 1000000000000), orderedInterval (-58235599107 / 1000000000000) (-58235598988 / 1000000000000))) = true
  norm_num [besselStateAtRationalPoint, besselIntervalStepZero,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, besselZeroTransition,
    besselInitial, besselGridStateAt, besselGridStateBlock00, besselGridStateBlock01,
    besselGridStateBlock02, besselGridStateBlock03, besselGridStateBlock04,
    besselGridStateBlock05, besselGridStateBlock06, besselGridStateBlock07,
    besselGridStateBlock08, besselGridStateBlock09, besselGridStateBlock10,
    besselGridStateBlock11, besselGridStateBlock12, besselGridStateBlock13,
    besselGridStateBlock14, besselGridState010, besselGridState014, besselGridState022, besselGridState026, besselGridState027, besselGridState035, besselGridState038, besselGridState041, besselGridState048, besselGridState049, besselGridState052, besselGridState055, besselGridState057, besselGridState059, besselGridState061, besselGridState069, besselGridState073, besselGridState075, besselGridState082, besselGridState088, besselGridState089, besselGridState094, besselGridState102, besselGridState106, besselGridState109, besselStateSubset, linearInterval, widenInterval,
    rationalErrorInterval, rationalIntervalSubset, orderedInterval, Finset.sum_range_succ,
    IntervalRat.add, IntervalRat.mul, IntervalRat.scale, IntervalRat.singleton]

theorem compactCertificate275_stateChecks1 :
    compactCertificate275.stateChecks 3 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 10 12 (128532159877693 / 4000000000000)) (orderedInterval (140380188520 / 1000000000000) (140380188527 / 1000000000000), orderedInterval (7966661842 / 1000000000000) (7966661849 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 27 12 (345255460975321 / 4000000000000)) (orderedInterval (-65462514763 / 1000000000000) (-65462431205 / 1000000000000), orderedInterval (55969456641 / 1000000000000) (55969540200 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 75 12 (937435738299957 / 4000000000000)) (orderedInterval (23866277347 / 1000000000000) (23866279134 / 1000000000000), orderedInterval (-46384868745 / 1000000000000) (-46384866958 / 1000000000000))) = true
  norm_num [besselStateAtRationalPoint, besselIntervalStepZero,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, besselZeroTransition,
    besselInitial, besselGridStateAt, besselGridStateBlock00, besselGridStateBlock01,
    besselGridStateBlock02, besselGridStateBlock03, besselGridStateBlock04,
    besselGridStateBlock05, besselGridStateBlock06, besselGridStateBlock07,
    besselGridStateBlock08, besselGridStateBlock09, besselGridStateBlock10,
    besselGridStateBlock11, besselGridStateBlock12, besselGridStateBlock13,
    besselGridStateBlock14, besselGridState010, besselGridState014, besselGridState022, besselGridState026, besselGridState027, besselGridState035, besselGridState038, besselGridState041, besselGridState048, besselGridState049, besselGridState052, besselGridState055, besselGridState057, besselGridState059, besselGridState061, besselGridState069, besselGridState073, besselGridState075, besselGridState082, besselGridState088, besselGridState089, besselGridState094, besselGridState102, besselGridState106, besselGridState109, besselStateSubset, linearInterval, widenInterval,
    rationalErrorInterval, rationalIntervalSubset, orderedInterval, Finset.sum_range_succ,
    IntervalRat.add, IntervalRat.mul, IntervalRat.scale, IntervalRat.singleton]

theorem compactCertificate275_stateChecks2 :
    compactCertificate275.stateChecks 6 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 55 12 (690510921950941 / 4000000000000)) (orderedInterval (-35521943358 / 1000000000000) (-35521943357 / 1000000000000), orderedInterval (-49151709822 / 1000000000000) (-49151709821 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 94 12 (1183202234144593 / 4000000000000)) (orderedInterval (44388057231 / 1000000000000) (44388057233 / 1000000000000), orderedInterval (13411645391 / 1000000000000) (13411645393 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 69 12 (871541410438387 / 4000000000000)) (orderedInterval (-51146063807 / 1000000000000) (-51146059296 / 1000000000000), orderedInterval (17606936803 / 1000000000000) (17606941313 / 1000000000000))) = true
  norm_num [besselStateAtRationalPoint, besselIntervalStepZero,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, besselZeroTransition,
    besselInitial, besselGridStateAt, besselGridStateBlock00, besselGridStateBlock01,
    besselGridStateBlock02, besselGridStateBlock03, besselGridStateBlock04,
    besselGridStateBlock05, besselGridStateBlock06, besselGridStateBlock07,
    besselGridStateBlock08, besselGridStateBlock09, besselGridStateBlock10,
    besselGridStateBlock11, besselGridStateBlock12, besselGridStateBlock13,
    besselGridStateBlock14, besselGridState010, besselGridState014, besselGridState022, besselGridState026, besselGridState027, besselGridState035, besselGridState038, besselGridState041, besselGridState048, besselGridState049, besselGridState052, besselGridState055, besselGridState057, besselGridState059, besselGridState061, besselGridState069, besselGridState073, besselGridState075, besselGridState082, besselGridState088, besselGridState089, besselGridState094, besselGridState102, besselGridState106, besselGridState109, besselStateSubset, linearInterval, widenInterval,
    rationalErrorInterval, rationalIntervalSubset, orderedInterval, Finset.sum_range_succ,
    IntervalRat.add, IntervalRat.mul, IntervalRat.scale, IntervalRat.singleton]

theorem compactCertificate275_stateChecks3 :
    compactCertificate275.stateChecks 9 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 106 12 (1337168650544701 / 4000000000000)) (orderedInterval (38347716473 / 1000000000000) (38347757490 / 1000000000000), orderedInterval (-20885992418 / 1000000000000) (-20885951401 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 61 12 (772014680343829 / 4000000000000)) (orderedInterval (-48025159299 / 1000000000000) (-48025113850 / 1000000000000), orderedInterval (31621486964 / 1000000000000) (31621532413 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 109 12 (1369953597833561 / 4000000000000)) (orderedInterval (-32099643987 / 1000000000000) (-32099643986 / 1000000000000), orderedInterval (-28735414554 / 1000000000000) (-28735414553 / 1000000000000))) = true
  norm_num [besselStateAtRationalPoint, besselIntervalStepZero,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, besselZeroTransition,
    besselInitial, besselGridStateAt, besselGridStateBlock00, besselGridStateBlock01,
    besselGridStateBlock02, besselGridStateBlock03, besselGridStateBlock04,
    besselGridStateBlock05, besselGridStateBlock06, besselGridStateBlock07,
    besselGridStateBlock08, besselGridStateBlock09, besselGridStateBlock10,
    besselGridStateBlock11, besselGridStateBlock12, besselGridStateBlock13,
    besselGridStateBlock14, besselGridState010, besselGridState014, besselGridState022, besselGridState026, besselGridState027, besselGridState035, besselGridState038, besselGridState041, besselGridState048, besselGridState049, besselGridState052, besselGridState055, besselGridState057, besselGridState059, besselGridState061, besselGridState069, besselGridState073, besselGridState075, besselGridState082, besselGridState088, besselGridState089, besselGridState094, besselGridState102, besselGridState106, besselGridState109, besselStateSubset, linearInterval, widenInterval,
    rationalErrorInterval, rationalIntervalSubset, orderedInterval, Finset.sum_range_succ,
    IntervalRat.add, IntervalRat.mul, IntervalRat.scale, IntervalRat.singleton]

theorem compactCertificate275_stateChecks4 :
    compactCertificate275.stateChecks 12 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 102 12 (1279988356802909 / 4000000000000)) (orderedInterval (14859734049 / 1000000000000) (14859734050 / 1000000000000), orderedInterval (42032043710 / 1000000000000) (42032043711 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 73 12 (913460088527597 / 4000000000000)) (orderedInterval (9784341011 / 1000000000000) (9784341054 / 1000000000000), orderedInterval (-51905926894 / 1000000000000) (-51905926851 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 82 12 (1035766382925963 / 4000000000000)) (orderedInterval (42397319900 / 1000000000000) (42397364518 / 1000000000000), orderedInterval (-25791982889 / 1000000000000) (-25791938271 / 1000000000000))) = true
  norm_num [besselStateAtRationalPoint, besselIntervalStepZero,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, besselZeroTransition,
    besselInitial, besselGridStateAt, besselGridStateBlock00, besselGridStateBlock01,
    besselGridStateBlock02, besselGridStateBlock03, besselGridStateBlock04,
    besselGridStateBlock05, besselGridStateBlock06, besselGridStateBlock07,
    besselGridStateBlock08, besselGridStateBlock09, besselGridStateBlock10,
    besselGridStateBlock11, besselGridStateBlock12, besselGridStateBlock13,
    besselGridStateBlock14, besselGridState010, besselGridState014, besselGridState022, besselGridState026, besselGridState027, besselGridState035, besselGridState038, besselGridState041, besselGridState048, besselGridState049, besselGridState052, besselGridState055, besselGridState057, besselGridState059, besselGridState061, besselGridState069, besselGridState073, besselGridState075, besselGridState082, besselGridState088, besselGridState089, besselGridState094, besselGridState102, besselGridState106, besselGridState109, besselStateSubset, linearInterval, widenInterval,
    rationalErrorInterval, rationalIntervalSubset, orderedInterval, Finset.sum_range_succ,
    IntervalRat.add, IntervalRat.mul, IntervalRat.scale, IntervalRat.singleton]

theorem compactCertificate275_stateChecks5 :
    compactCertificate275.stateChecks 15 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 69 12 (863514026009947 / 4000000000000)) (orderedInterval (5776131051 / 1000000000000) (5776131065 / 1000000000000), orderedInterval (-54009827181 / 1000000000000) (-54009827167 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 61 12 (762940829732887 / 4000000000000)) (orderedInterval (6755582261 / 1000000000000) (6755582281 / 1000000000000), orderedInterval (-57394431947 / 1000000000000) (-57394431927 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 88 12 (221129989503813 / 800000000000)) (orderedInterval (32263290655 / 1000000000000) (32263290656 / 1000000000000), orderedInterval (35469539950 / 1000000000000) (35469539951 / 1000000000000))) = true
  norm_num [besselStateAtRationalPoint, besselIntervalStepZero,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, besselZeroTransition,
    besselInitial, besselGridStateAt, besselGridStateBlock00, besselGridStateBlock01,
    besselGridStateBlock02, besselGridStateBlock03, besselGridStateBlock04,
    besselGridStateBlock05, besselGridStateBlock06, besselGridStateBlock07,
    besselGridStateBlock08, besselGridStateBlock09, besselGridStateBlock10,
    besselGridStateBlock11, besselGridStateBlock12, besselGridStateBlock13,
    besselGridStateBlock14, besselGridState010, besselGridState014, besselGridState022, besselGridState026, besselGridState027, besselGridState035, besselGridState038, besselGridState041, besselGridState048, besselGridState049, besselGridState052, besselGridState055, besselGridState057, besselGridState059, besselGridState061, besselGridState069, besselGridState073, besselGridState075, besselGridState082, besselGridState088, besselGridState089, besselGridState094, besselGridState102, besselGridState106, besselGridState109, besselStateSubset, linearInterval, widenInterval,
    rationalErrorInterval, rationalIntervalSubset, orderedInterval, Finset.sum_range_succ,
    IntervalRat.add, IntervalRat.mul, IntervalRat.scale, IntervalRat.singleton]

theorem compactCertificate275_stateChecks6 :
    compactCertificate275.stateChecks 18 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 49 12 (611657188401311 / 4000000000000)) (orderedInterval (15284783489 / 1000000000000) (15284783645 / 1000000000000), orderedInterval (-62736824384 / 1000000000000) (-62736824228 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 41 12 (518508572525671 / 4000000000000)) (orderedInterval (-70035306478 / 1000000000000) (-70035306409 / 1000000000000), orderedInterval (2756184659 / 1000000000000) (2756184727 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 26 12 (324458589561613 / 4000000000000)) (orderedInterval (19081856571 / 1000000000000) (19081856572 / 1000000000000), orderedInterval (86394882156 / 1000000000000) (86394882157 / 1000000000000))) = true
  norm_num [besselStateAtRationalPoint, besselIntervalStepZero,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, besselZeroTransition,
    besselInitial, besselGridStateAt, besselGridStateBlock00, besselGridStateBlock01,
    besselGridStateBlock02, besselGridStateBlock03, besselGridStateBlock04,
    besselGridStateBlock05, besselGridStateBlock06, besselGridStateBlock07,
    besselGridStateBlock08, besselGridStateBlock09, besselGridStateBlock10,
    besselGridStateBlock11, besselGridStateBlock12, besselGridStateBlock13,
    besselGridStateBlock14, besselGridState010, besselGridState014, besselGridState022, besselGridState026, besselGridState027, besselGridState035, besselGridState038, besselGridState041, besselGridState048, besselGridState049, besselGridState052, besselGridState055, besselGridState057, besselGridState059, besselGridState061, besselGridState069, besselGridState073, besselGridState075, besselGridState082, besselGridState088, besselGridState089, besselGridState094, besselGridState102, besselGridState106, besselGridState109, besselStateSubset, linearInterval, widenInterval,
    rationalErrorInterval, rationalIntervalSubset, orderedInterval, Finset.sum_range_succ,
    IntervalRat.add, IntervalRat.mul, IntervalRat.scale, IntervalRat.singleton]

theorem compactCertificate275_stateChecks7 :
    compactCertificate275.stateChecks 21 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 14 12 (174494908566771 / 4000000000000)) (orderedInterval (49693968996 / 1000000000000) (49693968997 / 1000000000000), orderedInterval (109542135046 / 1000000000000) (109542135047 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 38 12 (473787620853313 / 4000000000000)) (orderedInterval (-10902917859 / 1000000000000) (-10902917803 / 1000000000000), orderedInterval (72543603509 / 1000000000000) (72543603565 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 52 12 (646916490925601 / 4000000000000)) (orderedInterval (-47096890861 / 1000000000000) (-47096794420 / 1000000000000), orderedInterval (41596950157 / 1000000000000) (41597046598 / 1000000000000))) = true
  norm_num [besselStateAtRationalPoint, besselIntervalStepZero,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, besselZeroTransition,
    besselInitial, besselGridStateAt, besselGridStateBlock00, besselGridStateBlock01,
    besselGridStateBlock02, besselGridStateBlock03, besselGridStateBlock04,
    besselGridStateBlock05, besselGridStateBlock06, besselGridStateBlock07,
    besselGridStateBlock08, besselGridStateBlock09, besselGridStateBlock10,
    besselGridStateBlock11, besselGridStateBlock12, besselGridStateBlock13,
    besselGridStateBlock14, besselGridState010, besselGridState014, besselGridState022, besselGridState026, besselGridState027, besselGridState035, besselGridState038, besselGridState041, besselGridState048, besselGridState049, besselGridState052, besselGridState055, besselGridState057, besselGridState059, besselGridState061, besselGridState069, besselGridState073, besselGridState075, besselGridState082, besselGridState088, besselGridState089, besselGridState094, besselGridState102, besselGridState106, besselGridState109, besselStateSubset, linearInterval, widenInterval,
    rationalErrorInterval, rationalIntervalSubset, orderedInterval, Finset.sum_range_succ,
    IntervalRat.add, IntervalRat.mul, IntervalRat.scale, IntervalRat.singleton]

theorem compactCertificate275_stateChecks8 :
    compactCertificate275.stateChecks 24 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 22 12 (273541410438387 / 4000000000000)) (orderedInterval (5196466865 / 1000000000000) (5196466868 / 1000000000000), orderedInterval (96307968868 / 1000000000000) (96307968872 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 89 12 (1111930646867027 / 4000000000000)) (orderedInterval (35447240743 / 1000000000000) (35447292028 / 1000000000000), orderedInterval (-32213944346 / 1000000000000) (-32213893060 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 59 12 (742718140722493 / 4000000000000)) (orderedInterval (-52454465507 / 1000000000000) (-52454465506 / 1000000000000), orderedInterval (-25880197975 / 1000000000000) (-25880197974 / 1000000000000))) = true
  norm_num [besselStateAtRationalPoint, besselIntervalStepZero,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, besselZeroTransition,
    besselInitial, besselGridStateAt, besselGridStateBlock00, besselGridStateBlock01,
    besselGridStateBlock02, besselGridStateBlock03, besselGridStateBlock04,
    besselGridStateBlock05, besselGridStateBlock06, besselGridStateBlock07,
    besselGridStateBlock08, besselGridStateBlock09, besselGridStateBlock10,
    besselGridStateBlock11, besselGridStateBlock12, besselGridStateBlock13,
    besselGridStateBlock14, besselGridState010, besselGridState014, besselGridState022, besselGridState026, besselGridState027, besselGridState035, besselGridState038, besselGridState041, besselGridState048, besselGridState049, besselGridState052, besselGridState055, besselGridState057, besselGridState059, besselGridState061, besselGridState069, besselGridState073, besselGridState075, besselGridState082, besselGridState088, besselGridState089, besselGridState094, besselGridState102, besselGridState106, besselGridState109, besselStateSubset, linearInterval, widenInterval,
    rationalErrorInterval, rationalIntervalSubset, orderedInterval, Finset.sum_range_succ,
    IntervalRat.add, IntervalRat.mul, IntervalRat.scale, IntervalRat.singleton]

theorem compactCertificate275_states : ∀ j,
    BesselStateValid (compactCertificate275.point j) (compactCertificate275.state j) :=
  compactCertificate275.statesValid_of_checks3 compactCertificate275_stateChecks0
    compactCertificate275_stateChecks1 compactCertificate275_stateChecks2
    compactCertificate275_stateChecks3 compactCertificate275_stateChecks4
    compactCertificate275_stateChecks5 compactCertificate275_stateChecks6
    compactCertificate275_stateChecks7 compactCertificate275_stateChecks8

theorem compactCertificate275_chunkChecks0_0 :
    compactCertificate275.chunkChecks (0 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 0) <| besselDerivativeNearFromState (299 / 2) 0 (IntervalRat.scale (299 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-31963649775 / 1000000000000) (-31963645514 / 1000000000000), orderedInterval (56998583629 / 1000000000000) (56998587890 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 0) <| besselDerivativeNearFromState (440484093422399 / 4000000000000) 0 (IntervalRat.scale (299 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-61826310599 / 1000000000000) (-61826310598 / 1000000000000), orderedInterval (-43975134769 / 1000000000000) (-43975134768 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 0) <| besselDerivativeNearFromState (142443505495967 / 800000000000) 0 (IntervalRat.scale (299 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (13730996396 / 1000000000000) (13730996514 / 1000000000000), orderedInterval (-58235599107 / 1000000000000) (-58235598988 / 1000000000000)))) (orderedInterval (-12439622575 / 1000000000000) (-12439620868 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 0) <| besselDerivativeNearFromState (128532159877693 / 4000000000000) 0 (IntervalRat.scale (299 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (140380188520 / 1000000000000) (140380188527 / 1000000000000), orderedInterval (7966661842 / 1000000000000) (7966661849 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 0) <| besselDerivativeNearFromState (345255460975321 / 4000000000000) 0 (IntervalRat.scale (299 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-65462514763 / 1000000000000) (-65462431205 / 1000000000000), orderedInterval (55969456641 / 1000000000000) (55969540200 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 0) <| besselDerivativeNearFromState (937435738299957 / 4000000000000) 0 (IntervalRat.scale (299 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (23866277347 / 1000000000000) (23866279134 / 1000000000000), orderedInterval (-46384868745 / 1000000000000) (-46384866958 / 1000000000000)))) (orderedInterval (-5609821453 / 1000000000000) (-5609818256 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 0) <| besselDerivativeNearFromState (690510921950941 / 4000000000000) 0 (IntervalRat.scale (299 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-35521943358 / 1000000000000) (-35521943357 / 1000000000000), orderedInterval (-49151709822 / 1000000000000) (-49151709821 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 0) <| besselDerivativeNearFromState (1183202234144593 / 4000000000000) 0 (IntervalRat.scale (299 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (44388057231 / 1000000000000) (44388057233 / 1000000000000), orderedInterval (13411645391 / 1000000000000) (13411645393 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 0) <| besselDerivativeNearFromState (871541410438387 / 4000000000000) 0 (IntervalRat.scale (299 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-51146063807 / 1000000000000) (-51146059296 / 1000000000000), orderedInterval (17606936803 / 1000000000000) (17606941313 / 1000000000000)))) (orderedInterval (-2605204737 / 1000000000000) (-2605204619 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate275_chunkChecks0_1 :
    compactCertificate275.chunkChecks (0 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 0) <| besselDerivativeNearFromState (1337168650544701 / 4000000000000) 0 (IntervalRat.scale (299 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (38347716473 / 1000000000000) (38347757490 / 1000000000000), orderedInterval (-20885992418 / 1000000000000) (-20885951401 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 0) <| besselDerivativeNearFromState (772014680343829 / 4000000000000) 0 (IntervalRat.scale (299 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-48025159299 / 1000000000000) (-48025113850 / 1000000000000), orderedInterval (31621486964 / 1000000000000) (31621532413 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 0) <| besselDerivativeNearFromState (1369953597833561 / 4000000000000) 0 (IntervalRat.scale (299 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-32099643987 / 1000000000000) (-32099643986 / 1000000000000), orderedInterval (-28735414554 / 1000000000000) (-28735414553 / 1000000000000)))) (orderedInterval (-14935356154 / 1000000000000) (-14935345438 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 0) <| besselDerivativeNearFromState (1279988356802909 / 4000000000000) 0 (IntervalRat.scale (299 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (14859734049 / 1000000000000) (14859734050 / 1000000000000), orderedInterval (42032043710 / 1000000000000) (42032043711 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 0) <| besselDerivativeNearFromState (913460088527597 / 4000000000000) 0 (IntervalRat.scale (299 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (9784341011 / 1000000000000) (9784341054 / 1000000000000), orderedInterval (-51905926894 / 1000000000000) (-51905926851 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 0) <| besselDerivativeNearFromState (1035766382925963 / 4000000000000) 0 (IntervalRat.scale (299 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (42397319900 / 1000000000000) (42397364518 / 1000000000000), orderedInterval (-25791982889 / 1000000000000) (-25791938271 / 1000000000000)))) (orderedInterval (442416177 / 1000000000000) (442416425 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 0) <| besselDerivativeNearFromState (863514026009947 / 4000000000000) 0 (IntervalRat.scale (299 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (5776131051 / 1000000000000) (5776131065 / 1000000000000), orderedInterval (-54009827181 / 1000000000000) (-54009827167 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 0) <| besselDerivativeNearFromState (762940829732887 / 4000000000000) 0 (IntervalRat.scale (299 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (6755582261 / 1000000000000) (6755582281 / 1000000000000), orderedInterval (-57394431947 / 1000000000000) (-57394431927 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 0) <| besselDerivativeNearFromState (221129989503813 / 800000000000) 0 (IntervalRat.scale (299 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (32263290655 / 1000000000000) (32263290656 / 1000000000000), orderedInterval (35469539950 / 1000000000000) (35469539951 / 1000000000000)))) (orderedInterval (506169003 / 1000000000000) (506169020 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate275_chunkChecks0_2 :
    compactCertificate275.chunkChecks (0 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 0) <| besselDerivativeNearFromState (611657188401311 / 4000000000000) 0 (IntervalRat.scale (299 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (15284783489 / 1000000000000) (15284783645 / 1000000000000), orderedInterval (-62736824384 / 1000000000000) (-62736824228 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 0) <| besselDerivativeNearFromState (518508572525671 / 4000000000000) 0 (IntervalRat.scale (299 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-70035306478 / 1000000000000) (-70035306409 / 1000000000000), orderedInterval (2756184659 / 1000000000000) (2756184727 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 0) <| besselDerivativeNearFromState (324458589561613 / 4000000000000) 0 (IntervalRat.scale (299 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (19081856571 / 1000000000000) (19081856572 / 1000000000000), orderedInterval (86394882156 / 1000000000000) (86394882157 / 1000000000000)))) (orderedInterval (2141288871 / 1000000000000) (2141288939 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 0) <| besselDerivativeNearFromState (174494908566771 / 4000000000000) 0 (IntervalRat.scale (299 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (49693968996 / 1000000000000) (49693968997 / 1000000000000), orderedInterval (109542135046 / 1000000000000) (109542135047 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 0) <| besselDerivativeNearFromState (473787620853313 / 4000000000000) 0 (IntervalRat.scale (299 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-10902917859 / 1000000000000) (-10902917803 / 1000000000000), orderedInterval (72543603509 / 1000000000000) (72543603565 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 0) <| besselDerivativeNearFromState (646916490925601 / 4000000000000) 0 (IntervalRat.scale (299 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-47096890861 / 1000000000000) (-47096794420 / 1000000000000), orderedInterval (41596950157 / 1000000000000) (41597046598 / 1000000000000)))) (orderedInterval (2939193136 / 1000000000000) (2939200547 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 0) <| besselDerivativeNearFromState (273541410438387 / 4000000000000) 0 (IntervalRat.scale (299 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (5196466865 / 1000000000000) (5196466868 / 1000000000000), orderedInterval (96307968868 / 1000000000000) (96307968872 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 0) <| besselDerivativeNearFromState (1111930646867027 / 4000000000000) 0 (IntervalRat.scale (299 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (35447240743 / 1000000000000) (35447292028 / 1000000000000), orderedInterval (-32213944346 / 1000000000000) (-32213893060 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 0) <| besselDerivativeNearFromState (742718140722493 / 4000000000000) 0 (IntervalRat.scale (299 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-52454465507 / 1000000000000) (-52454465506 / 1000000000000), orderedInterval (-25880197975 / 1000000000000) (-25880197974 / 1000000000000)))) (orderedInterval (6987702613 / 1000000000000) (6987706830 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate275_chunkChecks0 :
    compactCertificate275.chunkChecks (0 : Fin 5) 0 9 = true :=
  compactCertificate275.chunkChecks_nine_of_three (0 : Fin 5) compactCertificate275_chunkChecks0_0
    compactCertificate275_chunkChecks0_1 compactCertificate275_chunkChecks0_2

theorem compactCertificate275_chunkChecks1_0 :
    compactCertificate275.chunkChecks (1 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 1) <| besselDerivativeNearFromState (299 / 2) 1 (IntervalRat.scale (299 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-31963649775 / 1000000000000) (-31963645514 / 1000000000000), orderedInterval (56998583629 / 1000000000000) (56998587890 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 1) <| besselDerivativeNearFromState (440484093422399 / 4000000000000) 1 (IntervalRat.scale (299 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-61826310599 / 1000000000000) (-61826310598 / 1000000000000), orderedInterval (-43975134769 / 1000000000000) (-43975134768 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 1) <| besselDerivativeNearFromState (142443505495967 / 800000000000) 1 (IntervalRat.scale (299 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (13730996396 / 1000000000000) (13730996514 / 1000000000000), orderedInterval (-58235599107 / 1000000000000) (-58235598988 / 1000000000000)))) (orderedInterval (18220374734 / 1000000000000) (18220376444 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 1) <| besselDerivativeNearFromState (128532159877693 / 4000000000000) 1 (IntervalRat.scale (299 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (140380188520 / 1000000000000) (140380188527 / 1000000000000), orderedInterval (7966661842 / 1000000000000) (7966661849 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 1) <| besselDerivativeNearFromState (345255460975321 / 4000000000000) 1 (IntervalRat.scale (299 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-65462514763 / 1000000000000) (-65462431205 / 1000000000000), orderedInterval (55969456641 / 1000000000000) (55969540200 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 1) <| besselDerivativeNearFromState (937435738299957 / 4000000000000) 1 (IntervalRat.scale (299 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (23866277347 / 1000000000000) (23866279134 / 1000000000000), orderedInterval (-46384868745 / 1000000000000) (-46384866958 / 1000000000000)))) (orderedInterval (6330457817 / 1000000000000) (6330459799 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 1) <| besselDerivativeNearFromState (690510921950941 / 4000000000000) 1 (IntervalRat.scale (299 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-35521943358 / 1000000000000) (-35521943357 / 1000000000000), orderedInterval (-49151709822 / 1000000000000) (-49151709821 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 1) <| besselDerivativeNearFromState (1183202234144593 / 4000000000000) 1 (IntervalRat.scale (299 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (44388057231 / 1000000000000) (44388057233 / 1000000000000), orderedInterval (13411645391 / 1000000000000) (13411645393 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 1) <| besselDerivativeNearFromState (871541410438387 / 4000000000000) 1 (IntervalRat.scale (299 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-51146063807 / 1000000000000) (-51146059296 / 1000000000000), orderedInterval (17606936803 / 1000000000000) (17606941313 / 1000000000000)))) (orderedInterval (-198313152 / 1000000000000) (-198312978 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate275_chunkChecks1_1 :
    compactCertificate275.chunkChecks (1 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 1) <| besselDerivativeNearFromState (1337168650544701 / 4000000000000) 1 (IntervalRat.scale (299 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (38347716473 / 1000000000000) (38347757490 / 1000000000000), orderedInterval (-20885992418 / 1000000000000) (-20885951401 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 1) <| besselDerivativeNearFromState (772014680343829 / 4000000000000) 1 (IntervalRat.scale (299 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-48025159299 / 1000000000000) (-48025113850 / 1000000000000), orderedInterval (31621486964 / 1000000000000) (31621532413 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 1) <| besselDerivativeNearFromState (1369953597833561 / 4000000000000) 1 (IntervalRat.scale (299 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-32099643987 / 1000000000000) (-32099643986 / 1000000000000), orderedInterval (-28735414554 / 1000000000000) (-28735414553 / 1000000000000)))) (orderedInterval (1965028907 / 1000000000000) (1965049675 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 1) <| besselDerivativeNearFromState (1279988356802909 / 4000000000000) 1 (IntervalRat.scale (299 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (14859734049 / 1000000000000) (14859734050 / 1000000000000), orderedInterval (42032043710 / 1000000000000) (42032043711 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 1) <| besselDerivativeNearFromState (913460088527597 / 4000000000000) 1 (IntervalRat.scale (299 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (9784341011 / 1000000000000) (9784341054 / 1000000000000), orderedInterval (-51905926894 / 1000000000000) (-51905926851 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 1) <| besselDerivativeNearFromState (1035766382925963 / 4000000000000) 1 (IntervalRat.scale (299 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (42397319900 / 1000000000000) (42397364518 / 1000000000000), orderedInterval (-25791982889 / 1000000000000) (-25791938271 / 1000000000000)))) (orderedInterval (-8895782947 / 1000000000000) (-8895782520 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 1) <| besselDerivativeNearFromState (863514026009947 / 4000000000000) 1 (IntervalRat.scale (299 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (5776131051 / 1000000000000) (5776131065 / 1000000000000), orderedInterval (-54009827181 / 1000000000000) (-54009827167 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 1) <| besselDerivativeNearFromState (762940829732887 / 4000000000000) 1 (IntervalRat.scale (299 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (6755582261 / 1000000000000) (6755582281 / 1000000000000), orderedInterval (-57394431947 / 1000000000000) (-57394431927 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 1) <| besselDerivativeNearFromState (221129989503813 / 800000000000) 1 (IntervalRat.scale (299 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (32263290655 / 1000000000000) (32263290656 / 1000000000000), orderedInterval (35469539950 / 1000000000000) (35469539951 / 1000000000000)))) (orderedInterval (4968926240 / 1000000000000) (4968926263 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate275_chunkChecks1_2 :
    compactCertificate275.chunkChecks (1 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 1) <| besselDerivativeNearFromState (611657188401311 / 4000000000000) 1 (IntervalRat.scale (299 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (15284783489 / 1000000000000) (15284783645 / 1000000000000), orderedInterval (-62736824384 / 1000000000000) (-62736824228 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 1) <| besselDerivativeNearFromState (518508572525671 / 4000000000000) 1 (IntervalRat.scale (299 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-70035306478 / 1000000000000) (-70035306409 / 1000000000000), orderedInterval (2756184659 / 1000000000000) (2756184727 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 1) <| besselDerivativeNearFromState (324458589561613 / 4000000000000) 1 (IntervalRat.scale (299 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (19081856571 / 1000000000000) (19081856572 / 1000000000000), orderedInterval (86394882156 / 1000000000000) (86394882157 / 1000000000000)))) (orderedInterval (11651018602 / 1000000000000) (11651018667 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 1) <| besselDerivativeNearFromState (174494908566771 / 4000000000000) 1 (IntervalRat.scale (299 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (49693968996 / 1000000000000) (49693968997 / 1000000000000), orderedInterval (109542135046 / 1000000000000) (109542135047 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 1) <| besselDerivativeNearFromState (473787620853313 / 4000000000000) 1 (IntervalRat.scale (299 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-10902917859 / 1000000000000) (-10902917803 / 1000000000000), orderedInterval (72543603509 / 1000000000000) (72543603565 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 1) <| besselDerivativeNearFromState (646916490925601 / 4000000000000) 1 (IntervalRat.scale (299 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-47096890861 / 1000000000000) (-47096794420 / 1000000000000), orderedInterval (41596950157 / 1000000000000) (41597046598 / 1000000000000)))) (orderedInterval (-5342882163 / 1000000000000) (-5342874149 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 1) <| besselDerivativeNearFromState (273541410438387 / 4000000000000) 1 (IntervalRat.scale (299 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (5196466865 / 1000000000000) (5196466868 / 1000000000000), orderedInterval (96307968868 / 1000000000000) (96307968872 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 1) <| besselDerivativeNearFromState (1111930646867027 / 4000000000000) 1 (IntervalRat.scale (299 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (35447240743 / 1000000000000) (35447292028 / 1000000000000), orderedInterval (-32213944346 / 1000000000000) (-32213893060 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 1) <| besselDerivativeNearFromState (742718140722493 / 4000000000000) 1 (IntervalRat.scale (299 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-52454465507 / 1000000000000) (-52454465506 / 1000000000000), orderedInterval (-25880197975 / 1000000000000) (-25880197974 / 1000000000000)))) (orderedInterval (11172393455 / 1000000000000) (11172401277 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate275_chunkChecks1 :
    compactCertificate275.chunkChecks (1 : Fin 5) 0 9 = true :=
  compactCertificate275.chunkChecks_nine_of_three (1 : Fin 5) compactCertificate275_chunkChecks1_0
    compactCertificate275_chunkChecks1_1 compactCertificate275_chunkChecks1_2

theorem compactCertificate275_chunkChecks2_0 :
    compactCertificate275.chunkChecks (2 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 2) <| besselDerivativeNearFromState (299 / 2) 2 (IntervalRat.scale (299 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-31963649775 / 1000000000000) (-31963645514 / 1000000000000), orderedInterval (56998583629 / 1000000000000) (56998587890 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 2) <| besselDerivativeNearFromState (440484093422399 / 4000000000000) 2 (IntervalRat.scale (299 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-61826310599 / 1000000000000) (-61826310598 / 1000000000000), orderedInterval (-43975134769 / 1000000000000) (-43975134768 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 2) <| besselDerivativeNearFromState (142443505495967 / 800000000000) 2 (IntervalRat.scale (299 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (13730996396 / 1000000000000) (13730996514 / 1000000000000), orderedInterval (-58235599107 / 1000000000000) (-58235598988 / 1000000000000)))) (orderedInterval (11717031330 / 1000000000000) (11717033054 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 2) <| besselDerivativeNearFromState (128532159877693 / 4000000000000) 2 (IntervalRat.scale (299 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (140380188520 / 1000000000000) (140380188527 / 1000000000000), orderedInterval (7966661842 / 1000000000000) (7966661849 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 2) <| besselDerivativeNearFromState (345255460975321 / 4000000000000) 2 (IntervalRat.scale (299 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-65462514763 / 1000000000000) (-65462431205 / 1000000000000), orderedInterval (55969456641 / 1000000000000) (55969540200 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 2) <| besselDerivativeNearFromState (937435738299957 / 4000000000000) 2 (IntervalRat.scale (299 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (23866277347 / 1000000000000) (23866279134 / 1000000000000), orderedInterval (-46384868745 / 1000000000000) (-46384866958 / 1000000000000)))) (orderedInterval (4994113713 / 1000000000000) (4994115084 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 2) <| besselDerivativeNearFromState (690510921950941 / 4000000000000) 2 (IntervalRat.scale (299 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-35521943358 / 1000000000000) (-35521943357 / 1000000000000), orderedInterval (-49151709822 / 1000000000000) (-49151709821 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 2) <| besselDerivativeNearFromState (1183202234144593 / 4000000000000) 2 (IntervalRat.scale (299 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (44388057231 / 1000000000000) (44388057233 / 1000000000000), orderedInterval (13411645391 / 1000000000000) (13411645393 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 2) <| besselDerivativeNearFromState (871541410438387 / 4000000000000) 2 (IntervalRat.scale (299 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-51146063807 / 1000000000000) (-51146059296 / 1000000000000), orderedInterval (17606936803 / 1000000000000) (17606941313 / 1000000000000)))) (orderedInterval (7986764995 / 1000000000000) (7986765255 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate275_chunkChecks2_1 :
    compactCertificate275.chunkChecks (2 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 2) <| besselDerivativeNearFromState (1337168650544701 / 4000000000000) 2 (IntervalRat.scale (299 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (38347716473 / 1000000000000) (38347757490 / 1000000000000), orderedInterval (-20885992418 / 1000000000000) (-20885951401 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 2) <| besselDerivativeNearFromState (772014680343829 / 4000000000000) 2 (IntervalRat.scale (299 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-48025159299 / 1000000000000) (-48025113850 / 1000000000000), orderedInterval (31621486964 / 1000000000000) (31621532413 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 2) <| besselDerivativeNearFromState (1369953597833561 / 4000000000000) 2 (IntervalRat.scale (299 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-32099643987 / 1000000000000) (-32099643986 / 1000000000000), orderedInterval (-28735414554 / 1000000000000) (-28735414553 / 1000000000000)))) (orderedInterval (63935215161 / 1000000000000) (63935257617 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 2) <| besselDerivativeNearFromState (1279988356802909 / 4000000000000) 2 (IntervalRat.scale (299 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (14859734049 / 1000000000000) (14859734050 / 1000000000000), orderedInterval (42032043710 / 1000000000000) (42032043711 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 2) <| besselDerivativeNearFromState (913460088527597 / 4000000000000) 2 (IntervalRat.scale (299 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (9784341011 / 1000000000000) (9784341054 / 1000000000000), orderedInterval (-51905926894 / 1000000000000) (-51905926851 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 2) <| besselDerivativeNearFromState (1035766382925963 / 4000000000000) 2 (IntervalRat.scale (299 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (42397319900 / 1000000000000) (42397364518 / 1000000000000), orderedInterval (-25791982889 / 1000000000000) (-25791938271 / 1000000000000)))) (orderedInterval (-226656947 / 1000000000000) (-226656209 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 2) <| besselDerivativeNearFromState (863514026009947 / 4000000000000) 2 (IntervalRat.scale (299 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (5776131051 / 1000000000000) (5776131065 / 1000000000000), orderedInterval (-54009827181 / 1000000000000) (-54009827167 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 2) <| besselDerivativeNearFromState (762940829732887 / 4000000000000) 2 (IntervalRat.scale (299 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (6755582261 / 1000000000000) (6755582281 / 1000000000000), orderedInterval (-57394431947 / 1000000000000) (-57394431927 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 2) <| besselDerivativeNearFromState (221129989503813 / 800000000000) 2 (IntervalRat.scale (299 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (32263290655 / 1000000000000) (32263290656 / 1000000000000), orderedInterval (35469539950 / 1000000000000) (35469539951 / 1000000000000)))) (orderedInterval (-2366937839 / 1000000000000) (-2366937805 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate275_chunkChecks2_2 :
    compactCertificate275.chunkChecks (2 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 2) <| besselDerivativeNearFromState (611657188401311 / 4000000000000) 2 (IntervalRat.scale (299 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (15284783489 / 1000000000000) (15284783645 / 1000000000000), orderedInterval (-62736824384 / 1000000000000) (-62736824228 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 2) <| besselDerivativeNearFromState (518508572525671 / 4000000000000) 2 (IntervalRat.scale (299 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-70035306478 / 1000000000000) (-70035306409 / 1000000000000), orderedInterval (2756184659 / 1000000000000) (2756184727 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 2) <| besselDerivativeNearFromState (324458589561613 / 4000000000000) 2 (IntervalRat.scale (299 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (19081856571 / 1000000000000) (19081856572 / 1000000000000), orderedInterval (86394882156 / 1000000000000) (86394882157 / 1000000000000)))) (orderedInterval (-684165709 / 1000000000000) (-684165646 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 2) <| besselDerivativeNearFromState (174494908566771 / 4000000000000) 2 (IntervalRat.scale (299 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (49693968996 / 1000000000000) (49693968997 / 1000000000000), orderedInterval (109542135046 / 1000000000000) (109542135047 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 2) <| besselDerivativeNearFromState (473787620853313 / 4000000000000) 2 (IntervalRat.scale (299 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-10902917859 / 1000000000000) (-10902917803 / 1000000000000), orderedInterval (72543603509 / 1000000000000) (72543603565 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 2) <| besselDerivativeNearFromState (646916490925601 / 4000000000000) 2 (IntervalRat.scale (299 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-47096890861 / 1000000000000) (-47096794420 / 1000000000000), orderedInterval (41596950157 / 1000000000000) (41597046598 / 1000000000000)))) (orderedInterval (-4265511444 / 1000000000000) (-4265502724 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 2) <| besselDerivativeNearFromState (273541410438387 / 4000000000000) 2 (IntervalRat.scale (299 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (5196466865 / 1000000000000) (5196466868 / 1000000000000), orderedInterval (96307968868 / 1000000000000) (96307968872 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 2) <| besselDerivativeNearFromState (1111930646867027 / 4000000000000) 2 (IntervalRat.scale (299 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (35447240743 / 1000000000000) (35447292028 / 1000000000000), orderedInterval (-32213944346 / 1000000000000) (-32213893060 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 2) <| besselDerivativeNearFromState (742718140722493 / 4000000000000) 2 (IntervalRat.scale (299 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-52454465507 / 1000000000000) (-52454465506 / 1000000000000), orderedInterval (-25880197975 / 1000000000000) (-25880197974 / 1000000000000)))) (orderedInterval (-5286759615 / 1000000000000) (-5286745043 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate275_chunkChecks2 :
    compactCertificate275.chunkChecks (2 : Fin 5) 0 9 = true :=
  compactCertificate275.chunkChecks_nine_of_three (2 : Fin 5) compactCertificate275_chunkChecks2_0
    compactCertificate275_chunkChecks2_1 compactCertificate275_chunkChecks2_2

theorem compactCertificate275_chunkChecks3_0 :
    compactCertificate275.chunkChecks (3 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 3) <| besselDerivativeNearFromState (299 / 2) 3 (IntervalRat.scale (299 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-31963649775 / 1000000000000) (-31963645514 / 1000000000000), orderedInterval (56998583629 / 1000000000000) (56998587890 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 3) <| besselDerivativeNearFromState (440484093422399 / 4000000000000) 3 (IntervalRat.scale (299 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-61826310599 / 1000000000000) (-61826310598 / 1000000000000), orderedInterval (-43975134769 / 1000000000000) (-43975134768 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 3) <| besselDerivativeNearFromState (142443505495967 / 800000000000) 3 (IntervalRat.scale (299 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (13730996396 / 1000000000000) (13730996514 / 1000000000000), orderedInterval (-58235599107 / 1000000000000) (-58235598988 / 1000000000000)))) (orderedInterval (-16732774740 / 1000000000000) (-16732773011 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 3) <| besselDerivativeNearFromState (128532159877693 / 4000000000000) 3 (IntervalRat.scale (299 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (140380188520 / 1000000000000) (140380188527 / 1000000000000), orderedInterval (7966661842 / 1000000000000) (7966661849 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 3) <| besselDerivativeNearFromState (345255460975321 / 4000000000000) 3 (IntervalRat.scale (299 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-65462514763 / 1000000000000) (-65462431205 / 1000000000000), orderedInterval (55969456641 / 1000000000000) (55969540200 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 3) <| besselDerivativeNearFromState (937435738299957 / 4000000000000) 3 (IntervalRat.scale (299 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (23866277347 / 1000000000000) (23866279134 / 1000000000000), orderedInterval (-46384868745 / 1000000000000) (-46384866958 / 1000000000000)))) (orderedInterval (-13128466202 / 1000000000000) (-13128465074 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 3) <| besselDerivativeNearFromState (690510921950941 / 4000000000000) 3 (IntervalRat.scale (299 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-35521943358 / 1000000000000) (-35521943357 / 1000000000000), orderedInterval (-49151709822 / 1000000000000) (-49151709821 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 3) <| besselDerivativeNearFromState (1183202234144593 / 4000000000000) 3 (IntervalRat.scale (299 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (44388057231 / 1000000000000) (44388057233 / 1000000000000), orderedInterval (13411645391 / 1000000000000) (13411645393 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 3) <| besselDerivativeNearFromState (871541410438387 / 4000000000000) 3 (IntervalRat.scale (299 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-51146063807 / 1000000000000) (-51146059296 / 1000000000000), orderedInterval (17606936803 / 1000000000000) (17606941313 / 1000000000000)))) (orderedInterval (1833513332 / 1000000000000) (1833513719 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate275_chunkChecks3_1 :
    compactCertificate275.chunkChecks (3 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 3) <| besselDerivativeNearFromState (1337168650544701 / 4000000000000) 3 (IntervalRat.scale (299 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (38347716473 / 1000000000000) (38347757490 / 1000000000000), orderedInterval (-20885992418 / 1000000000000) (-20885951401 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 3) <| besselDerivativeNearFromState (772014680343829 / 4000000000000) 3 (IntervalRat.scale (299 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-48025159299 / 1000000000000) (-48025113850 / 1000000000000), orderedInterval (31621486964 / 1000000000000) (31621532413 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 3) <| besselDerivativeNearFromState (1369953597833561 / 4000000000000) 3 (IntervalRat.scale (299 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-32099643987 / 1000000000000) (-32099643986 / 1000000000000), orderedInterval (-28735414554 / 1000000000000) (-28735414553 / 1000000000000)))) (orderedInterval (2151955515 / 1000000000000) (2152045104 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 3) <| besselDerivativeNearFromState (1279988356802909 / 4000000000000) 3 (IntervalRat.scale (299 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (14859734049 / 1000000000000) (14859734050 / 1000000000000), orderedInterval (42032043710 / 1000000000000) (42032043711 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 3) <| besselDerivativeNearFromState (913460088527597 / 4000000000000) 3 (IntervalRat.scale (299 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (9784341011 / 1000000000000) (9784341054 / 1000000000000), orderedInterval (-51905926894 / 1000000000000) (-51905926851 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 3) <| besselDerivativeNearFromState (1035766382925963 / 4000000000000) 3 (IntervalRat.scale (299 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (42397319900 / 1000000000000) (42397364518 / 1000000000000), orderedInterval (-25791982889 / 1000000000000) (-25791938271 / 1000000000000)))) (orderedInterval (24258713201 / 1000000000000) (24258714475 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 3) <| besselDerivativeNearFromState (863514026009947 / 4000000000000) 3 (IntervalRat.scale (299 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (5776131051 / 1000000000000) (5776131065 / 1000000000000), orderedInterval (-54009827181 / 1000000000000) (-54009827167 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 3) <| besselDerivativeNearFromState (762940829732887 / 4000000000000) 3 (IntervalRat.scale (299 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (6755582261 / 1000000000000) (6755582281 / 1000000000000), orderedInterval (-57394431947 / 1000000000000) (-57394431927 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 3) <| besselDerivativeNearFromState (221129989503813 / 800000000000) 3 (IntervalRat.scale (299 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (32263290655 / 1000000000000) (32263290656 / 1000000000000), orderedInterval (35469539950 / 1000000000000) (35469539951 / 1000000000000)))) (orderedInterval (-10666879990 / 1000000000000) (-10666879939 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate275_chunkChecks3_2 :
    compactCertificate275.chunkChecks (3 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 3) <| besselDerivativeNearFromState (611657188401311 / 4000000000000) 3 (IntervalRat.scale (299 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (15284783489 / 1000000000000) (15284783645 / 1000000000000), orderedInterval (-62736824384 / 1000000000000) (-62736824228 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 3) <| besselDerivativeNearFromState (518508572525671 / 4000000000000) 3 (IntervalRat.scale (299 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-70035306478 / 1000000000000) (-70035306409 / 1000000000000), orderedInterval (2756184659 / 1000000000000) (2756184727 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 3) <| besselDerivativeNearFromState (324458589561613 / 4000000000000) 3 (IntervalRat.scale (299 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (19081856571 / 1000000000000) (19081856572 / 1000000000000), orderedInterval (86394882156 / 1000000000000) (86394882157 / 1000000000000)))) (orderedInterval (-11076691986 / 1000000000000) (-11076691924 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 3) <| besselDerivativeNearFromState (174494908566771 / 4000000000000) 3 (IntervalRat.scale (299 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (49693968996 / 1000000000000) (49693968997 / 1000000000000), orderedInterval (109542135046 / 1000000000000) (109542135047 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 3) <| besselDerivativeNearFromState (473787620853313 / 4000000000000) 3 (IntervalRat.scale (299 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-10902917859 / 1000000000000) (-10902917803 / 1000000000000), orderedInterval (72543603509 / 1000000000000) (72543603565 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 3) <| besselDerivativeNearFromState (646916490925601 / 4000000000000) 3 (IntervalRat.scale (299 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-47096890861 / 1000000000000) (-47096794420 / 1000000000000), orderedInterval (41596950157 / 1000000000000) (41597046598 / 1000000000000)))) (orderedInterval (4933057204 / 1000000000000) (4933066637 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 3) <| besselDerivativeNearFromState (273541410438387 / 4000000000000) 3 (IntervalRat.scale (299 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (5196466865 / 1000000000000) (5196466868 / 1000000000000), orderedInterval (96307968868 / 1000000000000) (96307968872 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 3) <| besselDerivativeNearFromState (1111930646867027 / 4000000000000) 3 (IntervalRat.scale (299 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (35447240743 / 1000000000000) (35447292028 / 1000000000000), orderedInterval (-32213944346 / 1000000000000) (-32213893060 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 3) <| besselDerivativeNearFromState (742718140722493 / 4000000000000) 3 (IntervalRat.scale (299 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-52454465507 / 1000000000000) (-52454465506 / 1000000000000), orderedInterval (-25880197975 / 1000000000000) (-25880197974 / 1000000000000)))) (orderedInterval (-26180912965 / 1000000000000) (-26180885896 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate275_chunkChecks3 :
    compactCertificate275.chunkChecks (3 : Fin 5) 0 9 = true :=
  compactCertificate275.chunkChecks_nine_of_three (3 : Fin 5) compactCertificate275_chunkChecks3_0
    compactCertificate275_chunkChecks3_1 compactCertificate275_chunkChecks3_2

theorem compactCertificate275_chunkChecks4_0 :
    compactCertificate275.chunkChecks (4 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 4) <| besselDerivativeNearFromState (299 / 2) 4 (IntervalRat.scale (299 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-31963649775 / 1000000000000) (-31963645514 / 1000000000000), orderedInterval (56998583629 / 1000000000000) (56998587890 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 4) <| besselDerivativeNearFromState (440484093422399 / 4000000000000) 4 (IntervalRat.scale (299 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-61826310599 / 1000000000000) (-61826310598 / 1000000000000), orderedInterval (-43975134769 / 1000000000000) (-43975134768 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 4) <| besselDerivativeNearFromState (142443505495967 / 800000000000) 4 (IntervalRat.scale (299 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (13730996396 / 1000000000000) (13730996514 / 1000000000000), orderedInterval (-58235599107 / 1000000000000) (-58235598988 / 1000000000000)))) (orderedInterval (-10993262066 / 1000000000000) (-10993260322 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 4) <| besselDerivativeNearFromState (128532159877693 / 4000000000000) 4 (IntervalRat.scale (299 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (140380188520 / 1000000000000) (140380188527 / 1000000000000), orderedInterval (7966661842 / 1000000000000) (7966661849 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 4) <| besselDerivativeNearFromState (345255460975321 / 4000000000000) 4 (IntervalRat.scale (299 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-65462514763 / 1000000000000) (-65462431205 / 1000000000000), orderedInterval (55969456641 / 1000000000000) (55969540200 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 4) <| besselDerivativeNearFromState (937435738299957 / 4000000000000) 4 (IntervalRat.scale (299 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (23866277347 / 1000000000000) (23866279134 / 1000000000000), orderedInterval (-46384868745 / 1000000000000) (-46384866958 / 1000000000000)))) (orderedInterval (-10338921852 / 1000000000000) (-10338920665 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 4) <| besselDerivativeNearFromState (690510921950941 / 4000000000000) 4 (IntervalRat.scale (299 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-35521943358 / 1000000000000) (-35521943357 / 1000000000000), orderedInterval (-49151709822 / 1000000000000) (-49151709821 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 4) <| besselDerivativeNearFromState (1183202234144593 / 4000000000000) 4 (IntervalRat.scale (299 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (44388057231 / 1000000000000) (44388057233 / 1000000000000), orderedInterval (13411645391 / 1000000000000) (13411645393 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 4) <| besselDerivativeNearFromState (871541410438387 / 4000000000000) 4 (IntervalRat.scale (299 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-51146063807 / 1000000000000) (-51146059296 / 1000000000000), orderedInterval (17606936803 / 1000000000000) (17606941313 / 1000000000000)))) (orderedInterval (-26584194970 / 1000000000000) (-26584194384 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate275_chunkChecks4_1 :
    compactCertificate275.chunkChecks (4 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 4) <| besselDerivativeNearFromState (1337168650544701 / 4000000000000) 4 (IntervalRat.scale (299 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (38347716473 / 1000000000000) (38347757490 / 1000000000000), orderedInterval (-20885992418 / 1000000000000) (-20885951401 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 4) <| besselDerivativeNearFromState (772014680343829 / 4000000000000) 4 (IntervalRat.scale (299 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-48025159299 / 1000000000000) (-48025113850 / 1000000000000), orderedInterval (31621486964 / 1000000000000) (31621532413 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 4) <| besselDerivativeNearFromState (1369953597833561 / 4000000000000) 4 (IntervalRat.scale (299 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-32099643987 / 1000000000000) (-32099643986 / 1000000000000), orderedInterval (-28735414554 / 1000000000000) (-28735414553 / 1000000000000)))) (orderedInterval (-305943442558 / 1000000000000) (-305943248532 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 4) <| besselDerivativeNearFromState (1279988356802909 / 4000000000000) 4 (IntervalRat.scale (299 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (14859734049 / 1000000000000) (14859734050 / 1000000000000), orderedInterval (42032043710 / 1000000000000) (42032043711 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 4) <| besselDerivativeNearFromState (913460088527597 / 4000000000000) 4 (IntervalRat.scale (299 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (9784341011 / 1000000000000) (9784341054 / 1000000000000), orderedInterval (-51905926894 / 1000000000000) (-51905926851 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 4) <| besselDerivativeNearFromState (1035766382925963 / 4000000000000) 4 (IntervalRat.scale (299 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (42397319900 / 1000000000000) (42397364518 / 1000000000000), orderedInterval (-25791982889 / 1000000000000) (-25791938271 / 1000000000000)))) (orderedInterval (-2849094316 / 1000000000000) (-2849092104 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 4) <| besselDerivativeNearFromState (863514026009947 / 4000000000000) 4 (IntervalRat.scale (299 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (5776131051 / 1000000000000) (5776131065 / 1000000000000), orderedInterval (-54009827181 / 1000000000000) (-54009827167 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 4) <| besselDerivativeNearFromState (762940829732887 / 4000000000000) 4 (IntervalRat.scale (299 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (6755582261 / 1000000000000) (6755582281 / 1000000000000), orderedInterval (-57394431947 / 1000000000000) (-57394431927 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 4) <| besselDerivativeNearFromState (221129989503813 / 800000000000) 4 (IntervalRat.scale (299 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (32263290655 / 1000000000000) (32263290656 / 1000000000000), orderedInterval (35469539950 / 1000000000000) (35469539951 / 1000000000000)))) (orderedInterval (9061740865 / 1000000000000) (9061740945 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate275_chunkChecks4_2 :
    compactCertificate275.chunkChecks (4 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 4) <| besselDerivativeNearFromState (611657188401311 / 4000000000000) 4 (IntervalRat.scale (299 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (15284783489 / 1000000000000) (15284783645 / 1000000000000), orderedInterval (-62736824384 / 1000000000000) (-62736824228 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 4) <| besselDerivativeNearFromState (518508572525671 / 4000000000000) 4 (IntervalRat.scale (299 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-70035306478 / 1000000000000) (-70035306409 / 1000000000000), orderedInterval (2756184659 / 1000000000000) (2756184727 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 4) <| besselDerivativeNearFromState (324458589561613 / 4000000000000) 4 (IntervalRat.scale (299 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (19081856571 / 1000000000000) (19081856572 / 1000000000000), orderedInterval (86394882156 / 1000000000000) (86394882157 / 1000000000000)))) (orderedInterval (-232422421 / 1000000000000) (-232422359 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 4) <| besselDerivativeNearFromState (174494908566771 / 4000000000000) 4 (IntervalRat.scale (299 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (49693968996 / 1000000000000) (49693968997 / 1000000000000), orderedInterval (109542135046 / 1000000000000) (109542135047 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 4) <| besselDerivativeNearFromState (473787620853313 / 4000000000000) 4 (IntervalRat.scale (299 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-10902917859 / 1000000000000) (-10902917803 / 1000000000000), orderedInterval (72543603509 / 1000000000000) (72543603565 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 4) <| besselDerivativeNearFromState (646916490925601 / 4000000000000) 4 (IntervalRat.scale (299 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-47096890861 / 1000000000000) (-47096794420 / 1000000000000), orderedInterval (41596950157 / 1000000000000) (41597046598 / 1000000000000)))) (orderedInterval (4968061097 / 1000000000000) (4968071363 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 4) <| besselDerivativeNearFromState (273541410438387 / 4000000000000) 4 (IntervalRat.scale (299 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (5196466865 / 1000000000000) (5196466868 / 1000000000000), orderedInterval (96307968868 / 1000000000000) (96307968872 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 4) <| besselDerivativeNearFromState (1111930646867027 / 4000000000000) 4 (IntervalRat.scale (299 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (35447240743 / 1000000000000) (35447292028 / 1000000000000), orderedInterval (-32213944346 / 1000000000000) (-32213893060 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 4) <| besselDerivativeNearFromState (742718140722493 / 4000000000000) 4 (IntervalRat.scale (299 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-52454465507 / 1000000000000) (-52454465506 / 1000000000000), orderedInterval (-25880197975 / 1000000000000) (-25880197974 / 1000000000000)))) (orderedInterval (-10722004296 / 1000000000000) (-10721953822 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate275_chunkChecks4 :
    compactCertificate275.chunkChecks (4 : Fin 5) 0 9 = true :=
  compactCertificate275.chunkChecks_nine_of_three (4 : Fin 5) compactCertificate275_chunkChecks4_0
    compactCertificate275_chunkChecks4_1 compactCertificate275_chunkChecks4_2

theorem compactCertificate275_chunks :
    ∀ r : Fin 5, ∀ b, compactCertificate275.chunkCheck r b = true :=
  compactCertificate275.chunkChecks_all (by
    intro r
    fin_cases r
    · exact compactCertificate275_chunkChecks0
    · exact compactCertificate275_chunkChecks1
    · exact compactCertificate275_chunkChecks2
    · exact compactCertificate275_chunkChecks3
    · exact compactCertificate275_chunkChecks4)

theorem compactCertificate275_coefficient0 :
    compactCertificate275.coefficientCheck (0 : Fin 5) = true := by
  norm_num [CompactCertificate.coefficientCheck, intervalFinSumHull,
    compactCertificate275, rationalIntervalSubset, orderedInterval, Fin.sum_univ_succ]

theorem compactCertificate275_coefficient1 :
    compactCertificate275.coefficientCheck (1 : Fin 5) = true := by
  norm_num [CompactCertificate.coefficientCheck, intervalFinSumHull,
    compactCertificate275, rationalIntervalSubset, orderedInterval, Fin.sum_univ_succ]

theorem compactCertificate275_coefficient2 :
    compactCertificate275.coefficientCheck (2 : Fin 5) = true := by
  norm_num [CompactCertificate.coefficientCheck, intervalFinSumHull,
    compactCertificate275, rationalIntervalSubset, orderedInterval, Fin.sum_univ_succ]

theorem compactCertificate275_coefficient3 :
    compactCertificate275.coefficientCheck (3 : Fin 5) = true := by
  norm_num [CompactCertificate.coefficientCheck, intervalFinSumHull,
    compactCertificate275, rationalIntervalSubset, orderedInterval, Fin.sum_univ_succ]

theorem compactCertificate275_coefficient4 :
    compactCertificate275.coefficientCheck (4 : Fin 5) = true := by
  norm_num [CompactCertificate.coefficientCheck, intervalFinSumHull,
    compactCertificate275, rationalIntervalSubset, orderedInterval, Fin.sum_univ_succ]

theorem compactCertificate275_coefficients : ∀ r : Fin 5,
    compactCertificate275.coefficientCheck r = true := by
  intro r
  fin_cases r
  · exact compactCertificate275_coefficient0
  · exact compactCertificate275_coefficient1
  · exact compactCertificate275_coefficient2
  · exact compactCertificate275_coefficient3
  · exact compactCertificate275_coefficient4

theorem compactCertificate275_lower : (1 : ℚ) ≤ compactCertificate275.output.lo := by
  norm_num [CompactCertificate.output, CompactCertificate.interval,
    CompactCertificate.coefficientTargetNat, compactCertificate275, dualConstant,
    intervalTaylorSum, intervalPow, intervalSub, intervalMaxAbs, widenInterval,
    rationalErrorInterval, orderedInterval, IntervalRat.add, IntervalRat.mul, IntervalRat.scale,
    IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4]

theorem compactCertificate275_proves {t : ℝ} (ht : t ∈ compactCertificate275.interval) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t :=
  compactCertificate275.proves compactCertificate275_states compactCertificate275_chunks
    compactCertificate275_coefficients compactCertificate275_lower ht

end Erdos232
