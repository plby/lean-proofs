/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, OpenAI Codex
-/
import ErdosProblems.Erdos232.CompactBase

open LeanCert.Core
namespace Erdos232

def compactCertificate251 : CompactCertificate where
  left := 126
  right := 127
  center := 253 / 2
  grid := fun i =>
    match i.val with
    | 0 => 40
    | 1 => 30
    | 2 => 48
    | 3 => 9
    | 4 => 23
    | 5 => 63
    | 6 => 47
    | 7 => 80
    | 8 => 59
    | 9 => 90
    | 10 => 52
    | 11 => 92
    | 12 => 86
    | 13 => 62
    | 14 => 70
    | 15 => 58
    | 16 => 51
    | 17 => 74
    | 18 => 41
    | 19 => 35
    | 20 => 22
    | 21 => 12
    | 22 => 32
    | 23 => 44
    | 24 => 18
    | 25 => 75
    | _ => 50
  point := fun i =>
    match i.val with
    | 0 => 253 / 2
    | 1 => 372717309818953 / 4000000000000
    | 2 => 120529120035049 / 800000000000
    | 3 => 108757981434971 / 4000000000000
    | 4 => 292139236209887 / 4000000000000
    | 5 => 793214855484579 / 4000000000000
    | 6 => 584278472420027 / 4000000000000
    | 7 => 1001171121199271 / 4000000000000
    | 8 => 737458116524789 / 4000000000000
    | 9 => 1131450396614747 / 4000000000000
    | 10 => 653243191060163 / 4000000000000
    | 11 => 1159191505859167 / 4000000000000
    | 12 => 1083067071140923 / 4000000000000
    | 13 => 772927767215659 / 4000000000000
    | 14 => 876417708629661 / 4000000000000
    | 15 => 730665714316109 / 4000000000000
    | 16 => 645565317466289 / 4000000000000
    | 17 => 187109991118611 / 800000000000
    | 18 => 517556082493417 / 4000000000000
    | 19 => 438738022906337 / 4000000000000
    | 20 => 274541883475211 / 4000000000000
    | 21 => 147649538018037 / 4000000000000
    | 22 => 400897217645111 / 4000000000000
    | 23 => 547390876937047 / 4000000000000
    | 24 => 231458116524789 / 4000000000000
    | 25 => 940864393502869 / 4000000000000
    | _ => 628453811380571 / 4000000000000
  state := fun i =>
    match i.val with
    | 0 => (orderedInterval (70851983789 / 1000000000000) (70851983872 / 1000000000000), orderedInterval (-3819060683 / 1000000000000) (-3819060600 / 1000000000000))
    | 1 => (orderedInterval (-23191536638 / 1000000000000) (-23191536218 / 1000000000000), orderedInterval (79461918499 / 1000000000000) (79461918919 / 1000000000000))
    | 2 => (orderedInterval (39314553733 / 1000000000000) (39314553734 / 1000000000000), orderedInterval (51637011127 / 1000000000000) (51637011128 / 1000000000000))
    | 3 => (orderedInterval (45805134655 / 1000000000000) (45805135435 / 1000000000000), orderedInterval (-146853395218 / 1000000000000) (-146853394438 / 1000000000000))
    | 4 => (orderedInterval (-93358250146 / 1000000000000) (-93358250123 / 1000000000000), orderedInterval (-194764547 / 1000000000000) (-194764524 / 1000000000000))
    | 5 => (orderedInterval (-52128307048 / 1000000000000) (-52128307047 / 1000000000000), orderedInterval (-22071257978 / 1000000000000) (-22071257977 / 1000000000000))
    | 6 => (orderedInterval (47389912036 / 1000000000000) (47389980409 / 1000000000000), orderedInterval (-46124441484 / 1000000000000) (-46124373111 / 1000000000000))
    | 7 => (orderedInterval (-12464307019 / 1000000000000) (-12464306927 / 1000000000000), orderedInterval (48893558476 / 1000000000000) (48893558568 / 1000000000000))
    | 8 => (orderedInterval (11945856830 / 1000000000000) (11945856908 / 1000000000000), orderedInterval (-57568101380 / 1000000000000) (-57568101303 / 1000000000000))
    | 9 => (orderedInterval (37285666367 / 1000000000000) (37285666368 / 1000000000000), orderedInterval (29266852385 / 1000000000000) (29266852386 / 1000000000000))
    | 10 => (orderedInterval (41757746365 / 1000000000000) (41757746366 / 1000000000000), orderedInterval (46288772153 / 1000000000000) (46288772154 / 1000000000000))
    | 11 => (orderedInterval (46864784603 / 1000000000000) (46864784710 / 1000000000000), orderedInterval (597659941 / 1000000000000) (597660047 / 1000000000000))
    | 12 => (orderedInterval (47559898973 / 1000000000000) (47559898979 / 1000000000000), orderedInterval (9358141111 / 1000000000000) (9358141117 / 1000000000000))
    | 13 => (orderedInterval (-39628281252 / 1000000000000) (-39628241717 / 1000000000000), orderedInterval (41625886904 / 1000000000000) (41625926439 / 1000000000000))
    | 14 => (orderedInterval (-1198217751 / 1000000000000) (-1198217747 / 1000000000000), orderedInterval (53892677351 / 1000000000000) (53892677355 / 1000000000000))
    | 15 => (orderedInterval (55810743629 / 1000000000000) (55810743631 / 1000000000000), orderedInterval (19090412221 / 1000000000000) (19090412222 / 1000000000000))
    | 16 => (orderedInterval (-58233381132 / 1000000000000) (-58233375208 / 1000000000000), orderedInterval (23705548947 / 1000000000000) (23705554871 / 1000000000000))
    | 17 => (orderedInterval (42349038594 / 1000000000000) (42349117747 / 1000000000000), orderedInterval (-30561204692 / 1000000000000) (-30561125538 / 1000000000000))
    | 18 => (orderedInterval (-68708600549 / 1000000000000) (-68708600547 / 1000000000000), orderedInterval (-13851637219 / 1000000000000) (-13851637217 / 1000000000000))
    | 19 => (orderedInterval (-37392137708 / 1000000000000) (-37392137707 / 1000000000000), orderedInterval (-66206946178 / 1000000000000) (-66206946177 / 1000000000000))
    | 20 => (orderedInterval (28829485887 / 1000000000000) (28829485888 / 1000000000000), orderedInterval (91683617171 / 1000000000000) (91683617172 / 1000000000000))
    | 21 => (orderedInterval (-619081718 / 1000000000000) (-619081707 / 1000000000000), orderedInterval (131339938144 / 1000000000000) (131339938156 / 1000000000000))
    | 22 => (orderedInterval (36625649400 / 1000000000000) (36625649401 / 1000000000000), orderedInterval (70602577530 / 1000000000000) (70602577531 / 1000000000000))
    | 23 => (orderedInterval (-38391931127 / 1000000000000) (-38391920133 / 1000000000000), orderedInterval (56514921916 / 1000000000000) (56514932910 / 1000000000000))
    | 24 => (orderedInterval (90587923135 / 1000000000000) (90587938208 / 1000000000000), orderedInterval (-53655431718 / 1000000000000) (-53655416645 / 1000000000000))
    | 25 => (orderedInterval (-19370094324 / 1000000000000) (-19370094323 / 1000000000000), orderedInterval (-48242728557 / 1000000000000) (-48242728556 / 1000000000000))
    | _ => (orderedInterval (46472508253 / 1000000000000) (46472508254 / 1000000000000), orderedInterval (43352446454 / 1000000000000) (43352446455 / 1000000000000))
  chunkTarget := fun r b =>
    match r.val with
    | 0 =>
      match b.val with
      | 0 => orderedInterval (30174168756 / 1000000000000) (30174168802 / 1000000000000)
      | 1 => orderedInterval (-199843334 / 1000000000000) (-199843309 / 1000000000000)
      | 2 => orderedInterval (673156882 / 1000000000000) (673156894 / 1000000000000)
      | 3 => orderedInterval (3130797888 / 1000000000000) (3130797954 / 1000000000000)
      | 4 => orderedInterval (-4599903132 / 1000000000000) (-4599899378 / 1000000000000)
      | 5 => orderedInterval (5061289264 / 1000000000000) (5061291642 / 1000000000000)
      | 6 => orderedInterval (14040930986 / 1000000000000) (14040931019 / 1000000000000)
      | 7 => orderedInterval (2122823731 / 1000000000000) (2122824589 / 1000000000000)
      | _ => orderedInterval (-6596621531 / 1000000000000) (-6596621404 / 1000000000000)
    | 1 =>
      match b.val with
      | 0 => orderedInterval (2640525054 / 1000000000000) (2640525100 / 1000000000000)
      | 1 => orderedInterval (2797995759 / 1000000000000) (2797995779 / 1000000000000)
      | 2 => orderedInterval (-5011600918 / 1000000000000) (-5011600897 / 1000000000000)
      | 3 => orderedInterval (-7006119733 / 1000000000000) (-7006119593 / 1000000000000)
      | 4 => orderedInterval (5178748023 / 1000000000000) (5178753760 / 1000000000000)
      | 5 => orderedInterval (-2859187048 / 1000000000000) (-2859182850 / 1000000000000)
      | 6 => orderedInterval (7134001476 / 1000000000000) (7134001507 / 1000000000000)
      | 7 => orderedInterval (-6662252620 / 1000000000000) (-6662251694 / 1000000000000)
      | _ => orderedInterval (-2948491421 / 1000000000000) (-2948491329 / 1000000000000)
    | 2 =>
      match b.val with
      | 0 => orderedInterval (-31259333454 / 1000000000000) (-31259333407 / 1000000000000)
      | 1 => orderedInterval (-7969626874 / 1000000000000) (-7969626849 / 1000000000000)
      | 2 => orderedInterval (-2078687210 / 1000000000000) (-2078687172 / 1000000000000)
      | 3 => orderedInterval (-6939039051 / 1000000000000) (-6939038747 / 1000000000000)
      | 4 => orderedInterval (12618417786 / 1000000000000) (12618426597 / 1000000000000)
      | 5 => orderedInterval (-10452291127 / 1000000000000) (-10452283588 / 1000000000000)
      | 6 => orderedInterval (-13417336276 / 1000000000000) (-13417336246 / 1000000000000)
      | 7 => orderedInterval (-2870088182 / 1000000000000) (-2870087174 / 1000000000000)
      | _ => orderedInterval (7907936931 / 1000000000000) (7907937025 / 1000000000000)
    | 3 =>
      match b.val with
      | 0 => orderedInterval (-3654007171 / 1000000000000) (-3654007122 / 1000000000000)
      | 1 => orderedInterval (-5995692404 / 1000000000000) (-5995692367 / 1000000000000)
      | 2 => orderedInterval (16004628869 / 1000000000000) (16004628937 / 1000000000000)
      | 3 => orderedInterval (49795430080 / 1000000000000) (49795430752 / 1000000000000)
      | 4 => orderedInterval (-11055289112 / 1000000000000) (-11055275648 / 1000000000000)
      | 5 => orderedInterval (7181558950 / 1000000000000) (7181572563 / 1000000000000)
      | 6 => orderedInterval (-5183019787 / 1000000000000) (-5183019759 / 1000000000000)
      | 7 => orderedInterval (6362574383 / 1000000000000) (6362575472 / 1000000000000)
      | _ => orderedInterval (-9693988904 / 1000000000000) (-9693988781 / 1000000000000)
    | _ =>
      match b.val with
      | 0 => orderedInterval (32717366903 / 1000000000000) (32717366954 / 1000000000000)
      | 1 => orderedInterval (22093520673 / 1000000000000) (22093520730 / 1000000000000)
      | 2 => orderedInterval (6941518282 / 1000000000000) (6941518409 / 1000000000000)
      | 3 => orderedInterval (25673666511 / 1000000000000) (25673668022 / 1000000000000)
      | 4 => orderedInterval (-38194530625 / 1000000000000) (-38194509939 / 1000000000000)
      | 5 => orderedInterval (24188434115 / 1000000000000) (24188458973 / 1000000000000)
      | 6 => orderedInterval (13383161687 / 1000000000000) (13383161715 / 1000000000000)
      | 7 => orderedInterval (3601644777 / 1000000000000) (3601645963 / 1000000000000)
      | _ => orderedInterval (-1722315788 / 1000000000000) (-1722315601 / 1000000000000)
  coefficientTarget := fun i =>
    match i.val with
    | 0 => orderedInterval (43806799510 / 1000000000000) (43806806809 / 1000000000000)
    | 1 => orderedInterval (-6736381428 / 1000000000000) (-6736370217 / 1000000000000)
    | 2 => orderedInterval (-54460047457 / 1000000000000) (-54460029561 / 1000000000000)
    | 3 => orderedInterval (43762194904 / 1000000000000) (43762224047 / 1000000000000)
    | _ => orderedInterval (88682466535 / 1000000000000) (88682515226 / 1000000000000)

theorem compactCertificate251_stateChecks0 :
    compactCertificate251.stateChecks 0 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 40 12 (253 / 2)) (orderedInterval (70851983789 / 1000000000000) (70851983872 / 1000000000000), orderedInterval (-3819060683 / 1000000000000) (-3819060600 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 30 12 (372717309818953 / 4000000000000)) (orderedInterval (-23191536638 / 1000000000000) (-23191536218 / 1000000000000), orderedInterval (79461918499 / 1000000000000) (79461918919 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 48 12 (120529120035049 / 800000000000)) (orderedInterval (39314553733 / 1000000000000) (39314553734 / 1000000000000), orderedInterval (51637011127 / 1000000000000) (51637011128 / 1000000000000))) = true
  norm_num [besselStateAtRationalPoint, besselIntervalStepZero,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, besselZeroTransition,
    besselInitial, besselGridStateAt, besselGridStateBlock00, besselGridStateBlock01,
    besselGridStateBlock02, besselGridStateBlock03, besselGridStateBlock04,
    besselGridStateBlock05, besselGridStateBlock06, besselGridStateBlock07,
    besselGridStateBlock08, besselGridStateBlock09, besselGridStateBlock10,
    besselGridStateBlock11, besselGridStateBlock12, besselGridStateBlock13,
    besselGridStateBlock14, besselGridState009, besselGridState012, besselGridState018, besselGridState022, besselGridState023, besselGridState030, besselGridState032, besselGridState035, besselGridState040, besselGridState041, besselGridState044, besselGridState047, besselGridState048, besselGridState050, besselGridState051, besselGridState052, besselGridState058, besselGridState059, besselGridState062, besselGridState063, besselGridState070, besselGridState074, besselGridState075, besselGridState080, besselGridState086, besselGridState090, besselGridState092, besselStateSubset, linearInterval, widenInterval,
    rationalErrorInterval, rationalIntervalSubset, orderedInterval, Finset.sum_range_succ,
    IntervalRat.add, IntervalRat.mul, IntervalRat.scale, IntervalRat.singleton]

theorem compactCertificate251_stateChecks1 :
    compactCertificate251.stateChecks 3 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 9 12 (108757981434971 / 4000000000000)) (orderedInterval (45805134655 / 1000000000000) (45805135435 / 1000000000000), orderedInterval (-146853395218 / 1000000000000) (-146853394438 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 23 12 (292139236209887 / 4000000000000)) (orderedInterval (-93358250146 / 1000000000000) (-93358250123 / 1000000000000), orderedInterval (-194764547 / 1000000000000) (-194764524 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 63 12 (793214855484579 / 4000000000000)) (orderedInterval (-52128307048 / 1000000000000) (-52128307047 / 1000000000000), orderedInterval (-22071257978 / 1000000000000) (-22071257977 / 1000000000000))) = true
  norm_num [besselStateAtRationalPoint, besselIntervalStepZero,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, besselZeroTransition,
    besselInitial, besselGridStateAt, besselGridStateBlock00, besselGridStateBlock01,
    besselGridStateBlock02, besselGridStateBlock03, besselGridStateBlock04,
    besselGridStateBlock05, besselGridStateBlock06, besselGridStateBlock07,
    besselGridStateBlock08, besselGridStateBlock09, besselGridStateBlock10,
    besselGridStateBlock11, besselGridStateBlock12, besselGridStateBlock13,
    besselGridStateBlock14, besselGridState009, besselGridState012, besselGridState018, besselGridState022, besselGridState023, besselGridState030, besselGridState032, besselGridState035, besselGridState040, besselGridState041, besselGridState044, besselGridState047, besselGridState048, besselGridState050, besselGridState051, besselGridState052, besselGridState058, besselGridState059, besselGridState062, besselGridState063, besselGridState070, besselGridState074, besselGridState075, besselGridState080, besselGridState086, besselGridState090, besselGridState092, besselStateSubset, linearInterval, widenInterval,
    rationalErrorInterval, rationalIntervalSubset, orderedInterval, Finset.sum_range_succ,
    IntervalRat.add, IntervalRat.mul, IntervalRat.scale, IntervalRat.singleton]

theorem compactCertificate251_stateChecks2 :
    compactCertificate251.stateChecks 6 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 47 12 (584278472420027 / 4000000000000)) (orderedInterval (47389912036 / 1000000000000) (47389980409 / 1000000000000), orderedInterval (-46124441484 / 1000000000000) (-46124373111 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 80 12 (1001171121199271 / 4000000000000)) (orderedInterval (-12464307019 / 1000000000000) (-12464306927 / 1000000000000), orderedInterval (48893558476 / 1000000000000) (48893558568 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 59 12 (737458116524789 / 4000000000000)) (orderedInterval (11945856830 / 1000000000000) (11945856908 / 1000000000000), orderedInterval (-57568101380 / 1000000000000) (-57568101303 / 1000000000000))) = true
  norm_num [besselStateAtRationalPoint, besselIntervalStepZero,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, besselZeroTransition,
    besselInitial, besselGridStateAt, besselGridStateBlock00, besselGridStateBlock01,
    besselGridStateBlock02, besselGridStateBlock03, besselGridStateBlock04,
    besselGridStateBlock05, besselGridStateBlock06, besselGridStateBlock07,
    besselGridStateBlock08, besselGridStateBlock09, besselGridStateBlock10,
    besselGridStateBlock11, besselGridStateBlock12, besselGridStateBlock13,
    besselGridStateBlock14, besselGridState009, besselGridState012, besselGridState018, besselGridState022, besselGridState023, besselGridState030, besselGridState032, besselGridState035, besselGridState040, besselGridState041, besselGridState044, besselGridState047, besselGridState048, besselGridState050, besselGridState051, besselGridState052, besselGridState058, besselGridState059, besselGridState062, besselGridState063, besselGridState070, besselGridState074, besselGridState075, besselGridState080, besselGridState086, besselGridState090, besselGridState092, besselStateSubset, linearInterval, widenInterval,
    rationalErrorInterval, rationalIntervalSubset, orderedInterval, Finset.sum_range_succ,
    IntervalRat.add, IntervalRat.mul, IntervalRat.scale, IntervalRat.singleton]

theorem compactCertificate251_stateChecks3 :
    compactCertificate251.stateChecks 9 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 90 12 (1131450396614747 / 4000000000000)) (orderedInterval (37285666367 / 1000000000000) (37285666368 / 1000000000000), orderedInterval (29266852385 / 1000000000000) (29266852386 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 52 12 (653243191060163 / 4000000000000)) (orderedInterval (41757746365 / 1000000000000) (41757746366 / 1000000000000), orderedInterval (46288772153 / 1000000000000) (46288772154 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 92 12 (1159191505859167 / 4000000000000)) (orderedInterval (46864784603 / 1000000000000) (46864784710 / 1000000000000), orderedInterval (597659941 / 1000000000000) (597660047 / 1000000000000))) = true
  norm_num [besselStateAtRationalPoint, besselIntervalStepZero,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, besselZeroTransition,
    besselInitial, besselGridStateAt, besselGridStateBlock00, besselGridStateBlock01,
    besselGridStateBlock02, besselGridStateBlock03, besselGridStateBlock04,
    besselGridStateBlock05, besselGridStateBlock06, besselGridStateBlock07,
    besselGridStateBlock08, besselGridStateBlock09, besselGridStateBlock10,
    besselGridStateBlock11, besselGridStateBlock12, besselGridStateBlock13,
    besselGridStateBlock14, besselGridState009, besselGridState012, besselGridState018, besselGridState022, besselGridState023, besselGridState030, besselGridState032, besselGridState035, besselGridState040, besselGridState041, besselGridState044, besselGridState047, besselGridState048, besselGridState050, besselGridState051, besselGridState052, besselGridState058, besselGridState059, besselGridState062, besselGridState063, besselGridState070, besselGridState074, besselGridState075, besselGridState080, besselGridState086, besselGridState090, besselGridState092, besselStateSubset, linearInterval, widenInterval,
    rationalErrorInterval, rationalIntervalSubset, orderedInterval, Finset.sum_range_succ,
    IntervalRat.add, IntervalRat.mul, IntervalRat.scale, IntervalRat.singleton]

theorem compactCertificate251_stateChecks4 :
    compactCertificate251.stateChecks 12 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 86 12 (1083067071140923 / 4000000000000)) (orderedInterval (47559898973 / 1000000000000) (47559898979 / 1000000000000), orderedInterval (9358141111 / 1000000000000) (9358141117 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 62 12 (772927767215659 / 4000000000000)) (orderedInterval (-39628281252 / 1000000000000) (-39628241717 / 1000000000000), orderedInterval (41625886904 / 1000000000000) (41625926439 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 70 12 (876417708629661 / 4000000000000)) (orderedInterval (-1198217751 / 1000000000000) (-1198217747 / 1000000000000), orderedInterval (53892677351 / 1000000000000) (53892677355 / 1000000000000))) = true
  norm_num [besselStateAtRationalPoint, besselIntervalStepZero,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, besselZeroTransition,
    besselInitial, besselGridStateAt, besselGridStateBlock00, besselGridStateBlock01,
    besselGridStateBlock02, besselGridStateBlock03, besselGridStateBlock04,
    besselGridStateBlock05, besselGridStateBlock06, besselGridStateBlock07,
    besselGridStateBlock08, besselGridStateBlock09, besselGridStateBlock10,
    besselGridStateBlock11, besselGridStateBlock12, besselGridStateBlock13,
    besselGridStateBlock14, besselGridState009, besselGridState012, besselGridState018, besselGridState022, besselGridState023, besselGridState030, besselGridState032, besselGridState035, besselGridState040, besselGridState041, besselGridState044, besselGridState047, besselGridState048, besselGridState050, besselGridState051, besselGridState052, besselGridState058, besselGridState059, besselGridState062, besselGridState063, besselGridState070, besselGridState074, besselGridState075, besselGridState080, besselGridState086, besselGridState090, besselGridState092, besselStateSubset, linearInterval, widenInterval,
    rationalErrorInterval, rationalIntervalSubset, orderedInterval, Finset.sum_range_succ,
    IntervalRat.add, IntervalRat.mul, IntervalRat.scale, IntervalRat.singleton]

theorem compactCertificate251_stateChecks5 :
    compactCertificate251.stateChecks 15 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 58 12 (730665714316109 / 4000000000000)) (orderedInterval (55810743629 / 1000000000000) (55810743631 / 1000000000000), orderedInterval (19090412221 / 1000000000000) (19090412222 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 51 12 (645565317466289 / 4000000000000)) (orderedInterval (-58233381132 / 1000000000000) (-58233375208 / 1000000000000), orderedInterval (23705548947 / 1000000000000) (23705554871 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 74 12 (187109991118611 / 800000000000)) (orderedInterval (42349038594 / 1000000000000) (42349117747 / 1000000000000), orderedInterval (-30561204692 / 1000000000000) (-30561125538 / 1000000000000))) = true
  norm_num [besselStateAtRationalPoint, besselIntervalStepZero,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, besselZeroTransition,
    besselInitial, besselGridStateAt, besselGridStateBlock00, besselGridStateBlock01,
    besselGridStateBlock02, besselGridStateBlock03, besselGridStateBlock04,
    besselGridStateBlock05, besselGridStateBlock06, besselGridStateBlock07,
    besselGridStateBlock08, besselGridStateBlock09, besselGridStateBlock10,
    besselGridStateBlock11, besselGridStateBlock12, besselGridStateBlock13,
    besselGridStateBlock14, besselGridState009, besselGridState012, besselGridState018, besselGridState022, besselGridState023, besselGridState030, besselGridState032, besselGridState035, besselGridState040, besselGridState041, besselGridState044, besselGridState047, besselGridState048, besselGridState050, besselGridState051, besselGridState052, besselGridState058, besselGridState059, besselGridState062, besselGridState063, besselGridState070, besselGridState074, besselGridState075, besselGridState080, besselGridState086, besselGridState090, besselGridState092, besselStateSubset, linearInterval, widenInterval,
    rationalErrorInterval, rationalIntervalSubset, orderedInterval, Finset.sum_range_succ,
    IntervalRat.add, IntervalRat.mul, IntervalRat.scale, IntervalRat.singleton]

theorem compactCertificate251_stateChecks6 :
    compactCertificate251.stateChecks 18 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 41 12 (517556082493417 / 4000000000000)) (orderedInterval (-68708600549 / 1000000000000) (-68708600547 / 1000000000000), orderedInterval (-13851637219 / 1000000000000) (-13851637217 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 35 12 (438738022906337 / 4000000000000)) (orderedInterval (-37392137708 / 1000000000000) (-37392137707 / 1000000000000), orderedInterval (-66206946178 / 1000000000000) (-66206946177 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 22 12 (274541883475211 / 4000000000000)) (orderedInterval (28829485887 / 1000000000000) (28829485888 / 1000000000000), orderedInterval (91683617171 / 1000000000000) (91683617172 / 1000000000000))) = true
  norm_num [besselStateAtRationalPoint, besselIntervalStepZero,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, besselZeroTransition,
    besselInitial, besselGridStateAt, besselGridStateBlock00, besselGridStateBlock01,
    besselGridStateBlock02, besselGridStateBlock03, besselGridStateBlock04,
    besselGridStateBlock05, besselGridStateBlock06, besselGridStateBlock07,
    besselGridStateBlock08, besselGridStateBlock09, besselGridStateBlock10,
    besselGridStateBlock11, besselGridStateBlock12, besselGridStateBlock13,
    besselGridStateBlock14, besselGridState009, besselGridState012, besselGridState018, besselGridState022, besselGridState023, besselGridState030, besselGridState032, besselGridState035, besselGridState040, besselGridState041, besselGridState044, besselGridState047, besselGridState048, besselGridState050, besselGridState051, besselGridState052, besselGridState058, besselGridState059, besselGridState062, besselGridState063, besselGridState070, besselGridState074, besselGridState075, besselGridState080, besselGridState086, besselGridState090, besselGridState092, besselStateSubset, linearInterval, widenInterval,
    rationalErrorInterval, rationalIntervalSubset, orderedInterval, Finset.sum_range_succ,
    IntervalRat.add, IntervalRat.mul, IntervalRat.scale, IntervalRat.singleton]

theorem compactCertificate251_stateChecks7 :
    compactCertificate251.stateChecks 21 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 12 12 (147649538018037 / 4000000000000)) (orderedInterval (-619081718 / 1000000000000) (-619081707 / 1000000000000), orderedInterval (131339938144 / 1000000000000) (131339938156 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 32 12 (400897217645111 / 4000000000000)) (orderedInterval (36625649400 / 1000000000000) (36625649401 / 1000000000000), orderedInterval (70602577530 / 1000000000000) (70602577531 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 44 12 (547390876937047 / 4000000000000)) (orderedInterval (-38391931127 / 1000000000000) (-38391920133 / 1000000000000), orderedInterval (56514921916 / 1000000000000) (56514932910 / 1000000000000))) = true
  norm_num [besselStateAtRationalPoint, besselIntervalStepZero,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, besselZeroTransition,
    besselInitial, besselGridStateAt, besselGridStateBlock00, besselGridStateBlock01,
    besselGridStateBlock02, besselGridStateBlock03, besselGridStateBlock04,
    besselGridStateBlock05, besselGridStateBlock06, besselGridStateBlock07,
    besselGridStateBlock08, besselGridStateBlock09, besselGridStateBlock10,
    besselGridStateBlock11, besselGridStateBlock12, besselGridStateBlock13,
    besselGridStateBlock14, besselGridState009, besselGridState012, besselGridState018, besselGridState022, besselGridState023, besselGridState030, besselGridState032, besselGridState035, besselGridState040, besselGridState041, besselGridState044, besselGridState047, besselGridState048, besselGridState050, besselGridState051, besselGridState052, besselGridState058, besselGridState059, besselGridState062, besselGridState063, besselGridState070, besselGridState074, besselGridState075, besselGridState080, besselGridState086, besselGridState090, besselGridState092, besselStateSubset, linearInterval, widenInterval,
    rationalErrorInterval, rationalIntervalSubset, orderedInterval, Finset.sum_range_succ,
    IntervalRat.add, IntervalRat.mul, IntervalRat.scale, IntervalRat.singleton]

theorem compactCertificate251_stateChecks8 :
    compactCertificate251.stateChecks 24 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 18 12 (231458116524789 / 4000000000000)) (orderedInterval (90587923135 / 1000000000000) (90587938208 / 1000000000000), orderedInterval (-53655431718 / 1000000000000) (-53655416645 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 75 12 (940864393502869 / 4000000000000)) (orderedInterval (-19370094324 / 1000000000000) (-19370094323 / 1000000000000), orderedInterval (-48242728557 / 1000000000000) (-48242728556 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 50 12 (628453811380571 / 4000000000000)) (orderedInterval (46472508253 / 1000000000000) (46472508254 / 1000000000000), orderedInterval (43352446454 / 1000000000000) (43352446455 / 1000000000000))) = true
  norm_num [besselStateAtRationalPoint, besselIntervalStepZero,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, besselZeroTransition,
    besselInitial, besselGridStateAt, besselGridStateBlock00, besselGridStateBlock01,
    besselGridStateBlock02, besselGridStateBlock03, besselGridStateBlock04,
    besselGridStateBlock05, besselGridStateBlock06, besselGridStateBlock07,
    besselGridStateBlock08, besselGridStateBlock09, besselGridStateBlock10,
    besselGridStateBlock11, besselGridStateBlock12, besselGridStateBlock13,
    besselGridStateBlock14, besselGridState009, besselGridState012, besselGridState018, besselGridState022, besselGridState023, besselGridState030, besselGridState032, besselGridState035, besselGridState040, besselGridState041, besselGridState044, besselGridState047, besselGridState048, besselGridState050, besselGridState051, besselGridState052, besselGridState058, besselGridState059, besselGridState062, besselGridState063, besselGridState070, besselGridState074, besselGridState075, besselGridState080, besselGridState086, besselGridState090, besselGridState092, besselStateSubset, linearInterval, widenInterval,
    rationalErrorInterval, rationalIntervalSubset, orderedInterval, Finset.sum_range_succ,
    IntervalRat.add, IntervalRat.mul, IntervalRat.scale, IntervalRat.singleton]

theorem compactCertificate251_states : ∀ j,
    BesselStateValid (compactCertificate251.point j) (compactCertificate251.state j) :=
  compactCertificate251.statesValid_of_checks3 compactCertificate251_stateChecks0
    compactCertificate251_stateChecks1 compactCertificate251_stateChecks2
    compactCertificate251_stateChecks3 compactCertificate251_stateChecks4
    compactCertificate251_stateChecks5 compactCertificate251_stateChecks6
    compactCertificate251_stateChecks7 compactCertificate251_stateChecks8

theorem compactCertificate251_chunkChecks0_0 :
    compactCertificate251.chunkChecks (0 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 0) <| besselDerivativeNearFromState (253 / 2) 0 (IntervalRat.scale (253 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (70851983789 / 1000000000000) (70851983872 / 1000000000000), orderedInterval (-3819060683 / 1000000000000) (-3819060600 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 0) <| besselDerivativeNearFromState (372717309818953 / 4000000000000) 0 (IntervalRat.scale (253 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-23191536638 / 1000000000000) (-23191536218 / 1000000000000), orderedInterval (79461918499 / 1000000000000) (79461918919 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 0) <| besselDerivativeNearFromState (120529120035049 / 800000000000) 0 (IntervalRat.scale (253 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (39314553733 / 1000000000000) (39314553734 / 1000000000000), orderedInterval (51637011127 / 1000000000000) (51637011128 / 1000000000000)))) (orderedInterval (30174168756 / 1000000000000) (30174168802 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 0) <| besselDerivativeNearFromState (108757981434971 / 4000000000000) 0 (IntervalRat.scale (253 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (45805134655 / 1000000000000) (45805135435 / 1000000000000), orderedInterval (-146853395218 / 1000000000000) (-146853394438 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 0) <| besselDerivativeNearFromState (292139236209887 / 4000000000000) 0 (IntervalRat.scale (253 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-93358250146 / 1000000000000) (-93358250123 / 1000000000000), orderedInterval (-194764547 / 1000000000000) (-194764524 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 0) <| besselDerivativeNearFromState (793214855484579 / 4000000000000) 0 (IntervalRat.scale (253 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-52128307048 / 1000000000000) (-52128307047 / 1000000000000), orderedInterval (-22071257978 / 1000000000000) (-22071257977 / 1000000000000)))) (orderedInterval (-199843334 / 1000000000000) (-199843309 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 0) <| besselDerivativeNearFromState (584278472420027 / 4000000000000) 0 (IntervalRat.scale (253 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (47389912036 / 1000000000000) (47389980409 / 1000000000000), orderedInterval (-46124441484 / 1000000000000) (-46124373111 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 0) <| besselDerivativeNearFromState (1001171121199271 / 4000000000000) 0 (IntervalRat.scale (253 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-12464307019 / 1000000000000) (-12464306927 / 1000000000000), orderedInterval (48893558476 / 1000000000000) (48893558568 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 0) <| besselDerivativeNearFromState (737458116524789 / 4000000000000) 0 (IntervalRat.scale (253 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (11945856830 / 1000000000000) (11945856908 / 1000000000000), orderedInterval (-57568101380 / 1000000000000) (-57568101303 / 1000000000000)))) (orderedInterval (673156882 / 1000000000000) (673156894 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate251_chunkChecks0_1 :
    compactCertificate251.chunkChecks (0 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 0) <| besselDerivativeNearFromState (1131450396614747 / 4000000000000) 0 (IntervalRat.scale (253 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (37285666367 / 1000000000000) (37285666368 / 1000000000000), orderedInterval (29266852385 / 1000000000000) (29266852386 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 0) <| besselDerivativeNearFromState (653243191060163 / 4000000000000) 0 (IntervalRat.scale (253 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (41757746365 / 1000000000000) (41757746366 / 1000000000000), orderedInterval (46288772153 / 1000000000000) (46288772154 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 0) <| besselDerivativeNearFromState (1159191505859167 / 4000000000000) 0 (IntervalRat.scale (253 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (46864784603 / 1000000000000) (46864784710 / 1000000000000), orderedInterval (597659941 / 1000000000000) (597660047 / 1000000000000)))) (orderedInterval (3130797888 / 1000000000000) (3130797954 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 0) <| besselDerivativeNearFromState (1083067071140923 / 4000000000000) 0 (IntervalRat.scale (253 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (47559898973 / 1000000000000) (47559898979 / 1000000000000), orderedInterval (9358141111 / 1000000000000) (9358141117 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 0) <| besselDerivativeNearFromState (772927767215659 / 4000000000000) 0 (IntervalRat.scale (253 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-39628281252 / 1000000000000) (-39628241717 / 1000000000000), orderedInterval (41625886904 / 1000000000000) (41625926439 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 0) <| besselDerivativeNearFromState (876417708629661 / 4000000000000) 0 (IntervalRat.scale (253 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-1198217751 / 1000000000000) (-1198217747 / 1000000000000), orderedInterval (53892677351 / 1000000000000) (53892677355 / 1000000000000)))) (orderedInterval (-4599903132 / 1000000000000) (-4599899378 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 0) <| besselDerivativeNearFromState (730665714316109 / 4000000000000) 0 (IntervalRat.scale (253 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (55810743629 / 1000000000000) (55810743631 / 1000000000000), orderedInterval (19090412221 / 1000000000000) (19090412222 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 0) <| besselDerivativeNearFromState (645565317466289 / 4000000000000) 0 (IntervalRat.scale (253 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-58233381132 / 1000000000000) (-58233375208 / 1000000000000), orderedInterval (23705548947 / 1000000000000) (23705554871 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 0) <| besselDerivativeNearFromState (187109991118611 / 800000000000) 0 (IntervalRat.scale (253 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (42349038594 / 1000000000000) (42349117747 / 1000000000000), orderedInterval (-30561204692 / 1000000000000) (-30561125538 / 1000000000000)))) (orderedInterval (5061289264 / 1000000000000) (5061291642 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate251_chunkChecks0_2 :
    compactCertificate251.chunkChecks (0 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 0) <| besselDerivativeNearFromState (517556082493417 / 4000000000000) 0 (IntervalRat.scale (253 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-68708600549 / 1000000000000) (-68708600547 / 1000000000000), orderedInterval (-13851637219 / 1000000000000) (-13851637217 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 0) <| besselDerivativeNearFromState (438738022906337 / 4000000000000) 0 (IntervalRat.scale (253 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-37392137708 / 1000000000000) (-37392137707 / 1000000000000), orderedInterval (-66206946178 / 1000000000000) (-66206946177 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 0) <| besselDerivativeNearFromState (274541883475211 / 4000000000000) 0 (IntervalRat.scale (253 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (28829485887 / 1000000000000) (28829485888 / 1000000000000), orderedInterval (91683617171 / 1000000000000) (91683617172 / 1000000000000)))) (orderedInterval (14040930986 / 1000000000000) (14040931019 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 0) <| besselDerivativeNearFromState (147649538018037 / 4000000000000) 0 (IntervalRat.scale (253 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-619081718 / 1000000000000) (-619081707 / 1000000000000), orderedInterval (131339938144 / 1000000000000) (131339938156 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 0) <| besselDerivativeNearFromState (400897217645111 / 4000000000000) 0 (IntervalRat.scale (253 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (36625649400 / 1000000000000) (36625649401 / 1000000000000), orderedInterval (70602577530 / 1000000000000) (70602577531 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 0) <| besselDerivativeNearFromState (547390876937047 / 4000000000000) 0 (IntervalRat.scale (253 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-38391931127 / 1000000000000) (-38391920133 / 1000000000000), orderedInterval (56514921916 / 1000000000000) (56514932910 / 1000000000000)))) (orderedInterval (2122823731 / 1000000000000) (2122824589 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 0) <| besselDerivativeNearFromState (231458116524789 / 4000000000000) 0 (IntervalRat.scale (253 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (90587923135 / 1000000000000) (90587938208 / 1000000000000), orderedInterval (-53655431718 / 1000000000000) (-53655416645 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 0) <| besselDerivativeNearFromState (940864393502869 / 4000000000000) 0 (IntervalRat.scale (253 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-19370094324 / 1000000000000) (-19370094323 / 1000000000000), orderedInterval (-48242728557 / 1000000000000) (-48242728556 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 0) <| besselDerivativeNearFromState (628453811380571 / 4000000000000) 0 (IntervalRat.scale (253 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (46472508253 / 1000000000000) (46472508254 / 1000000000000), orderedInterval (43352446454 / 1000000000000) (43352446455 / 1000000000000)))) (orderedInterval (-6596621531 / 1000000000000) (-6596621404 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate251_chunkChecks0 :
    compactCertificate251.chunkChecks (0 : Fin 5) 0 9 = true :=
  compactCertificate251.chunkChecks_nine_of_three (0 : Fin 5) compactCertificate251_chunkChecks0_0
    compactCertificate251_chunkChecks0_1 compactCertificate251_chunkChecks0_2

theorem compactCertificate251_chunkChecks1_0 :
    compactCertificate251.chunkChecks (1 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 1) <| besselDerivativeNearFromState (253 / 2) 1 (IntervalRat.scale (253 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (70851983789 / 1000000000000) (70851983872 / 1000000000000), orderedInterval (-3819060683 / 1000000000000) (-3819060600 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 1) <| besselDerivativeNearFromState (372717309818953 / 4000000000000) 1 (IntervalRat.scale (253 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-23191536638 / 1000000000000) (-23191536218 / 1000000000000), orderedInterval (79461918499 / 1000000000000) (79461918919 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 1) <| besselDerivativeNearFromState (120529120035049 / 800000000000) 1 (IntervalRat.scale (253 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (39314553733 / 1000000000000) (39314553734 / 1000000000000), orderedInterval (51637011127 / 1000000000000) (51637011128 / 1000000000000)))) (orderedInterval (2640525054 / 1000000000000) (2640525100 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 1) <| besselDerivativeNearFromState (108757981434971 / 4000000000000) 1 (IntervalRat.scale (253 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (45805134655 / 1000000000000) (45805135435 / 1000000000000), orderedInterval (-146853395218 / 1000000000000) (-146853394438 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 1) <| besselDerivativeNearFromState (292139236209887 / 4000000000000) 1 (IntervalRat.scale (253 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-93358250146 / 1000000000000) (-93358250123 / 1000000000000), orderedInterval (-194764547 / 1000000000000) (-194764524 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 1) <| besselDerivativeNearFromState (793214855484579 / 4000000000000) 1 (IntervalRat.scale (253 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-52128307048 / 1000000000000) (-52128307047 / 1000000000000), orderedInterval (-22071257978 / 1000000000000) (-22071257977 / 1000000000000)))) (orderedInterval (2797995759 / 1000000000000) (2797995779 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 1) <| besselDerivativeNearFromState (584278472420027 / 4000000000000) 1 (IntervalRat.scale (253 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (47389912036 / 1000000000000) (47389980409 / 1000000000000), orderedInterval (-46124441484 / 1000000000000) (-46124373111 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 1) <| besselDerivativeNearFromState (1001171121199271 / 4000000000000) 1 (IntervalRat.scale (253 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-12464307019 / 1000000000000) (-12464306927 / 1000000000000), orderedInterval (48893558476 / 1000000000000) (48893558568 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 1) <| besselDerivativeNearFromState (737458116524789 / 4000000000000) 1 (IntervalRat.scale (253 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (11945856830 / 1000000000000) (11945856908 / 1000000000000), orderedInterval (-57568101380 / 1000000000000) (-57568101303 / 1000000000000)))) (orderedInterval (-5011600918 / 1000000000000) (-5011600897 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate251_chunkChecks1_1 :
    compactCertificate251.chunkChecks (1 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 1) <| besselDerivativeNearFromState (1131450396614747 / 4000000000000) 1 (IntervalRat.scale (253 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (37285666367 / 1000000000000) (37285666368 / 1000000000000), orderedInterval (29266852385 / 1000000000000) (29266852386 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 1) <| besselDerivativeNearFromState (653243191060163 / 4000000000000) 1 (IntervalRat.scale (253 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (41757746365 / 1000000000000) (41757746366 / 1000000000000), orderedInterval (46288772153 / 1000000000000) (46288772154 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 1) <| besselDerivativeNearFromState (1159191505859167 / 4000000000000) 1 (IntervalRat.scale (253 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (46864784603 / 1000000000000) (46864784710 / 1000000000000), orderedInterval (597659941 / 1000000000000) (597660047 / 1000000000000)))) (orderedInterval (-7006119733 / 1000000000000) (-7006119593 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 1) <| besselDerivativeNearFromState (1083067071140923 / 4000000000000) 1 (IntervalRat.scale (253 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (47559898973 / 1000000000000) (47559898979 / 1000000000000), orderedInterval (9358141111 / 1000000000000) (9358141117 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 1) <| besselDerivativeNearFromState (772927767215659 / 4000000000000) 1 (IntervalRat.scale (253 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-39628281252 / 1000000000000) (-39628241717 / 1000000000000), orderedInterval (41625886904 / 1000000000000) (41625926439 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 1) <| besselDerivativeNearFromState (876417708629661 / 4000000000000) 1 (IntervalRat.scale (253 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-1198217751 / 1000000000000) (-1198217747 / 1000000000000), orderedInterval (53892677351 / 1000000000000) (53892677355 / 1000000000000)))) (orderedInterval (5178748023 / 1000000000000) (5178753760 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 1) <| besselDerivativeNearFromState (730665714316109 / 4000000000000) 1 (IntervalRat.scale (253 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (55810743629 / 1000000000000) (55810743631 / 1000000000000), orderedInterval (19090412221 / 1000000000000) (19090412222 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 1) <| besselDerivativeNearFromState (645565317466289 / 4000000000000) 1 (IntervalRat.scale (253 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-58233381132 / 1000000000000) (-58233375208 / 1000000000000), orderedInterval (23705548947 / 1000000000000) (23705554871 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 1) <| besselDerivativeNearFromState (187109991118611 / 800000000000) 1 (IntervalRat.scale (253 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (42349038594 / 1000000000000) (42349117747 / 1000000000000), orderedInterval (-30561204692 / 1000000000000) (-30561125538 / 1000000000000)))) (orderedInterval (-2859187048 / 1000000000000) (-2859182850 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate251_chunkChecks1_2 :
    compactCertificate251.chunkChecks (1 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 1) <| besselDerivativeNearFromState (517556082493417 / 4000000000000) 1 (IntervalRat.scale (253 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-68708600549 / 1000000000000) (-68708600547 / 1000000000000), orderedInterval (-13851637219 / 1000000000000) (-13851637217 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 1) <| besselDerivativeNearFromState (438738022906337 / 4000000000000) 1 (IntervalRat.scale (253 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-37392137708 / 1000000000000) (-37392137707 / 1000000000000), orderedInterval (-66206946178 / 1000000000000) (-66206946177 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 1) <| besselDerivativeNearFromState (274541883475211 / 4000000000000) 1 (IntervalRat.scale (253 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (28829485887 / 1000000000000) (28829485888 / 1000000000000), orderedInterval (91683617171 / 1000000000000) (91683617172 / 1000000000000)))) (orderedInterval (7134001476 / 1000000000000) (7134001507 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 1) <| besselDerivativeNearFromState (147649538018037 / 4000000000000) 1 (IntervalRat.scale (253 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-619081718 / 1000000000000) (-619081707 / 1000000000000), orderedInterval (131339938144 / 1000000000000) (131339938156 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 1) <| besselDerivativeNearFromState (400897217645111 / 4000000000000) 1 (IntervalRat.scale (253 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (36625649400 / 1000000000000) (36625649401 / 1000000000000), orderedInterval (70602577530 / 1000000000000) (70602577531 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 1) <| besselDerivativeNearFromState (547390876937047 / 4000000000000) 1 (IntervalRat.scale (253 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-38391931127 / 1000000000000) (-38391920133 / 1000000000000), orderedInterval (56514921916 / 1000000000000) (56514932910 / 1000000000000)))) (orderedInterval (-6662252620 / 1000000000000) (-6662251694 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 1) <| besselDerivativeNearFromState (231458116524789 / 4000000000000) 1 (IntervalRat.scale (253 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (90587923135 / 1000000000000) (90587938208 / 1000000000000), orderedInterval (-53655431718 / 1000000000000) (-53655416645 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 1) <| besselDerivativeNearFromState (940864393502869 / 4000000000000) 1 (IntervalRat.scale (253 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-19370094324 / 1000000000000) (-19370094323 / 1000000000000), orderedInterval (-48242728557 / 1000000000000) (-48242728556 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 1) <| besselDerivativeNearFromState (628453811380571 / 4000000000000) 1 (IntervalRat.scale (253 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (46472508253 / 1000000000000) (46472508254 / 1000000000000), orderedInterval (43352446454 / 1000000000000) (43352446455 / 1000000000000)))) (orderedInterval (-2948491421 / 1000000000000) (-2948491329 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate251_chunkChecks1 :
    compactCertificate251.chunkChecks (1 : Fin 5) 0 9 = true :=
  compactCertificate251.chunkChecks_nine_of_three (1 : Fin 5) compactCertificate251_chunkChecks1_0
    compactCertificate251_chunkChecks1_1 compactCertificate251_chunkChecks1_2

theorem compactCertificate251_chunkChecks2_0 :
    compactCertificate251.chunkChecks (2 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 2) <| besselDerivativeNearFromState (253 / 2) 2 (IntervalRat.scale (253 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (70851983789 / 1000000000000) (70851983872 / 1000000000000), orderedInterval (-3819060683 / 1000000000000) (-3819060600 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 2) <| besselDerivativeNearFromState (372717309818953 / 4000000000000) 2 (IntervalRat.scale (253 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-23191536638 / 1000000000000) (-23191536218 / 1000000000000), orderedInterval (79461918499 / 1000000000000) (79461918919 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 2) <| besselDerivativeNearFromState (120529120035049 / 800000000000) 2 (IntervalRat.scale (253 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (39314553733 / 1000000000000) (39314553734 / 1000000000000), orderedInterval (51637011127 / 1000000000000) (51637011128 / 1000000000000)))) (orderedInterval (-31259333454 / 1000000000000) (-31259333407 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 2) <| besselDerivativeNearFromState (108757981434971 / 4000000000000) 2 (IntervalRat.scale (253 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (45805134655 / 1000000000000) (45805135435 / 1000000000000), orderedInterval (-146853395218 / 1000000000000) (-146853394438 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 2) <| besselDerivativeNearFromState (292139236209887 / 4000000000000) 2 (IntervalRat.scale (253 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-93358250146 / 1000000000000) (-93358250123 / 1000000000000), orderedInterval (-194764547 / 1000000000000) (-194764524 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 2) <| besselDerivativeNearFromState (793214855484579 / 4000000000000) 2 (IntervalRat.scale (253 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-52128307048 / 1000000000000) (-52128307047 / 1000000000000), orderedInterval (-22071257978 / 1000000000000) (-22071257977 / 1000000000000)))) (orderedInterval (-7969626874 / 1000000000000) (-7969626849 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 2) <| besselDerivativeNearFromState (584278472420027 / 4000000000000) 2 (IntervalRat.scale (253 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (47389912036 / 1000000000000) (47389980409 / 1000000000000), orderedInterval (-46124441484 / 1000000000000) (-46124373111 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 2) <| besselDerivativeNearFromState (1001171121199271 / 4000000000000) 2 (IntervalRat.scale (253 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-12464307019 / 1000000000000) (-12464306927 / 1000000000000), orderedInterval (48893558476 / 1000000000000) (48893558568 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 2) <| besselDerivativeNearFromState (737458116524789 / 4000000000000) 2 (IntervalRat.scale (253 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (11945856830 / 1000000000000) (11945856908 / 1000000000000), orderedInterval (-57568101380 / 1000000000000) (-57568101303 / 1000000000000)))) (orderedInterval (-2078687210 / 1000000000000) (-2078687172 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate251_chunkChecks2_1 :
    compactCertificate251.chunkChecks (2 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 2) <| besselDerivativeNearFromState (1131450396614747 / 4000000000000) 2 (IntervalRat.scale (253 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (37285666367 / 1000000000000) (37285666368 / 1000000000000), orderedInterval (29266852385 / 1000000000000) (29266852386 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 2) <| besselDerivativeNearFromState (653243191060163 / 4000000000000) 2 (IntervalRat.scale (253 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (41757746365 / 1000000000000) (41757746366 / 1000000000000), orderedInterval (46288772153 / 1000000000000) (46288772154 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 2) <| besselDerivativeNearFromState (1159191505859167 / 4000000000000) 2 (IntervalRat.scale (253 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (46864784603 / 1000000000000) (46864784710 / 1000000000000), orderedInterval (597659941 / 1000000000000) (597660047 / 1000000000000)))) (orderedInterval (-6939039051 / 1000000000000) (-6939038747 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 2) <| besselDerivativeNearFromState (1083067071140923 / 4000000000000) 2 (IntervalRat.scale (253 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (47559898973 / 1000000000000) (47559898979 / 1000000000000), orderedInterval (9358141111 / 1000000000000) (9358141117 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 2) <| besselDerivativeNearFromState (772927767215659 / 4000000000000) 2 (IntervalRat.scale (253 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-39628281252 / 1000000000000) (-39628241717 / 1000000000000), orderedInterval (41625886904 / 1000000000000) (41625926439 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 2) <| besselDerivativeNearFromState (876417708629661 / 4000000000000) 2 (IntervalRat.scale (253 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-1198217751 / 1000000000000) (-1198217747 / 1000000000000), orderedInterval (53892677351 / 1000000000000) (53892677355 / 1000000000000)))) (orderedInterval (12618417786 / 1000000000000) (12618426597 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 2) <| besselDerivativeNearFromState (730665714316109 / 4000000000000) 2 (IntervalRat.scale (253 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (55810743629 / 1000000000000) (55810743631 / 1000000000000), orderedInterval (19090412221 / 1000000000000) (19090412222 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 2) <| besselDerivativeNearFromState (645565317466289 / 4000000000000) 2 (IntervalRat.scale (253 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-58233381132 / 1000000000000) (-58233375208 / 1000000000000), orderedInterval (23705548947 / 1000000000000) (23705554871 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 2) <| besselDerivativeNearFromState (187109991118611 / 800000000000) 2 (IntervalRat.scale (253 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (42349038594 / 1000000000000) (42349117747 / 1000000000000), orderedInterval (-30561204692 / 1000000000000) (-30561125538 / 1000000000000)))) (orderedInterval (-10452291127 / 1000000000000) (-10452283588 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate251_chunkChecks2_2 :
    compactCertificate251.chunkChecks (2 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 2) <| besselDerivativeNearFromState (517556082493417 / 4000000000000) 2 (IntervalRat.scale (253 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-68708600549 / 1000000000000) (-68708600547 / 1000000000000), orderedInterval (-13851637219 / 1000000000000) (-13851637217 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 2) <| besselDerivativeNearFromState (438738022906337 / 4000000000000) 2 (IntervalRat.scale (253 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-37392137708 / 1000000000000) (-37392137707 / 1000000000000), orderedInterval (-66206946178 / 1000000000000) (-66206946177 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 2) <| besselDerivativeNearFromState (274541883475211 / 4000000000000) 2 (IntervalRat.scale (253 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (28829485887 / 1000000000000) (28829485888 / 1000000000000), orderedInterval (91683617171 / 1000000000000) (91683617172 / 1000000000000)))) (orderedInterval (-13417336276 / 1000000000000) (-13417336246 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 2) <| besselDerivativeNearFromState (147649538018037 / 4000000000000) 2 (IntervalRat.scale (253 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-619081718 / 1000000000000) (-619081707 / 1000000000000), orderedInterval (131339938144 / 1000000000000) (131339938156 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 2) <| besselDerivativeNearFromState (400897217645111 / 4000000000000) 2 (IntervalRat.scale (253 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (36625649400 / 1000000000000) (36625649401 / 1000000000000), orderedInterval (70602577530 / 1000000000000) (70602577531 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 2) <| besselDerivativeNearFromState (547390876937047 / 4000000000000) 2 (IntervalRat.scale (253 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-38391931127 / 1000000000000) (-38391920133 / 1000000000000), orderedInterval (56514921916 / 1000000000000) (56514932910 / 1000000000000)))) (orderedInterval (-2870088182 / 1000000000000) (-2870087174 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 2) <| besselDerivativeNearFromState (231458116524789 / 4000000000000) 2 (IntervalRat.scale (253 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (90587923135 / 1000000000000) (90587938208 / 1000000000000), orderedInterval (-53655431718 / 1000000000000) (-53655416645 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 2) <| besselDerivativeNearFromState (940864393502869 / 4000000000000) 2 (IntervalRat.scale (253 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-19370094324 / 1000000000000) (-19370094323 / 1000000000000), orderedInterval (-48242728557 / 1000000000000) (-48242728556 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 2) <| besselDerivativeNearFromState (628453811380571 / 4000000000000) 2 (IntervalRat.scale (253 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (46472508253 / 1000000000000) (46472508254 / 1000000000000), orderedInterval (43352446454 / 1000000000000) (43352446455 / 1000000000000)))) (orderedInterval (7907936931 / 1000000000000) (7907937025 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate251_chunkChecks2 :
    compactCertificate251.chunkChecks (2 : Fin 5) 0 9 = true :=
  compactCertificate251.chunkChecks_nine_of_three (2 : Fin 5) compactCertificate251_chunkChecks2_0
    compactCertificate251_chunkChecks2_1 compactCertificate251_chunkChecks2_2

theorem compactCertificate251_chunkChecks3_0 :
    compactCertificate251.chunkChecks (3 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 3) <| besselDerivativeNearFromState (253 / 2) 3 (IntervalRat.scale (253 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (70851983789 / 1000000000000) (70851983872 / 1000000000000), orderedInterval (-3819060683 / 1000000000000) (-3819060600 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 3) <| besselDerivativeNearFromState (372717309818953 / 4000000000000) 3 (IntervalRat.scale (253 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-23191536638 / 1000000000000) (-23191536218 / 1000000000000), orderedInterval (79461918499 / 1000000000000) (79461918919 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 3) <| besselDerivativeNearFromState (120529120035049 / 800000000000) 3 (IntervalRat.scale (253 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (39314553733 / 1000000000000) (39314553734 / 1000000000000), orderedInterval (51637011127 / 1000000000000) (51637011128 / 1000000000000)))) (orderedInterval (-3654007171 / 1000000000000) (-3654007122 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 3) <| besselDerivativeNearFromState (108757981434971 / 4000000000000) 3 (IntervalRat.scale (253 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (45805134655 / 1000000000000) (45805135435 / 1000000000000), orderedInterval (-146853395218 / 1000000000000) (-146853394438 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 3) <| besselDerivativeNearFromState (292139236209887 / 4000000000000) 3 (IntervalRat.scale (253 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-93358250146 / 1000000000000) (-93358250123 / 1000000000000), orderedInterval (-194764547 / 1000000000000) (-194764524 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 3) <| besselDerivativeNearFromState (793214855484579 / 4000000000000) 3 (IntervalRat.scale (253 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-52128307048 / 1000000000000) (-52128307047 / 1000000000000), orderedInterval (-22071257978 / 1000000000000) (-22071257977 / 1000000000000)))) (orderedInterval (-5995692404 / 1000000000000) (-5995692367 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 3) <| besselDerivativeNearFromState (584278472420027 / 4000000000000) 3 (IntervalRat.scale (253 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (47389912036 / 1000000000000) (47389980409 / 1000000000000), orderedInterval (-46124441484 / 1000000000000) (-46124373111 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 3) <| besselDerivativeNearFromState (1001171121199271 / 4000000000000) 3 (IntervalRat.scale (253 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-12464307019 / 1000000000000) (-12464306927 / 1000000000000), orderedInterval (48893558476 / 1000000000000) (48893558568 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 3) <| besselDerivativeNearFromState (737458116524789 / 4000000000000) 3 (IntervalRat.scale (253 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (11945856830 / 1000000000000) (11945856908 / 1000000000000), orderedInterval (-57568101380 / 1000000000000) (-57568101303 / 1000000000000)))) (orderedInterval (16004628869 / 1000000000000) (16004628937 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate251_chunkChecks3_1 :
    compactCertificate251.chunkChecks (3 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 3) <| besselDerivativeNearFromState (1131450396614747 / 4000000000000) 3 (IntervalRat.scale (253 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (37285666367 / 1000000000000) (37285666368 / 1000000000000), orderedInterval (29266852385 / 1000000000000) (29266852386 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 3) <| besselDerivativeNearFromState (653243191060163 / 4000000000000) 3 (IntervalRat.scale (253 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (41757746365 / 1000000000000) (41757746366 / 1000000000000), orderedInterval (46288772153 / 1000000000000) (46288772154 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 3) <| besselDerivativeNearFromState (1159191505859167 / 4000000000000) 3 (IntervalRat.scale (253 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (46864784603 / 1000000000000) (46864784710 / 1000000000000), orderedInterval (597659941 / 1000000000000) (597660047 / 1000000000000)))) (orderedInterval (49795430080 / 1000000000000) (49795430752 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 3) <| besselDerivativeNearFromState (1083067071140923 / 4000000000000) 3 (IntervalRat.scale (253 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (47559898973 / 1000000000000) (47559898979 / 1000000000000), orderedInterval (9358141111 / 1000000000000) (9358141117 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 3) <| besselDerivativeNearFromState (772927767215659 / 4000000000000) 3 (IntervalRat.scale (253 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-39628281252 / 1000000000000) (-39628241717 / 1000000000000), orderedInterval (41625886904 / 1000000000000) (41625926439 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 3) <| besselDerivativeNearFromState (876417708629661 / 4000000000000) 3 (IntervalRat.scale (253 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-1198217751 / 1000000000000) (-1198217747 / 1000000000000), orderedInterval (53892677351 / 1000000000000) (53892677355 / 1000000000000)))) (orderedInterval (-11055289112 / 1000000000000) (-11055275648 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 3) <| besselDerivativeNearFromState (730665714316109 / 4000000000000) 3 (IntervalRat.scale (253 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (55810743629 / 1000000000000) (55810743631 / 1000000000000), orderedInterval (19090412221 / 1000000000000) (19090412222 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 3) <| besselDerivativeNearFromState (645565317466289 / 4000000000000) 3 (IntervalRat.scale (253 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-58233381132 / 1000000000000) (-58233375208 / 1000000000000), orderedInterval (23705548947 / 1000000000000) (23705554871 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 3) <| besselDerivativeNearFromState (187109991118611 / 800000000000) 3 (IntervalRat.scale (253 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (42349038594 / 1000000000000) (42349117747 / 1000000000000), orderedInterval (-30561204692 / 1000000000000) (-30561125538 / 1000000000000)))) (orderedInterval (7181558950 / 1000000000000) (7181572563 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate251_chunkChecks3_2 :
    compactCertificate251.chunkChecks (3 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 3) <| besselDerivativeNearFromState (517556082493417 / 4000000000000) 3 (IntervalRat.scale (253 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-68708600549 / 1000000000000) (-68708600547 / 1000000000000), orderedInterval (-13851637219 / 1000000000000) (-13851637217 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 3) <| besselDerivativeNearFromState (438738022906337 / 4000000000000) 3 (IntervalRat.scale (253 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-37392137708 / 1000000000000) (-37392137707 / 1000000000000), orderedInterval (-66206946178 / 1000000000000) (-66206946177 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 3) <| besselDerivativeNearFromState (274541883475211 / 4000000000000) 3 (IntervalRat.scale (253 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (28829485887 / 1000000000000) (28829485888 / 1000000000000), orderedInterval (91683617171 / 1000000000000) (91683617172 / 1000000000000)))) (orderedInterval (-5183019787 / 1000000000000) (-5183019759 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 3) <| besselDerivativeNearFromState (147649538018037 / 4000000000000) 3 (IntervalRat.scale (253 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-619081718 / 1000000000000) (-619081707 / 1000000000000), orderedInterval (131339938144 / 1000000000000) (131339938156 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 3) <| besselDerivativeNearFromState (400897217645111 / 4000000000000) 3 (IntervalRat.scale (253 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (36625649400 / 1000000000000) (36625649401 / 1000000000000), orderedInterval (70602577530 / 1000000000000) (70602577531 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 3) <| besselDerivativeNearFromState (547390876937047 / 4000000000000) 3 (IntervalRat.scale (253 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-38391931127 / 1000000000000) (-38391920133 / 1000000000000), orderedInterval (56514921916 / 1000000000000) (56514932910 / 1000000000000)))) (orderedInterval (6362574383 / 1000000000000) (6362575472 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 3) <| besselDerivativeNearFromState (231458116524789 / 4000000000000) 3 (IntervalRat.scale (253 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (90587923135 / 1000000000000) (90587938208 / 1000000000000), orderedInterval (-53655431718 / 1000000000000) (-53655416645 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 3) <| besselDerivativeNearFromState (940864393502869 / 4000000000000) 3 (IntervalRat.scale (253 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-19370094324 / 1000000000000) (-19370094323 / 1000000000000), orderedInterval (-48242728557 / 1000000000000) (-48242728556 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 3) <| besselDerivativeNearFromState (628453811380571 / 4000000000000) 3 (IntervalRat.scale (253 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (46472508253 / 1000000000000) (46472508254 / 1000000000000), orderedInterval (43352446454 / 1000000000000) (43352446455 / 1000000000000)))) (orderedInterval (-9693988904 / 1000000000000) (-9693988781 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate251_chunkChecks3 :
    compactCertificate251.chunkChecks (3 : Fin 5) 0 9 = true :=
  compactCertificate251.chunkChecks_nine_of_three (3 : Fin 5) compactCertificate251_chunkChecks3_0
    compactCertificate251_chunkChecks3_1 compactCertificate251_chunkChecks3_2

theorem compactCertificate251_chunkChecks4_0 :
    compactCertificate251.chunkChecks (4 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 4) <| besselDerivativeNearFromState (253 / 2) 4 (IntervalRat.scale (253 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (70851983789 / 1000000000000) (70851983872 / 1000000000000), orderedInterval (-3819060683 / 1000000000000) (-3819060600 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 4) <| besselDerivativeNearFromState (372717309818953 / 4000000000000) 4 (IntervalRat.scale (253 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-23191536638 / 1000000000000) (-23191536218 / 1000000000000), orderedInterval (79461918499 / 1000000000000) (79461918919 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 4) <| besselDerivativeNearFromState (120529120035049 / 800000000000) 4 (IntervalRat.scale (253 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (39314553733 / 1000000000000) (39314553734 / 1000000000000), orderedInterval (51637011127 / 1000000000000) (51637011128 / 1000000000000)))) (orderedInterval (32717366903 / 1000000000000) (32717366954 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 4) <| besselDerivativeNearFromState (108757981434971 / 4000000000000) 4 (IntervalRat.scale (253 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (45805134655 / 1000000000000) (45805135435 / 1000000000000), orderedInterval (-146853395218 / 1000000000000) (-146853394438 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 4) <| besselDerivativeNearFromState (292139236209887 / 4000000000000) 4 (IntervalRat.scale (253 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-93358250146 / 1000000000000) (-93358250123 / 1000000000000), orderedInterval (-194764547 / 1000000000000) (-194764524 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 4) <| besselDerivativeNearFromState (793214855484579 / 4000000000000) 4 (IntervalRat.scale (253 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-52128307048 / 1000000000000) (-52128307047 / 1000000000000), orderedInterval (-22071257978 / 1000000000000) (-22071257977 / 1000000000000)))) (orderedInterval (22093520673 / 1000000000000) (22093520730 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 4) <| besselDerivativeNearFromState (584278472420027 / 4000000000000) 4 (IntervalRat.scale (253 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (47389912036 / 1000000000000) (47389980409 / 1000000000000), orderedInterval (-46124441484 / 1000000000000) (-46124373111 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 4) <| besselDerivativeNearFromState (1001171121199271 / 4000000000000) 4 (IntervalRat.scale (253 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-12464307019 / 1000000000000) (-12464306927 / 1000000000000), orderedInterval (48893558476 / 1000000000000) (48893558568 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 4) <| besselDerivativeNearFromState (737458116524789 / 4000000000000) 4 (IntervalRat.scale (253 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (11945856830 / 1000000000000) (11945856908 / 1000000000000), orderedInterval (-57568101380 / 1000000000000) (-57568101303 / 1000000000000)))) (orderedInterval (6941518282 / 1000000000000) (6941518409 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate251_chunkChecks4_1 :
    compactCertificate251.chunkChecks (4 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 4) <| besselDerivativeNearFromState (1131450396614747 / 4000000000000) 4 (IntervalRat.scale (253 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (37285666367 / 1000000000000) (37285666368 / 1000000000000), orderedInterval (29266852385 / 1000000000000) (29266852386 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 4) <| besselDerivativeNearFromState (653243191060163 / 4000000000000) 4 (IntervalRat.scale (253 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (41757746365 / 1000000000000) (41757746366 / 1000000000000), orderedInterval (46288772153 / 1000000000000) (46288772154 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 4) <| besselDerivativeNearFromState (1159191505859167 / 4000000000000) 4 (IntervalRat.scale (253 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (46864784603 / 1000000000000) (46864784710 / 1000000000000), orderedInterval (597659941 / 1000000000000) (597660047 / 1000000000000)))) (orderedInterval (25673666511 / 1000000000000) (25673668022 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 4) <| besselDerivativeNearFromState (1083067071140923 / 4000000000000) 4 (IntervalRat.scale (253 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (47559898973 / 1000000000000) (47559898979 / 1000000000000), orderedInterval (9358141111 / 1000000000000) (9358141117 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 4) <| besselDerivativeNearFromState (772927767215659 / 4000000000000) 4 (IntervalRat.scale (253 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-39628281252 / 1000000000000) (-39628241717 / 1000000000000), orderedInterval (41625886904 / 1000000000000) (41625926439 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 4) <| besselDerivativeNearFromState (876417708629661 / 4000000000000) 4 (IntervalRat.scale (253 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-1198217751 / 1000000000000) (-1198217747 / 1000000000000), orderedInterval (53892677351 / 1000000000000) (53892677355 / 1000000000000)))) (orderedInterval (-38194530625 / 1000000000000) (-38194509939 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 4) <| besselDerivativeNearFromState (730665714316109 / 4000000000000) 4 (IntervalRat.scale (253 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (55810743629 / 1000000000000) (55810743631 / 1000000000000), orderedInterval (19090412221 / 1000000000000) (19090412222 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 4) <| besselDerivativeNearFromState (645565317466289 / 4000000000000) 4 (IntervalRat.scale (253 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-58233381132 / 1000000000000) (-58233375208 / 1000000000000), orderedInterval (23705548947 / 1000000000000) (23705554871 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 4) <| besselDerivativeNearFromState (187109991118611 / 800000000000) 4 (IntervalRat.scale (253 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (42349038594 / 1000000000000) (42349117747 / 1000000000000), orderedInterval (-30561204692 / 1000000000000) (-30561125538 / 1000000000000)))) (orderedInterval (24188434115 / 1000000000000) (24188458973 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate251_chunkChecks4_2 :
    compactCertificate251.chunkChecks (4 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 4) <| besselDerivativeNearFromState (517556082493417 / 4000000000000) 4 (IntervalRat.scale (253 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-68708600549 / 1000000000000) (-68708600547 / 1000000000000), orderedInterval (-13851637219 / 1000000000000) (-13851637217 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 4) <| besselDerivativeNearFromState (438738022906337 / 4000000000000) 4 (IntervalRat.scale (253 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-37392137708 / 1000000000000) (-37392137707 / 1000000000000), orderedInterval (-66206946178 / 1000000000000) (-66206946177 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 4) <| besselDerivativeNearFromState (274541883475211 / 4000000000000) 4 (IntervalRat.scale (253 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (28829485887 / 1000000000000) (28829485888 / 1000000000000), orderedInterval (91683617171 / 1000000000000) (91683617172 / 1000000000000)))) (orderedInterval (13383161687 / 1000000000000) (13383161715 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 4) <| besselDerivativeNearFromState (147649538018037 / 4000000000000) 4 (IntervalRat.scale (253 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-619081718 / 1000000000000) (-619081707 / 1000000000000), orderedInterval (131339938144 / 1000000000000) (131339938156 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 4) <| besselDerivativeNearFromState (400897217645111 / 4000000000000) 4 (IntervalRat.scale (253 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (36625649400 / 1000000000000) (36625649401 / 1000000000000), orderedInterval (70602577530 / 1000000000000) (70602577531 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 4) <| besselDerivativeNearFromState (547390876937047 / 4000000000000) 4 (IntervalRat.scale (253 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-38391931127 / 1000000000000) (-38391920133 / 1000000000000), orderedInterval (56514921916 / 1000000000000) (56514932910 / 1000000000000)))) (orderedInterval (3601644777 / 1000000000000) (3601645963 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 4) <| besselDerivativeNearFromState (231458116524789 / 4000000000000) 4 (IntervalRat.scale (253 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (90587923135 / 1000000000000) (90587938208 / 1000000000000), orderedInterval (-53655431718 / 1000000000000) (-53655416645 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 4) <| besselDerivativeNearFromState (940864393502869 / 4000000000000) 4 (IntervalRat.scale (253 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-19370094324 / 1000000000000) (-19370094323 / 1000000000000), orderedInterval (-48242728557 / 1000000000000) (-48242728556 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 4) <| besselDerivativeNearFromState (628453811380571 / 4000000000000) 4 (IntervalRat.scale (253 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (46472508253 / 1000000000000) (46472508254 / 1000000000000), orderedInterval (43352446454 / 1000000000000) (43352446455 / 1000000000000)))) (orderedInterval (-1722315788 / 1000000000000) (-1722315601 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate251_chunkChecks4 :
    compactCertificate251.chunkChecks (4 : Fin 5) 0 9 = true :=
  compactCertificate251.chunkChecks_nine_of_three (4 : Fin 5) compactCertificate251_chunkChecks4_0
    compactCertificate251_chunkChecks4_1 compactCertificate251_chunkChecks4_2

theorem compactCertificate251_chunks :
    ∀ r : Fin 5, ∀ b, compactCertificate251.chunkCheck r b = true :=
  compactCertificate251.chunkChecks_all (by
    intro r
    fin_cases r
    · exact compactCertificate251_chunkChecks0
    · exact compactCertificate251_chunkChecks1
    · exact compactCertificate251_chunkChecks2
    · exact compactCertificate251_chunkChecks3
    · exact compactCertificate251_chunkChecks4)

theorem compactCertificate251_coefficient0 :
    compactCertificate251.coefficientCheck (0 : Fin 5) = true := by
  norm_num [CompactCertificate.coefficientCheck, intervalFinSumHull,
    compactCertificate251, rationalIntervalSubset, orderedInterval, Fin.sum_univ_succ]

theorem compactCertificate251_coefficient1 :
    compactCertificate251.coefficientCheck (1 : Fin 5) = true := by
  norm_num [CompactCertificate.coefficientCheck, intervalFinSumHull,
    compactCertificate251, rationalIntervalSubset, orderedInterval, Fin.sum_univ_succ]

theorem compactCertificate251_coefficient2 :
    compactCertificate251.coefficientCheck (2 : Fin 5) = true := by
  norm_num [CompactCertificate.coefficientCheck, intervalFinSumHull,
    compactCertificate251, rationalIntervalSubset, orderedInterval, Fin.sum_univ_succ]

theorem compactCertificate251_coefficient3 :
    compactCertificate251.coefficientCheck (3 : Fin 5) = true := by
  norm_num [CompactCertificate.coefficientCheck, intervalFinSumHull,
    compactCertificate251, rationalIntervalSubset, orderedInterval, Fin.sum_univ_succ]

theorem compactCertificate251_coefficient4 :
    compactCertificate251.coefficientCheck (4 : Fin 5) = true := by
  norm_num [CompactCertificate.coefficientCheck, intervalFinSumHull,
    compactCertificate251, rationalIntervalSubset, orderedInterval, Fin.sum_univ_succ]

theorem compactCertificate251_coefficients : ∀ r : Fin 5,
    compactCertificate251.coefficientCheck r = true := by
  intro r
  fin_cases r
  · exact compactCertificate251_coefficient0
  · exact compactCertificate251_coefficient1
  · exact compactCertificate251_coefficient2
  · exact compactCertificate251_coefficient3
  · exact compactCertificate251_coefficient4

theorem compactCertificate251_lower : (1 : ℚ) ≤ compactCertificate251.output.lo := by
  norm_num [CompactCertificate.output, CompactCertificate.interval,
    CompactCertificate.coefficientTargetNat, compactCertificate251, dualConstant,
    intervalTaylorSum, intervalPow, intervalSub, intervalMaxAbs, widenInterval,
    rationalErrorInterval, orderedInterval, IntervalRat.add, IntervalRat.mul, IntervalRat.scale,
    IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4]

theorem compactCertificate251_proves {t : ℝ} (ht : t ∈ compactCertificate251.interval) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t :=
  compactCertificate251.proves compactCertificate251_states compactCertificate251_chunks
    compactCertificate251_coefficients compactCertificate251_lower ht

end Erdos232
