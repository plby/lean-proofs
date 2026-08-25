/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, OpenAI Codex
-/
import ErdosProblems.Erdos232.CompactBase

open LeanCert.Core
namespace Erdos232

def compactCertificate204 : CompactCertificate where
  left := 2957 / 32
  right := 1479 / 16
  center := 5915 / 64
  grid := fun i =>
    match i.val with
    | 0 => 29
    | 1 => 22
    | 2 => 35
    | 3 => 6
    | 4 => 17
    | 5 => 46
    | 6 => 34
    | 7 => 58
    | 8 => 43
    | 9 => 66
    | 10 => 38
    | 11 => 67
    | 12 => 63
    | 13 => 45
    | 14 => 51
    | 15 => 43
    | 16 => 38
    | 17 => 54
    | 18 => 30
    | 19 => 26
    | 20 => 16
    | 21 => 9
    | 22 => 23
    | 23 => 32
    | 24 => 13
    | 25 => 55
    | _ => 37
  point := fun i =>
    match i.val with
    | 0 => 5915 / 64
    | 1 => 1742784891366883 / 25600000000000
    | 2 => 563580826092739 / 5120000000000
    | 3 => 508540284733481 / 25600000000000
    | 4 => 1366010736902357 / 25600000000000
    | 5 => 3708984877621569 / 25600000000000
    | 6 => 2732021473805897 / 25600000000000
    | 7 => 4681365361180781 / 25600000000000
    | 8 => 3448272536951879 / 25600000000000
    | 9 => 5290536834763817 / 25600000000000
    | 10 => 3054492865708193 / 25600000000000
    | 11 => 5420251191428437 / 25600000000000
    | 12 => 5064301759524553 / 25600000000000
    | 13 => 3614124698087449 / 25600000000000
    | 14 => 4098032210707071 / 25600000000000
    | 15 => 3416512015952399 / 25600000000000
    | 16 => 3018591978508379 / 25600000000000
    | 17 => 874905610645521 / 5120000000000
    | 18 => 2420034962805187 / 25600000000000
    | 19 => 2051490439123307 / 25600000000000
    | 20 => 1283727463048121 / 25600000000000
    | 21 => 690392899112007 / 25600000000000
    | 22 => 1874551021637021 / 25600000000000
    | 23 => 2559539159749117 / 25600000000000
    | 24 => 1082272536951879 / 25600000000000
    | 25 => 4399377776734759 / 25600000000000
    | _ => 2938580469815081 / 25600000000000
  state := fun i =>
    match i.val with
    | 0 => (orderedInterval (-71652819764 / 1000000000000) (-71652801958 / 1000000000000), orderedInterval (42268626976 / 1000000000000) (42268644782 / 1000000000000))
    | 1 => (orderedInterval (-24293380419 / 1000000000000) (-24293380086 / 1000000000000), orderedInterval (93781004454 / 1000000000000) (93781004787 / 1000000000000))
    | 2 => (orderedInterval (-59708224515 / 1000000000000) (-59708224514 / 1000000000000), orderedInterval (-46829273947 / 1000000000000) (-46829273946 / 1000000000000))
    | 3 => (orderedInterval (174533514242 / 1000000000000) (174533514685 / 1000000000000), orderedInterval (-44095174296 / 1000000000000) (-44095173853 / 1000000000000))
    | 4 => (orderedInterval (-73307917537 / 1000000000000) (-73307917536 / 1000000000000), orderedInterval (-80286607071 / 1000000000000) (-80286607070 / 1000000000000))
    | 5 => (orderedInterval (60599051115 / 1000000000000) (60599051116 / 1000000000000), orderedInterval (26656978226 / 1000000000000) (26656978227 / 1000000000000))
    | 6 => (orderedInterval (49143187337 / 1000000000000) (49143187338 / 1000000000000), orderedInterval (59354240807 / 1000000000000) (59354240808 / 1000000000000))
    | 7 => (orderedInterval (58484724218 / 1000000000000) (58484724226 / 1000000000000), orderedInterval (7642229053 / 1000000000000) (7642229061 / 1000000000000))
    | 8 => (orderedInterval (-26399568439 / 1000000000000) (-26399568438 / 1000000000000), orderedInterval (-63379210551 / 1000000000000) (-63379210550 / 1000000000000))
    | 9 => (orderedInterval (5611278452 / 1000000000000) (5611278454 / 1000000000000), orderedInterval (55204321836 / 1000000000000) (55204321838 / 1000000000000))
    | 10 => (orderedInterval (48162195970 / 1000000000000) (48162195971 / 1000000000000), orderedInterval (54716124054 / 1000000000000) (54716124055 / 1000000000000))
    | 11 => (orderedInterval (-49234347549 / 1000000000000) (-49234331878 / 1000000000000), orderedInterval (24256429840 / 1000000000000) (24256445512 / 1000000000000))
    | 12 => (orderedInterval (-36053474887 / 1000000000000) (-36053474886 / 1000000000000), orderedInterval (-43706776982 / 1000000000000) (-43706776981 / 1000000000000))
    | 13 => (orderedInterval (-37337682047 / 1000000000000) (-37337682046 / 1000000000000), orderedInterval (-55682543248 / 1000000000000) (-55682543247 / 1000000000000))
    | 14 => (orderedInterval (-37800878893 / 1000000000000) (-37800878892 / 1000000000000), orderedInterval (-50359644599 / 1000000000000) (-50359644598 / 1000000000000))
    | 15 => (orderedInterval (51729349956 / 1000000000000) (51729456226 / 1000000000000), orderedInterval (-45957053192 / 1000000000000) (-45956946922 / 1000000000000))
    | 16 => (orderedInterval (-46341216568 / 1000000000000) (-46341189555 / 1000000000000), orderedInterval (57218692611 / 1000000000000) (57218719625 / 1000000000000))
    | 17 => (orderedInterval (55017073360 / 1000000000000) (55017085225 / 1000000000000), orderedInterval (-26592936368 / 1000000000000) (-26592924503 / 1000000000000))
    | 18 => (orderedInterval (71942598380 / 1000000000000) (71942598381 / 1000000000000), orderedInterval (39098662629 / 1000000000000) (39098662630 / 1000000000000))
    | 19 => (orderedInterval (-61482308742 / 1000000000000) (-61482244224 / 1000000000000), orderedInterval (64913745064 / 1000000000000) (64913809583 / 1000000000000))
    | 20 => (orderedInterval (69349758212 / 1000000000000) (69349758213 / 1000000000000), orderedInterval (88112803192 / 1000000000000) (88112803193 / 1000000000000))
    | 21 => (orderedInterval (77013710819 / 1000000000000) (77013719755 / 1000000000000), orderedInterval (-134382151693 / 1000000000000) (-134382142757 / 1000000000000))
    | 22 => (orderedInterval (-91719167289 / 1000000000000) (-91719166947 / 1000000000000), orderedInterval (17403285065 / 1000000000000) (17403285407 / 1000000000000))
    | 23 => (orderedInterval (18593824290 / 1000000000000) (18593824291 / 1000000000000), orderedInterval (77506530682 / 1000000000000) (77506530683 / 1000000000000))
    | 24 => (orderedInterval (-97893327141 / 1000000000000) (-97893284591 / 1000000000000), orderedInterval (75152011254 / 1000000000000) (75152053805 / 1000000000000))
    | 25 => (orderedInterval (9229690989 / 1000000000000) (9229691028 / 1000000000000), orderedInterval (-60187648266 / 1000000000000) (-60187648227 / 1000000000000))
    | _ => (orderedInterval (46030487001 / 1000000000000) (46030510598 / 1000000000000), orderedInterval (-58743136188 / 1000000000000) (-58743112591 / 1000000000000))
  chunkTarget := fun r b =>
    match r.val with
    | 0 =>
      match b.val with
      | 0 => orderedInterval (-32130783266 / 1000000000000) (-32130776198 / 1000000000000)
      | 1 => orderedInterval (-8878129750 / 1000000000000) (-8878129733 / 1000000000000)
      | 2 => orderedInterval (-2441928378 / 1000000000000) (-2441928372 / 1000000000000)
      | 3 => orderedInterval (-4427586648 / 1000000000000) (-4427584382 / 1000000000000)
      | 4 => orderedInterval (-2688587527 / 1000000000000) (-2688587515 / 1000000000000)
      | 5 => orderedInterval (4657960140 / 1000000000000) (4657963226 / 1000000000000)
      | 6 => orderedInterval (-5765485261 / 1000000000000) (-5765481585 / 1000000000000)
      | 7 => orderedInterval (-766256951 / 1000000000000) (-766256766 / 1000000000000)
      | _ => orderedInterval (-9977991189 / 1000000000000) (-9977986475 / 1000000000000)
    | 1 =>
      match b.val with
      | 0 => orderedInterval (14124623073 / 1000000000000) (14124630141 / 1000000000000)
      | 1 => orderedInterval (-4560312539 / 1000000000000) (-4560312524 / 1000000000000)
      | 2 => orderedInterval (-2698803941 / 1000000000000) (-2698803931 / 1000000000000)
      | 3 => orderedInterval (-8800754811 / 1000000000000) (-8800749629 / 1000000000000)
      | 4 => orderedInterval (-5912869965 / 1000000000000) (-5912869946 / 1000000000000)
      | 5 => orderedInterval (-6202818772 / 1000000000000) (-6202814452 / 1000000000000)
      | 6 => orderedInterval (-8023687491 / 1000000000000) (-8023684302 / 1000000000000)
      | 7 => orderedInterval (-6014661271 / 1000000000000) (-6014661206 / 1000000000000)
      | _ => orderedInterval (23006293675 / 1000000000000) (23006299334 / 1000000000000)
    | 2 =>
      match b.val with
      | 0 => orderedInterval (33340646754 / 1000000000000) (33340653899 / 1000000000000)
      | 1 => orderedInterval (11615530335 / 1000000000000) (11615530354 / 1000000000000)
      | 2 => orderedInterval (8446443711 / 1000000000000) (8446443729 / 1000000000000)
      | 3 => orderedInterval (35864939238 / 1000000000000) (35864951151 / 1000000000000)
      | 4 => orderedInterval (4746525935 / 1000000000000) (4746525966 / 1000000000000)
      | 5 => orderedInterval (-10310548942 / 1000000000000) (-10310542762 / 1000000000000)
      | 6 => orderedInterval (8840447448 / 1000000000000) (8840450250 / 1000000000000)
      | 7 => orderedInterval (547668533 / 1000000000000) (547668563 / 1000000000000)
      | _ => orderedInterval (15794656025 / 1000000000000) (15794663034 / 1000000000000)
    | 3 =>
      match b.val with
      | 0 => orderedInterval (-12819660850 / 1000000000000) (-12819653706 / 1000000000000)
      | 1 => orderedInterval (7733443261 / 1000000000000) (7733443289 / 1000000000000)
      | 2 => orderedInterval (6475998044 / 1000000000000) (6475998076 / 1000000000000)
      | 3 => orderedInterval (59099817323 / 1000000000000) (59099844596 / 1000000000000)
      | 4 => orderedInterval (9653399230 / 1000000000000) (9653399282 / 1000000000000)
      | 5 => orderedInterval (12812188254 / 1000000000000) (12812197174 / 1000000000000)
      | 6 => orderedInterval (8530052528 / 1000000000000) (8530054959 / 1000000000000)
      | 7 => orderedInterval (7648264106 / 1000000000000) (7648264125 / 1000000000000)
      | _ => orderedInterval (-52825084448 / 1000000000000) (-52825075765 / 1000000000000)
    | _ =>
      match b.val with
      | 0 => orderedInterval (-35235836402 / 1000000000000) (-35235829180 / 1000000000000)
      | 1 => orderedInterval (-26483001951 / 1000000000000) (-26483001909 / 1000000000000)
      | 2 => orderedInterval (-30664541138 / 1000000000000) (-30664541079 / 1000000000000)
      | 3 => orderedInterval (-209064290071 / 1000000000000) (-209064227334 / 1000000000000)
      | 4 => orderedInterval (-4047589966 / 1000000000000) (-4047589877 / 1000000000000)
      | 5 => orderedInterval (25806536674 / 1000000000000) (25806549892 / 1000000000000)
      | 6 => orderedInterval (-10611436051 / 1000000000000) (-10611433916 / 1000000000000)
      | 7 => orderedInterval (-1307506689 / 1000000000000) (-1307506673 / 1000000000000)
      | _ => orderedInterval (-28412864831 / 1000000000000) (-28412853933 / 1000000000000)
  coefficientTarget := fun i =>
    match i.val with
    | 0 => orderedInterval (-62418788830 / 1000000000000) (-62418767800 / 1000000000000)
    | 1 => orderedInterval (-5082992042 / 1000000000000) (-5082966515 / 1000000000000)
    | 2 => orderedInterval (108886309037 / 1000000000000) (108886344184 / 1000000000000)
    | 3 => orderedInterval (46308417448 / 1000000000000) (46308472030 / 1000000000000)
    | _ => orderedInterval (-320020530425 / 1000000000000) (-320020434009 / 1000000000000)

theorem compactCertificate204_stateChecks0 :
    compactCertificate204.stateChecks 0 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 29 12 (5915 / 64)) (orderedInterval (-71652819764 / 1000000000000) (-71652801958 / 1000000000000), orderedInterval (42268626976 / 1000000000000) (42268644782 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 22 12 (1742784891366883 / 25600000000000)) (orderedInterval (-24293380419 / 1000000000000) (-24293380086 / 1000000000000), orderedInterval (93781004454 / 1000000000000) (93781004787 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 35 12 (563580826092739 / 5120000000000)) (orderedInterval (-59708224515 / 1000000000000) (-59708224514 / 1000000000000), orderedInterval (-46829273947 / 1000000000000) (-46829273946 / 1000000000000))) = true
  norm_num [besselStateAtRationalPoint, besselIntervalStepZero,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, besselZeroTransition,
    besselInitial, besselGridStateAt, besselGridStateBlock00, besselGridStateBlock01,
    besselGridStateBlock02, besselGridStateBlock03, besselGridStateBlock04,
    besselGridStateBlock05, besselGridStateBlock06, besselGridStateBlock07,
    besselGridStateBlock08, besselGridStateBlock09, besselGridStateBlock10,
    besselGridStateBlock11, besselGridStateBlock12, besselGridStateBlock13,
    besselGridStateBlock14, besselGridState006, besselGridState009, besselGridState013, besselGridState016, besselGridState017, besselGridState022, besselGridState023, besselGridState026, besselGridState029, besselGridState030, besselGridState032, besselGridState034, besselGridState035, besselGridState037, besselGridState038, besselGridState043, besselGridState045, besselGridState046, besselGridState051, besselGridState054, besselGridState055, besselGridState058, besselGridState063, besselGridState066, besselGridState067, besselStateSubset, linearInterval, widenInterval,
    rationalErrorInterval, rationalIntervalSubset, orderedInterval, Finset.sum_range_succ,
    IntervalRat.add, IntervalRat.mul, IntervalRat.scale, IntervalRat.singleton]

theorem compactCertificate204_stateChecks1 :
    compactCertificate204.stateChecks 3 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 6 12 (508540284733481 / 25600000000000)) (orderedInterval (174533514242 / 1000000000000) (174533514685 / 1000000000000), orderedInterval (-44095174296 / 1000000000000) (-44095173853 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 17 12 (1366010736902357 / 25600000000000)) (orderedInterval (-73307917537 / 1000000000000) (-73307917536 / 1000000000000), orderedInterval (-80286607071 / 1000000000000) (-80286607070 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 46 12 (3708984877621569 / 25600000000000)) (orderedInterval (60599051115 / 1000000000000) (60599051116 / 1000000000000), orderedInterval (26656978226 / 1000000000000) (26656978227 / 1000000000000))) = true
  norm_num [besselStateAtRationalPoint, besselIntervalStepZero,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, besselZeroTransition,
    besselInitial, besselGridStateAt, besselGridStateBlock00, besselGridStateBlock01,
    besselGridStateBlock02, besselGridStateBlock03, besselGridStateBlock04,
    besselGridStateBlock05, besselGridStateBlock06, besselGridStateBlock07,
    besselGridStateBlock08, besselGridStateBlock09, besselGridStateBlock10,
    besselGridStateBlock11, besselGridStateBlock12, besselGridStateBlock13,
    besselGridStateBlock14, besselGridState006, besselGridState009, besselGridState013, besselGridState016, besselGridState017, besselGridState022, besselGridState023, besselGridState026, besselGridState029, besselGridState030, besselGridState032, besselGridState034, besselGridState035, besselGridState037, besselGridState038, besselGridState043, besselGridState045, besselGridState046, besselGridState051, besselGridState054, besselGridState055, besselGridState058, besselGridState063, besselGridState066, besselGridState067, besselStateSubset, linearInterval, widenInterval,
    rationalErrorInterval, rationalIntervalSubset, orderedInterval, Finset.sum_range_succ,
    IntervalRat.add, IntervalRat.mul, IntervalRat.scale, IntervalRat.singleton]

theorem compactCertificate204_stateChecks2 :
    compactCertificate204.stateChecks 6 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 34 12 (2732021473805897 / 25600000000000)) (orderedInterval (49143187337 / 1000000000000) (49143187338 / 1000000000000), orderedInterval (59354240807 / 1000000000000) (59354240808 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 58 12 (4681365361180781 / 25600000000000)) (orderedInterval (58484724218 / 1000000000000) (58484724226 / 1000000000000), orderedInterval (7642229053 / 1000000000000) (7642229061 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 43 12 (3448272536951879 / 25600000000000)) (orderedInterval (-26399568439 / 1000000000000) (-26399568438 / 1000000000000), orderedInterval (-63379210551 / 1000000000000) (-63379210550 / 1000000000000))) = true
  norm_num [besselStateAtRationalPoint, besselIntervalStepZero,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, besselZeroTransition,
    besselInitial, besselGridStateAt, besselGridStateBlock00, besselGridStateBlock01,
    besselGridStateBlock02, besselGridStateBlock03, besselGridStateBlock04,
    besselGridStateBlock05, besselGridStateBlock06, besselGridStateBlock07,
    besselGridStateBlock08, besselGridStateBlock09, besselGridStateBlock10,
    besselGridStateBlock11, besselGridStateBlock12, besselGridStateBlock13,
    besselGridStateBlock14, besselGridState006, besselGridState009, besselGridState013, besselGridState016, besselGridState017, besselGridState022, besselGridState023, besselGridState026, besselGridState029, besselGridState030, besselGridState032, besselGridState034, besselGridState035, besselGridState037, besselGridState038, besselGridState043, besselGridState045, besselGridState046, besselGridState051, besselGridState054, besselGridState055, besselGridState058, besselGridState063, besselGridState066, besselGridState067, besselStateSubset, linearInterval, widenInterval,
    rationalErrorInterval, rationalIntervalSubset, orderedInterval, Finset.sum_range_succ,
    IntervalRat.add, IntervalRat.mul, IntervalRat.scale, IntervalRat.singleton]

theorem compactCertificate204_stateChecks3 :
    compactCertificate204.stateChecks 9 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 66 12 (5290536834763817 / 25600000000000)) (orderedInterval (5611278452 / 1000000000000) (5611278454 / 1000000000000), orderedInterval (55204321836 / 1000000000000) (55204321838 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 38 12 (3054492865708193 / 25600000000000)) (orderedInterval (48162195970 / 1000000000000) (48162195971 / 1000000000000), orderedInterval (54716124054 / 1000000000000) (54716124055 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 67 12 (5420251191428437 / 25600000000000)) (orderedInterval (-49234347549 / 1000000000000) (-49234331878 / 1000000000000), orderedInterval (24256429840 / 1000000000000) (24256445512 / 1000000000000))) = true
  norm_num [besselStateAtRationalPoint, besselIntervalStepZero,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, besselZeroTransition,
    besselInitial, besselGridStateAt, besselGridStateBlock00, besselGridStateBlock01,
    besselGridStateBlock02, besselGridStateBlock03, besselGridStateBlock04,
    besselGridStateBlock05, besselGridStateBlock06, besselGridStateBlock07,
    besselGridStateBlock08, besselGridStateBlock09, besselGridStateBlock10,
    besselGridStateBlock11, besselGridStateBlock12, besselGridStateBlock13,
    besselGridStateBlock14, besselGridState006, besselGridState009, besselGridState013, besselGridState016, besselGridState017, besselGridState022, besselGridState023, besselGridState026, besselGridState029, besselGridState030, besselGridState032, besselGridState034, besselGridState035, besselGridState037, besselGridState038, besselGridState043, besselGridState045, besselGridState046, besselGridState051, besselGridState054, besselGridState055, besselGridState058, besselGridState063, besselGridState066, besselGridState067, besselStateSubset, linearInterval, widenInterval,
    rationalErrorInterval, rationalIntervalSubset, orderedInterval, Finset.sum_range_succ,
    IntervalRat.add, IntervalRat.mul, IntervalRat.scale, IntervalRat.singleton]

theorem compactCertificate204_stateChecks4 :
    compactCertificate204.stateChecks 12 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 63 12 (5064301759524553 / 25600000000000)) (orderedInterval (-36053474887 / 1000000000000) (-36053474886 / 1000000000000), orderedInterval (-43706776982 / 1000000000000) (-43706776981 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 45 12 (3614124698087449 / 25600000000000)) (orderedInterval (-37337682047 / 1000000000000) (-37337682046 / 1000000000000), orderedInterval (-55682543248 / 1000000000000) (-55682543247 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 51 12 (4098032210707071 / 25600000000000)) (orderedInterval (-37800878893 / 1000000000000) (-37800878892 / 1000000000000), orderedInterval (-50359644599 / 1000000000000) (-50359644598 / 1000000000000))) = true
  norm_num [besselStateAtRationalPoint, besselIntervalStepZero,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, besselZeroTransition,
    besselInitial, besselGridStateAt, besselGridStateBlock00, besselGridStateBlock01,
    besselGridStateBlock02, besselGridStateBlock03, besselGridStateBlock04,
    besselGridStateBlock05, besselGridStateBlock06, besselGridStateBlock07,
    besselGridStateBlock08, besselGridStateBlock09, besselGridStateBlock10,
    besselGridStateBlock11, besselGridStateBlock12, besselGridStateBlock13,
    besselGridStateBlock14, besselGridState006, besselGridState009, besselGridState013, besselGridState016, besselGridState017, besselGridState022, besselGridState023, besselGridState026, besselGridState029, besselGridState030, besselGridState032, besselGridState034, besselGridState035, besselGridState037, besselGridState038, besselGridState043, besselGridState045, besselGridState046, besselGridState051, besselGridState054, besselGridState055, besselGridState058, besselGridState063, besselGridState066, besselGridState067, besselStateSubset, linearInterval, widenInterval,
    rationalErrorInterval, rationalIntervalSubset, orderedInterval, Finset.sum_range_succ,
    IntervalRat.add, IntervalRat.mul, IntervalRat.scale, IntervalRat.singleton]

theorem compactCertificate204_stateChecks5 :
    compactCertificate204.stateChecks 15 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 43 12 (3416512015952399 / 25600000000000)) (orderedInterval (51729349956 / 1000000000000) (51729456226 / 1000000000000), orderedInterval (-45957053192 / 1000000000000) (-45956946922 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 38 12 (3018591978508379 / 25600000000000)) (orderedInterval (-46341216568 / 1000000000000) (-46341189555 / 1000000000000), orderedInterval (57218692611 / 1000000000000) (57218719625 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 54 12 (874905610645521 / 5120000000000)) (orderedInterval (55017073360 / 1000000000000) (55017085225 / 1000000000000), orderedInterval (-26592936368 / 1000000000000) (-26592924503 / 1000000000000))) = true
  norm_num [besselStateAtRationalPoint, besselIntervalStepZero,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, besselZeroTransition,
    besselInitial, besselGridStateAt, besselGridStateBlock00, besselGridStateBlock01,
    besselGridStateBlock02, besselGridStateBlock03, besselGridStateBlock04,
    besselGridStateBlock05, besselGridStateBlock06, besselGridStateBlock07,
    besselGridStateBlock08, besselGridStateBlock09, besselGridStateBlock10,
    besselGridStateBlock11, besselGridStateBlock12, besselGridStateBlock13,
    besselGridStateBlock14, besselGridState006, besselGridState009, besselGridState013, besselGridState016, besselGridState017, besselGridState022, besselGridState023, besselGridState026, besselGridState029, besselGridState030, besselGridState032, besselGridState034, besselGridState035, besselGridState037, besselGridState038, besselGridState043, besselGridState045, besselGridState046, besselGridState051, besselGridState054, besselGridState055, besselGridState058, besselGridState063, besselGridState066, besselGridState067, besselStateSubset, linearInterval, widenInterval,
    rationalErrorInterval, rationalIntervalSubset, orderedInterval, Finset.sum_range_succ,
    IntervalRat.add, IntervalRat.mul, IntervalRat.scale, IntervalRat.singleton]

theorem compactCertificate204_stateChecks6 :
    compactCertificate204.stateChecks 18 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 30 12 (2420034962805187 / 25600000000000)) (orderedInterval (71942598380 / 1000000000000) (71942598381 / 1000000000000), orderedInterval (39098662629 / 1000000000000) (39098662630 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 26 12 (2051490439123307 / 25600000000000)) (orderedInterval (-61482308742 / 1000000000000) (-61482244224 / 1000000000000), orderedInterval (64913745064 / 1000000000000) (64913809583 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 16 12 (1283727463048121 / 25600000000000)) (orderedInterval (69349758212 / 1000000000000) (69349758213 / 1000000000000), orderedInterval (88112803192 / 1000000000000) (88112803193 / 1000000000000))) = true
  norm_num [besselStateAtRationalPoint, besselIntervalStepZero,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, besselZeroTransition,
    besselInitial, besselGridStateAt, besselGridStateBlock00, besselGridStateBlock01,
    besselGridStateBlock02, besselGridStateBlock03, besselGridStateBlock04,
    besselGridStateBlock05, besselGridStateBlock06, besselGridStateBlock07,
    besselGridStateBlock08, besselGridStateBlock09, besselGridStateBlock10,
    besselGridStateBlock11, besselGridStateBlock12, besselGridStateBlock13,
    besselGridStateBlock14, besselGridState006, besselGridState009, besselGridState013, besselGridState016, besselGridState017, besselGridState022, besselGridState023, besselGridState026, besselGridState029, besselGridState030, besselGridState032, besselGridState034, besselGridState035, besselGridState037, besselGridState038, besselGridState043, besselGridState045, besselGridState046, besselGridState051, besselGridState054, besselGridState055, besselGridState058, besselGridState063, besselGridState066, besselGridState067, besselStateSubset, linearInterval, widenInterval,
    rationalErrorInterval, rationalIntervalSubset, orderedInterval, Finset.sum_range_succ,
    IntervalRat.add, IntervalRat.mul, IntervalRat.scale, IntervalRat.singleton]

theorem compactCertificate204_stateChecks7 :
    compactCertificate204.stateChecks 21 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 9 12 (690392899112007 / 25600000000000)) (orderedInterval (77013710819 / 1000000000000) (77013719755 / 1000000000000), orderedInterval (-134382151693 / 1000000000000) (-134382142757 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 23 12 (1874551021637021 / 25600000000000)) (orderedInterval (-91719167289 / 1000000000000) (-91719166947 / 1000000000000), orderedInterval (17403285065 / 1000000000000) (17403285407 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 32 12 (2559539159749117 / 25600000000000)) (orderedInterval (18593824290 / 1000000000000) (18593824291 / 1000000000000), orderedInterval (77506530682 / 1000000000000) (77506530683 / 1000000000000))) = true
  norm_num [besselStateAtRationalPoint, besselIntervalStepZero,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, besselZeroTransition,
    besselInitial, besselGridStateAt, besselGridStateBlock00, besselGridStateBlock01,
    besselGridStateBlock02, besselGridStateBlock03, besselGridStateBlock04,
    besselGridStateBlock05, besselGridStateBlock06, besselGridStateBlock07,
    besselGridStateBlock08, besselGridStateBlock09, besselGridStateBlock10,
    besselGridStateBlock11, besselGridStateBlock12, besselGridStateBlock13,
    besselGridStateBlock14, besselGridState006, besselGridState009, besselGridState013, besselGridState016, besselGridState017, besselGridState022, besselGridState023, besselGridState026, besselGridState029, besselGridState030, besselGridState032, besselGridState034, besselGridState035, besselGridState037, besselGridState038, besselGridState043, besselGridState045, besselGridState046, besselGridState051, besselGridState054, besselGridState055, besselGridState058, besselGridState063, besselGridState066, besselGridState067, besselStateSubset, linearInterval, widenInterval,
    rationalErrorInterval, rationalIntervalSubset, orderedInterval, Finset.sum_range_succ,
    IntervalRat.add, IntervalRat.mul, IntervalRat.scale, IntervalRat.singleton]

theorem compactCertificate204_stateChecks8 :
    compactCertificate204.stateChecks 24 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 13 12 (1082272536951879 / 25600000000000)) (orderedInterval (-97893327141 / 1000000000000) (-97893284591 / 1000000000000), orderedInterval (75152011254 / 1000000000000) (75152053805 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 55 12 (4399377776734759 / 25600000000000)) (orderedInterval (9229690989 / 1000000000000) (9229691028 / 1000000000000), orderedInterval (-60187648266 / 1000000000000) (-60187648227 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 37 12 (2938580469815081 / 25600000000000)) (orderedInterval (46030487001 / 1000000000000) (46030510598 / 1000000000000), orderedInterval (-58743136188 / 1000000000000) (-58743112591 / 1000000000000))) = true
  norm_num [besselStateAtRationalPoint, besselIntervalStepZero,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, besselZeroTransition,
    besselInitial, besselGridStateAt, besselGridStateBlock00, besselGridStateBlock01,
    besselGridStateBlock02, besselGridStateBlock03, besselGridStateBlock04,
    besselGridStateBlock05, besselGridStateBlock06, besselGridStateBlock07,
    besselGridStateBlock08, besselGridStateBlock09, besselGridStateBlock10,
    besselGridStateBlock11, besselGridStateBlock12, besselGridStateBlock13,
    besselGridStateBlock14, besselGridState006, besselGridState009, besselGridState013, besselGridState016, besselGridState017, besselGridState022, besselGridState023, besselGridState026, besselGridState029, besselGridState030, besselGridState032, besselGridState034, besselGridState035, besselGridState037, besselGridState038, besselGridState043, besselGridState045, besselGridState046, besselGridState051, besselGridState054, besselGridState055, besselGridState058, besselGridState063, besselGridState066, besselGridState067, besselStateSubset, linearInterval, widenInterval,
    rationalErrorInterval, rationalIntervalSubset, orderedInterval, Finset.sum_range_succ,
    IntervalRat.add, IntervalRat.mul, IntervalRat.scale, IntervalRat.singleton]

theorem compactCertificate204_states : ∀ j,
    BesselStateValid (compactCertificate204.point j) (compactCertificate204.state j) :=
  compactCertificate204.statesValid_of_checks3 compactCertificate204_stateChecks0
    compactCertificate204_stateChecks1 compactCertificate204_stateChecks2
    compactCertificate204_stateChecks3 compactCertificate204_stateChecks4
    compactCertificate204_stateChecks5 compactCertificate204_stateChecks6
    compactCertificate204_stateChecks7 compactCertificate204_stateChecks8

theorem compactCertificate204_chunkChecks0_0 :
    compactCertificate204.chunkChecks (0 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 0) <| besselDerivativeNearFromState (5915 / 64) 0 (IntervalRat.scale (5915 / 64) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-71652819764 / 1000000000000) (-71652801958 / 1000000000000), orderedInterval (42268626976 / 1000000000000) (42268644782 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 0) <| besselDerivativeNearFromState (1742784891366883 / 25600000000000) 0 (IntervalRat.scale (5915 / 64) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-24293380419 / 1000000000000) (-24293380086 / 1000000000000), orderedInterval (93781004454 / 1000000000000) (93781004787 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 0) <| besselDerivativeNearFromState (563580826092739 / 5120000000000) 0 (IntervalRat.scale (5915 / 64) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-59708224515 / 1000000000000) (-59708224514 / 1000000000000), orderedInterval (-46829273947 / 1000000000000) (-46829273946 / 1000000000000)))) (orderedInterval (-32130783266 / 1000000000000) (-32130776198 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 0) <| besselDerivativeNearFromState (508540284733481 / 25600000000000) 0 (IntervalRat.scale (5915 / 64) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (174533514242 / 1000000000000) (174533514685 / 1000000000000), orderedInterval (-44095174296 / 1000000000000) (-44095173853 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 0) <| besselDerivativeNearFromState (1366010736902357 / 25600000000000) 0 (IntervalRat.scale (5915 / 64) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-73307917537 / 1000000000000) (-73307917536 / 1000000000000), orderedInterval (-80286607071 / 1000000000000) (-80286607070 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 0) <| besselDerivativeNearFromState (3708984877621569 / 25600000000000) 0 (IntervalRat.scale (5915 / 64) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (60599051115 / 1000000000000) (60599051116 / 1000000000000), orderedInterval (26656978226 / 1000000000000) (26656978227 / 1000000000000)))) (orderedInterval (-8878129750 / 1000000000000) (-8878129733 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 0) <| besselDerivativeNearFromState (2732021473805897 / 25600000000000) 0 (IntervalRat.scale (5915 / 64) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (49143187337 / 1000000000000) (49143187338 / 1000000000000), orderedInterval (59354240807 / 1000000000000) (59354240808 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 0) <| besselDerivativeNearFromState (4681365361180781 / 25600000000000) 0 (IntervalRat.scale (5915 / 64) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (58484724218 / 1000000000000) (58484724226 / 1000000000000), orderedInterval (7642229053 / 1000000000000) (7642229061 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 0) <| besselDerivativeNearFromState (3448272536951879 / 25600000000000) 0 (IntervalRat.scale (5915 / 64) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-26399568439 / 1000000000000) (-26399568438 / 1000000000000), orderedInterval (-63379210551 / 1000000000000) (-63379210550 / 1000000000000)))) (orderedInterval (-2441928378 / 1000000000000) (-2441928372 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate204_chunkChecks0_1 :
    compactCertificate204.chunkChecks (0 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 0) <| besselDerivativeNearFromState (5290536834763817 / 25600000000000) 0 (IntervalRat.scale (5915 / 64) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (5611278452 / 1000000000000) (5611278454 / 1000000000000), orderedInterval (55204321836 / 1000000000000) (55204321838 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 0) <| besselDerivativeNearFromState (3054492865708193 / 25600000000000) 0 (IntervalRat.scale (5915 / 64) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (48162195970 / 1000000000000) (48162195971 / 1000000000000), orderedInterval (54716124054 / 1000000000000) (54716124055 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 0) <| besselDerivativeNearFromState (5420251191428437 / 25600000000000) 0 (IntervalRat.scale (5915 / 64) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-49234347549 / 1000000000000) (-49234331878 / 1000000000000), orderedInterval (24256429840 / 1000000000000) (24256445512 / 1000000000000)))) (orderedInterval (-4427586648 / 1000000000000) (-4427584382 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 0) <| besselDerivativeNearFromState (5064301759524553 / 25600000000000) 0 (IntervalRat.scale (5915 / 64) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-36053474887 / 1000000000000) (-36053474886 / 1000000000000), orderedInterval (-43706776982 / 1000000000000) (-43706776981 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 0) <| besselDerivativeNearFromState (3614124698087449 / 25600000000000) 0 (IntervalRat.scale (5915 / 64) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-37337682047 / 1000000000000) (-37337682046 / 1000000000000), orderedInterval (-55682543248 / 1000000000000) (-55682543247 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 0) <| besselDerivativeNearFromState (4098032210707071 / 25600000000000) 0 (IntervalRat.scale (5915 / 64) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-37800878893 / 1000000000000) (-37800878892 / 1000000000000), orderedInterval (-50359644599 / 1000000000000) (-50359644598 / 1000000000000)))) (orderedInterval (-2688587527 / 1000000000000) (-2688587515 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 0) <| besselDerivativeNearFromState (3416512015952399 / 25600000000000) 0 (IntervalRat.scale (5915 / 64) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (51729349956 / 1000000000000) (51729456226 / 1000000000000), orderedInterval (-45957053192 / 1000000000000) (-45956946922 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 0) <| besselDerivativeNearFromState (3018591978508379 / 25600000000000) 0 (IntervalRat.scale (5915 / 64) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-46341216568 / 1000000000000) (-46341189555 / 1000000000000), orderedInterval (57218692611 / 1000000000000) (57218719625 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 0) <| besselDerivativeNearFromState (874905610645521 / 5120000000000) 0 (IntervalRat.scale (5915 / 64) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (55017073360 / 1000000000000) (55017085225 / 1000000000000), orderedInterval (-26592936368 / 1000000000000) (-26592924503 / 1000000000000)))) (orderedInterval (4657960140 / 1000000000000) (4657963226 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate204_chunkChecks0_2 :
    compactCertificate204.chunkChecks (0 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 0) <| besselDerivativeNearFromState (2420034962805187 / 25600000000000) 0 (IntervalRat.scale (5915 / 64) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (71942598380 / 1000000000000) (71942598381 / 1000000000000), orderedInterval (39098662629 / 1000000000000) (39098662630 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 0) <| besselDerivativeNearFromState (2051490439123307 / 25600000000000) 0 (IntervalRat.scale (5915 / 64) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-61482308742 / 1000000000000) (-61482244224 / 1000000000000), orderedInterval (64913745064 / 1000000000000) (64913809583 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 0) <| besselDerivativeNearFromState (1283727463048121 / 25600000000000) 0 (IntervalRat.scale (5915 / 64) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (69349758212 / 1000000000000) (69349758213 / 1000000000000), orderedInterval (88112803192 / 1000000000000) (88112803193 / 1000000000000)))) (orderedInterval (-5765485261 / 1000000000000) (-5765481585 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 0) <| besselDerivativeNearFromState (690392899112007 / 25600000000000) 0 (IntervalRat.scale (5915 / 64) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (77013710819 / 1000000000000) (77013719755 / 1000000000000), orderedInterval (-134382151693 / 1000000000000) (-134382142757 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 0) <| besselDerivativeNearFromState (1874551021637021 / 25600000000000) 0 (IntervalRat.scale (5915 / 64) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-91719167289 / 1000000000000) (-91719166947 / 1000000000000), orderedInterval (17403285065 / 1000000000000) (17403285407 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 0) <| besselDerivativeNearFromState (2559539159749117 / 25600000000000) 0 (IntervalRat.scale (5915 / 64) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (18593824290 / 1000000000000) (18593824291 / 1000000000000), orderedInterval (77506530682 / 1000000000000) (77506530683 / 1000000000000)))) (orderedInterval (-766256951 / 1000000000000) (-766256766 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 0) <| besselDerivativeNearFromState (1082272536951879 / 25600000000000) 0 (IntervalRat.scale (5915 / 64) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-97893327141 / 1000000000000) (-97893284591 / 1000000000000), orderedInterval (75152011254 / 1000000000000) (75152053805 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 0) <| besselDerivativeNearFromState (4399377776734759 / 25600000000000) 0 (IntervalRat.scale (5915 / 64) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (9229690989 / 1000000000000) (9229691028 / 1000000000000), orderedInterval (-60187648266 / 1000000000000) (-60187648227 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 0) <| besselDerivativeNearFromState (2938580469815081 / 25600000000000) 0 (IntervalRat.scale (5915 / 64) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (46030487001 / 1000000000000) (46030510598 / 1000000000000), orderedInterval (-58743136188 / 1000000000000) (-58743112591 / 1000000000000)))) (orderedInterval (-9977991189 / 1000000000000) (-9977986475 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate204_chunkChecks0 :
    compactCertificate204.chunkChecks (0 : Fin 5) 0 9 = true :=
  compactCertificate204.chunkChecks_nine_of_three (0 : Fin 5) compactCertificate204_chunkChecks0_0
    compactCertificate204_chunkChecks0_1 compactCertificate204_chunkChecks0_2

theorem compactCertificate204_chunkChecks1_0 :
    compactCertificate204.chunkChecks (1 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 1) <| besselDerivativeNearFromState (5915 / 64) 1 (IntervalRat.scale (5915 / 64) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-71652819764 / 1000000000000) (-71652801958 / 1000000000000), orderedInterval (42268626976 / 1000000000000) (42268644782 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 1) <| besselDerivativeNearFromState (1742784891366883 / 25600000000000) 1 (IntervalRat.scale (5915 / 64) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-24293380419 / 1000000000000) (-24293380086 / 1000000000000), orderedInterval (93781004454 / 1000000000000) (93781004787 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 1) <| besselDerivativeNearFromState (563580826092739 / 5120000000000) 1 (IntervalRat.scale (5915 / 64) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-59708224515 / 1000000000000) (-59708224514 / 1000000000000), orderedInterval (-46829273947 / 1000000000000) (-46829273946 / 1000000000000)))) (orderedInterval (14124623073 / 1000000000000) (14124630141 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 1) <| besselDerivativeNearFromState (508540284733481 / 25600000000000) 1 (IntervalRat.scale (5915 / 64) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (174533514242 / 1000000000000) (174533514685 / 1000000000000), orderedInterval (-44095174296 / 1000000000000) (-44095173853 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 1) <| besselDerivativeNearFromState (1366010736902357 / 25600000000000) 1 (IntervalRat.scale (5915 / 64) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-73307917537 / 1000000000000) (-73307917536 / 1000000000000), orderedInterval (-80286607071 / 1000000000000) (-80286607070 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 1) <| besselDerivativeNearFromState (3708984877621569 / 25600000000000) 1 (IntervalRat.scale (5915 / 64) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (60599051115 / 1000000000000) (60599051116 / 1000000000000), orderedInterval (26656978226 / 1000000000000) (26656978227 / 1000000000000)))) (orderedInterval (-4560312539 / 1000000000000) (-4560312524 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 1) <| besselDerivativeNearFromState (2732021473805897 / 25600000000000) 1 (IntervalRat.scale (5915 / 64) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (49143187337 / 1000000000000) (49143187338 / 1000000000000), orderedInterval (59354240807 / 1000000000000) (59354240808 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 1) <| besselDerivativeNearFromState (4681365361180781 / 25600000000000) 1 (IntervalRat.scale (5915 / 64) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (58484724218 / 1000000000000) (58484724226 / 1000000000000), orderedInterval (7642229053 / 1000000000000) (7642229061 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 1) <| besselDerivativeNearFromState (3448272536951879 / 25600000000000) 1 (IntervalRat.scale (5915 / 64) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-26399568439 / 1000000000000) (-26399568438 / 1000000000000), orderedInterval (-63379210551 / 1000000000000) (-63379210550 / 1000000000000)))) (orderedInterval (-2698803941 / 1000000000000) (-2698803931 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate204_chunkChecks1_1 :
    compactCertificate204.chunkChecks (1 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 1) <| besselDerivativeNearFromState (5290536834763817 / 25600000000000) 1 (IntervalRat.scale (5915 / 64) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (5611278452 / 1000000000000) (5611278454 / 1000000000000), orderedInterval (55204321836 / 1000000000000) (55204321838 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 1) <| besselDerivativeNearFromState (3054492865708193 / 25600000000000) 1 (IntervalRat.scale (5915 / 64) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (48162195970 / 1000000000000) (48162195971 / 1000000000000), orderedInterval (54716124054 / 1000000000000) (54716124055 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 1) <| besselDerivativeNearFromState (5420251191428437 / 25600000000000) 1 (IntervalRat.scale (5915 / 64) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-49234347549 / 1000000000000) (-49234331878 / 1000000000000), orderedInterval (24256429840 / 1000000000000) (24256445512 / 1000000000000)))) (orderedInterval (-8800754811 / 1000000000000) (-8800749629 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 1) <| besselDerivativeNearFromState (5064301759524553 / 25600000000000) 1 (IntervalRat.scale (5915 / 64) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-36053474887 / 1000000000000) (-36053474886 / 1000000000000), orderedInterval (-43706776982 / 1000000000000) (-43706776981 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 1) <| besselDerivativeNearFromState (3614124698087449 / 25600000000000) 1 (IntervalRat.scale (5915 / 64) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-37337682047 / 1000000000000) (-37337682046 / 1000000000000), orderedInterval (-55682543248 / 1000000000000) (-55682543247 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 1) <| besselDerivativeNearFromState (4098032210707071 / 25600000000000) 1 (IntervalRat.scale (5915 / 64) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-37800878893 / 1000000000000) (-37800878892 / 1000000000000), orderedInterval (-50359644599 / 1000000000000) (-50359644598 / 1000000000000)))) (orderedInterval (-5912869965 / 1000000000000) (-5912869946 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 1) <| besselDerivativeNearFromState (3416512015952399 / 25600000000000) 1 (IntervalRat.scale (5915 / 64) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (51729349956 / 1000000000000) (51729456226 / 1000000000000), orderedInterval (-45957053192 / 1000000000000) (-45956946922 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 1) <| besselDerivativeNearFromState (3018591978508379 / 25600000000000) 1 (IntervalRat.scale (5915 / 64) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-46341216568 / 1000000000000) (-46341189555 / 1000000000000), orderedInterval (57218692611 / 1000000000000) (57218719625 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 1) <| besselDerivativeNearFromState (874905610645521 / 5120000000000) 1 (IntervalRat.scale (5915 / 64) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (55017073360 / 1000000000000) (55017085225 / 1000000000000), orderedInterval (-26592936368 / 1000000000000) (-26592924503 / 1000000000000)))) (orderedInterval (-6202818772 / 1000000000000) (-6202814452 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate204_chunkChecks1_2 :
    compactCertificate204.chunkChecks (1 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 1) <| besselDerivativeNearFromState (2420034962805187 / 25600000000000) 1 (IntervalRat.scale (5915 / 64) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (71942598380 / 1000000000000) (71942598381 / 1000000000000), orderedInterval (39098662629 / 1000000000000) (39098662630 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 1) <| besselDerivativeNearFromState (2051490439123307 / 25600000000000) 1 (IntervalRat.scale (5915 / 64) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-61482308742 / 1000000000000) (-61482244224 / 1000000000000), orderedInterval (64913745064 / 1000000000000) (64913809583 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 1) <| besselDerivativeNearFromState (1283727463048121 / 25600000000000) 1 (IntervalRat.scale (5915 / 64) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (69349758212 / 1000000000000) (69349758213 / 1000000000000), orderedInterval (88112803192 / 1000000000000) (88112803193 / 1000000000000)))) (orderedInterval (-8023687491 / 1000000000000) (-8023684302 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 1) <| besselDerivativeNearFromState (690392899112007 / 25600000000000) 1 (IntervalRat.scale (5915 / 64) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (77013710819 / 1000000000000) (77013719755 / 1000000000000), orderedInterval (-134382151693 / 1000000000000) (-134382142757 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 1) <| besselDerivativeNearFromState (1874551021637021 / 25600000000000) 1 (IntervalRat.scale (5915 / 64) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-91719167289 / 1000000000000) (-91719166947 / 1000000000000), orderedInterval (17403285065 / 1000000000000) (17403285407 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 1) <| besselDerivativeNearFromState (2559539159749117 / 25600000000000) 1 (IntervalRat.scale (5915 / 64) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (18593824290 / 1000000000000) (18593824291 / 1000000000000), orderedInterval (77506530682 / 1000000000000) (77506530683 / 1000000000000)))) (orderedInterval (-6014661271 / 1000000000000) (-6014661206 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 1) <| besselDerivativeNearFromState (1082272536951879 / 25600000000000) 1 (IntervalRat.scale (5915 / 64) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-97893327141 / 1000000000000) (-97893284591 / 1000000000000), orderedInterval (75152011254 / 1000000000000) (75152053805 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 1) <| besselDerivativeNearFromState (4399377776734759 / 25600000000000) 1 (IntervalRat.scale (5915 / 64) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (9229690989 / 1000000000000) (9229691028 / 1000000000000), orderedInterval (-60187648266 / 1000000000000) (-60187648227 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 1) <| besselDerivativeNearFromState (2938580469815081 / 25600000000000) 1 (IntervalRat.scale (5915 / 64) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (46030487001 / 1000000000000) (46030510598 / 1000000000000), orderedInterval (-58743136188 / 1000000000000) (-58743112591 / 1000000000000)))) (orderedInterval (23006293675 / 1000000000000) (23006299334 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate204_chunkChecks1 :
    compactCertificate204.chunkChecks (1 : Fin 5) 0 9 = true :=
  compactCertificate204.chunkChecks_nine_of_three (1 : Fin 5) compactCertificate204_chunkChecks1_0
    compactCertificate204_chunkChecks1_1 compactCertificate204_chunkChecks1_2

theorem compactCertificate204_chunkChecks2_0 :
    compactCertificate204.chunkChecks (2 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 2) <| besselDerivativeNearFromState (5915 / 64) 2 (IntervalRat.scale (5915 / 64) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-71652819764 / 1000000000000) (-71652801958 / 1000000000000), orderedInterval (42268626976 / 1000000000000) (42268644782 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 2) <| besselDerivativeNearFromState (1742784891366883 / 25600000000000) 2 (IntervalRat.scale (5915 / 64) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-24293380419 / 1000000000000) (-24293380086 / 1000000000000), orderedInterval (93781004454 / 1000000000000) (93781004787 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 2) <| besselDerivativeNearFromState (563580826092739 / 5120000000000) 2 (IntervalRat.scale (5915 / 64) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-59708224515 / 1000000000000) (-59708224514 / 1000000000000), orderedInterval (-46829273947 / 1000000000000) (-46829273946 / 1000000000000)))) (orderedInterval (33340646754 / 1000000000000) (33340653899 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 2) <| besselDerivativeNearFromState (508540284733481 / 25600000000000) 2 (IntervalRat.scale (5915 / 64) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (174533514242 / 1000000000000) (174533514685 / 1000000000000), orderedInterval (-44095174296 / 1000000000000) (-44095173853 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 2) <| besselDerivativeNearFromState (1366010736902357 / 25600000000000) 2 (IntervalRat.scale (5915 / 64) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-73307917537 / 1000000000000) (-73307917536 / 1000000000000), orderedInterval (-80286607071 / 1000000000000) (-80286607070 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 2) <| besselDerivativeNearFromState (3708984877621569 / 25600000000000) 2 (IntervalRat.scale (5915 / 64) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (60599051115 / 1000000000000) (60599051116 / 1000000000000), orderedInterval (26656978226 / 1000000000000) (26656978227 / 1000000000000)))) (orderedInterval (11615530335 / 1000000000000) (11615530354 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 2) <| besselDerivativeNearFromState (2732021473805897 / 25600000000000) 2 (IntervalRat.scale (5915 / 64) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (49143187337 / 1000000000000) (49143187338 / 1000000000000), orderedInterval (59354240807 / 1000000000000) (59354240808 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 2) <| besselDerivativeNearFromState (4681365361180781 / 25600000000000) 2 (IntervalRat.scale (5915 / 64) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (58484724218 / 1000000000000) (58484724226 / 1000000000000), orderedInterval (7642229053 / 1000000000000) (7642229061 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 2) <| besselDerivativeNearFromState (3448272536951879 / 25600000000000) 2 (IntervalRat.scale (5915 / 64) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-26399568439 / 1000000000000) (-26399568438 / 1000000000000), orderedInterval (-63379210551 / 1000000000000) (-63379210550 / 1000000000000)))) (orderedInterval (8446443711 / 1000000000000) (8446443729 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate204_chunkChecks2_1 :
    compactCertificate204.chunkChecks (2 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 2) <| besselDerivativeNearFromState (5290536834763817 / 25600000000000) 2 (IntervalRat.scale (5915 / 64) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (5611278452 / 1000000000000) (5611278454 / 1000000000000), orderedInterval (55204321836 / 1000000000000) (55204321838 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 2) <| besselDerivativeNearFromState (3054492865708193 / 25600000000000) 2 (IntervalRat.scale (5915 / 64) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (48162195970 / 1000000000000) (48162195971 / 1000000000000), orderedInterval (54716124054 / 1000000000000) (54716124055 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 2) <| besselDerivativeNearFromState (5420251191428437 / 25600000000000) 2 (IntervalRat.scale (5915 / 64) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-49234347549 / 1000000000000) (-49234331878 / 1000000000000), orderedInterval (24256429840 / 1000000000000) (24256445512 / 1000000000000)))) (orderedInterval (35864939238 / 1000000000000) (35864951151 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 2) <| besselDerivativeNearFromState (5064301759524553 / 25600000000000) 2 (IntervalRat.scale (5915 / 64) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-36053474887 / 1000000000000) (-36053474886 / 1000000000000), orderedInterval (-43706776982 / 1000000000000) (-43706776981 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 2) <| besselDerivativeNearFromState (3614124698087449 / 25600000000000) 2 (IntervalRat.scale (5915 / 64) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-37337682047 / 1000000000000) (-37337682046 / 1000000000000), orderedInterval (-55682543248 / 1000000000000) (-55682543247 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 2) <| besselDerivativeNearFromState (4098032210707071 / 25600000000000) 2 (IntervalRat.scale (5915 / 64) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-37800878893 / 1000000000000) (-37800878892 / 1000000000000), orderedInterval (-50359644599 / 1000000000000) (-50359644598 / 1000000000000)))) (orderedInterval (4746525935 / 1000000000000) (4746525966 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 2) <| besselDerivativeNearFromState (3416512015952399 / 25600000000000) 2 (IntervalRat.scale (5915 / 64) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (51729349956 / 1000000000000) (51729456226 / 1000000000000), orderedInterval (-45957053192 / 1000000000000) (-45956946922 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 2) <| besselDerivativeNearFromState (3018591978508379 / 25600000000000) 2 (IntervalRat.scale (5915 / 64) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-46341216568 / 1000000000000) (-46341189555 / 1000000000000), orderedInterval (57218692611 / 1000000000000) (57218719625 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 2) <| besselDerivativeNearFromState (874905610645521 / 5120000000000) 2 (IntervalRat.scale (5915 / 64) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (55017073360 / 1000000000000) (55017085225 / 1000000000000), orderedInterval (-26592936368 / 1000000000000) (-26592924503 / 1000000000000)))) (orderedInterval (-10310548942 / 1000000000000) (-10310542762 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate204_chunkChecks2_2 :
    compactCertificate204.chunkChecks (2 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 2) <| besselDerivativeNearFromState (2420034962805187 / 25600000000000) 2 (IntervalRat.scale (5915 / 64) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (71942598380 / 1000000000000) (71942598381 / 1000000000000), orderedInterval (39098662629 / 1000000000000) (39098662630 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 2) <| besselDerivativeNearFromState (2051490439123307 / 25600000000000) 2 (IntervalRat.scale (5915 / 64) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-61482308742 / 1000000000000) (-61482244224 / 1000000000000), orderedInterval (64913745064 / 1000000000000) (64913809583 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 2) <| besselDerivativeNearFromState (1283727463048121 / 25600000000000) 2 (IntervalRat.scale (5915 / 64) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (69349758212 / 1000000000000) (69349758213 / 1000000000000), orderedInterval (88112803192 / 1000000000000) (88112803193 / 1000000000000)))) (orderedInterval (8840447448 / 1000000000000) (8840450250 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 2) <| besselDerivativeNearFromState (690392899112007 / 25600000000000) 2 (IntervalRat.scale (5915 / 64) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (77013710819 / 1000000000000) (77013719755 / 1000000000000), orderedInterval (-134382151693 / 1000000000000) (-134382142757 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 2) <| besselDerivativeNearFromState (1874551021637021 / 25600000000000) 2 (IntervalRat.scale (5915 / 64) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-91719167289 / 1000000000000) (-91719166947 / 1000000000000), orderedInterval (17403285065 / 1000000000000) (17403285407 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 2) <| besselDerivativeNearFromState (2559539159749117 / 25600000000000) 2 (IntervalRat.scale (5915 / 64) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (18593824290 / 1000000000000) (18593824291 / 1000000000000), orderedInterval (77506530682 / 1000000000000) (77506530683 / 1000000000000)))) (orderedInterval (547668533 / 1000000000000) (547668563 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 2) <| besselDerivativeNearFromState (1082272536951879 / 25600000000000) 2 (IntervalRat.scale (5915 / 64) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-97893327141 / 1000000000000) (-97893284591 / 1000000000000), orderedInterval (75152011254 / 1000000000000) (75152053805 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 2) <| besselDerivativeNearFromState (4399377776734759 / 25600000000000) 2 (IntervalRat.scale (5915 / 64) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (9229690989 / 1000000000000) (9229691028 / 1000000000000), orderedInterval (-60187648266 / 1000000000000) (-60187648227 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 2) <| besselDerivativeNearFromState (2938580469815081 / 25600000000000) 2 (IntervalRat.scale (5915 / 64) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (46030487001 / 1000000000000) (46030510598 / 1000000000000), orderedInterval (-58743136188 / 1000000000000) (-58743112591 / 1000000000000)))) (orderedInterval (15794656025 / 1000000000000) (15794663034 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate204_chunkChecks2 :
    compactCertificate204.chunkChecks (2 : Fin 5) 0 9 = true :=
  compactCertificate204.chunkChecks_nine_of_three (2 : Fin 5) compactCertificate204_chunkChecks2_0
    compactCertificate204_chunkChecks2_1 compactCertificate204_chunkChecks2_2

theorem compactCertificate204_chunkChecks3_0 :
    compactCertificate204.chunkChecks (3 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 3) <| besselDerivativeNearFromState (5915 / 64) 3 (IntervalRat.scale (5915 / 64) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-71652819764 / 1000000000000) (-71652801958 / 1000000000000), orderedInterval (42268626976 / 1000000000000) (42268644782 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 3) <| besselDerivativeNearFromState (1742784891366883 / 25600000000000) 3 (IntervalRat.scale (5915 / 64) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-24293380419 / 1000000000000) (-24293380086 / 1000000000000), orderedInterval (93781004454 / 1000000000000) (93781004787 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 3) <| besselDerivativeNearFromState (563580826092739 / 5120000000000) 3 (IntervalRat.scale (5915 / 64) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-59708224515 / 1000000000000) (-59708224514 / 1000000000000), orderedInterval (-46829273947 / 1000000000000) (-46829273946 / 1000000000000)))) (orderedInterval (-12819660850 / 1000000000000) (-12819653706 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 3) <| besselDerivativeNearFromState (508540284733481 / 25600000000000) 3 (IntervalRat.scale (5915 / 64) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (174533514242 / 1000000000000) (174533514685 / 1000000000000), orderedInterval (-44095174296 / 1000000000000) (-44095173853 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 3) <| besselDerivativeNearFromState (1366010736902357 / 25600000000000) 3 (IntervalRat.scale (5915 / 64) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-73307917537 / 1000000000000) (-73307917536 / 1000000000000), orderedInterval (-80286607071 / 1000000000000) (-80286607070 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 3) <| besselDerivativeNearFromState (3708984877621569 / 25600000000000) 3 (IntervalRat.scale (5915 / 64) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (60599051115 / 1000000000000) (60599051116 / 1000000000000), orderedInterval (26656978226 / 1000000000000) (26656978227 / 1000000000000)))) (orderedInterval (7733443261 / 1000000000000) (7733443289 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 3) <| besselDerivativeNearFromState (2732021473805897 / 25600000000000) 3 (IntervalRat.scale (5915 / 64) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (49143187337 / 1000000000000) (49143187338 / 1000000000000), orderedInterval (59354240807 / 1000000000000) (59354240808 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 3) <| besselDerivativeNearFromState (4681365361180781 / 25600000000000) 3 (IntervalRat.scale (5915 / 64) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (58484724218 / 1000000000000) (58484724226 / 1000000000000), orderedInterval (7642229053 / 1000000000000) (7642229061 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 3) <| besselDerivativeNearFromState (3448272536951879 / 25600000000000) 3 (IntervalRat.scale (5915 / 64) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-26399568439 / 1000000000000) (-26399568438 / 1000000000000), orderedInterval (-63379210551 / 1000000000000) (-63379210550 / 1000000000000)))) (orderedInterval (6475998044 / 1000000000000) (6475998076 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate204_chunkChecks3_1 :
    compactCertificate204.chunkChecks (3 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 3) <| besselDerivativeNearFromState (5290536834763817 / 25600000000000) 3 (IntervalRat.scale (5915 / 64) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (5611278452 / 1000000000000) (5611278454 / 1000000000000), orderedInterval (55204321836 / 1000000000000) (55204321838 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 3) <| besselDerivativeNearFromState (3054492865708193 / 25600000000000) 3 (IntervalRat.scale (5915 / 64) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (48162195970 / 1000000000000) (48162195971 / 1000000000000), orderedInterval (54716124054 / 1000000000000) (54716124055 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 3) <| besselDerivativeNearFromState (5420251191428437 / 25600000000000) 3 (IntervalRat.scale (5915 / 64) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-49234347549 / 1000000000000) (-49234331878 / 1000000000000), orderedInterval (24256429840 / 1000000000000) (24256445512 / 1000000000000)))) (orderedInterval (59099817323 / 1000000000000) (59099844596 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 3) <| besselDerivativeNearFromState (5064301759524553 / 25600000000000) 3 (IntervalRat.scale (5915 / 64) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-36053474887 / 1000000000000) (-36053474886 / 1000000000000), orderedInterval (-43706776982 / 1000000000000) (-43706776981 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 3) <| besselDerivativeNearFromState (3614124698087449 / 25600000000000) 3 (IntervalRat.scale (5915 / 64) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-37337682047 / 1000000000000) (-37337682046 / 1000000000000), orderedInterval (-55682543248 / 1000000000000) (-55682543247 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 3) <| besselDerivativeNearFromState (4098032210707071 / 25600000000000) 3 (IntervalRat.scale (5915 / 64) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-37800878893 / 1000000000000) (-37800878892 / 1000000000000), orderedInterval (-50359644599 / 1000000000000) (-50359644598 / 1000000000000)))) (orderedInterval (9653399230 / 1000000000000) (9653399282 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 3) <| besselDerivativeNearFromState (3416512015952399 / 25600000000000) 3 (IntervalRat.scale (5915 / 64) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (51729349956 / 1000000000000) (51729456226 / 1000000000000), orderedInterval (-45957053192 / 1000000000000) (-45956946922 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 3) <| besselDerivativeNearFromState (3018591978508379 / 25600000000000) 3 (IntervalRat.scale (5915 / 64) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-46341216568 / 1000000000000) (-46341189555 / 1000000000000), orderedInterval (57218692611 / 1000000000000) (57218719625 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 3) <| besselDerivativeNearFromState (874905610645521 / 5120000000000) 3 (IntervalRat.scale (5915 / 64) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (55017073360 / 1000000000000) (55017085225 / 1000000000000), orderedInterval (-26592936368 / 1000000000000) (-26592924503 / 1000000000000)))) (orderedInterval (12812188254 / 1000000000000) (12812197174 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate204_chunkChecks3_2 :
    compactCertificate204.chunkChecks (3 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 3) <| besselDerivativeNearFromState (2420034962805187 / 25600000000000) 3 (IntervalRat.scale (5915 / 64) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (71942598380 / 1000000000000) (71942598381 / 1000000000000), orderedInterval (39098662629 / 1000000000000) (39098662630 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 3) <| besselDerivativeNearFromState (2051490439123307 / 25600000000000) 3 (IntervalRat.scale (5915 / 64) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-61482308742 / 1000000000000) (-61482244224 / 1000000000000), orderedInterval (64913745064 / 1000000000000) (64913809583 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 3) <| besselDerivativeNearFromState (1283727463048121 / 25600000000000) 3 (IntervalRat.scale (5915 / 64) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (69349758212 / 1000000000000) (69349758213 / 1000000000000), orderedInterval (88112803192 / 1000000000000) (88112803193 / 1000000000000)))) (orderedInterval (8530052528 / 1000000000000) (8530054959 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 3) <| besselDerivativeNearFromState (690392899112007 / 25600000000000) 3 (IntervalRat.scale (5915 / 64) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (77013710819 / 1000000000000) (77013719755 / 1000000000000), orderedInterval (-134382151693 / 1000000000000) (-134382142757 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 3) <| besselDerivativeNearFromState (1874551021637021 / 25600000000000) 3 (IntervalRat.scale (5915 / 64) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-91719167289 / 1000000000000) (-91719166947 / 1000000000000), orderedInterval (17403285065 / 1000000000000) (17403285407 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 3) <| besselDerivativeNearFromState (2559539159749117 / 25600000000000) 3 (IntervalRat.scale (5915 / 64) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (18593824290 / 1000000000000) (18593824291 / 1000000000000), orderedInterval (77506530682 / 1000000000000) (77506530683 / 1000000000000)))) (orderedInterval (7648264106 / 1000000000000) (7648264125 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 3) <| besselDerivativeNearFromState (1082272536951879 / 25600000000000) 3 (IntervalRat.scale (5915 / 64) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-97893327141 / 1000000000000) (-97893284591 / 1000000000000), orderedInterval (75152011254 / 1000000000000) (75152053805 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 3) <| besselDerivativeNearFromState (4399377776734759 / 25600000000000) 3 (IntervalRat.scale (5915 / 64) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (9229690989 / 1000000000000) (9229691028 / 1000000000000), orderedInterval (-60187648266 / 1000000000000) (-60187648227 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 3) <| besselDerivativeNearFromState (2938580469815081 / 25600000000000) 3 (IntervalRat.scale (5915 / 64) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (46030487001 / 1000000000000) (46030510598 / 1000000000000), orderedInterval (-58743136188 / 1000000000000) (-58743112591 / 1000000000000)))) (orderedInterval (-52825084448 / 1000000000000) (-52825075765 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate204_chunkChecks3 :
    compactCertificate204.chunkChecks (3 : Fin 5) 0 9 = true :=
  compactCertificate204.chunkChecks_nine_of_three (3 : Fin 5) compactCertificate204_chunkChecks3_0
    compactCertificate204_chunkChecks3_1 compactCertificate204_chunkChecks3_2

theorem compactCertificate204_chunkChecks4_0 :
    compactCertificate204.chunkChecks (4 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 4) <| besselDerivativeNearFromState (5915 / 64) 4 (IntervalRat.scale (5915 / 64) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-71652819764 / 1000000000000) (-71652801958 / 1000000000000), orderedInterval (42268626976 / 1000000000000) (42268644782 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 4) <| besselDerivativeNearFromState (1742784891366883 / 25600000000000) 4 (IntervalRat.scale (5915 / 64) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-24293380419 / 1000000000000) (-24293380086 / 1000000000000), orderedInterval (93781004454 / 1000000000000) (93781004787 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 4) <| besselDerivativeNearFromState (563580826092739 / 5120000000000) 4 (IntervalRat.scale (5915 / 64) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-59708224515 / 1000000000000) (-59708224514 / 1000000000000), orderedInterval (-46829273947 / 1000000000000) (-46829273946 / 1000000000000)))) (orderedInterval (-35235836402 / 1000000000000) (-35235829180 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 4) <| besselDerivativeNearFromState (508540284733481 / 25600000000000) 4 (IntervalRat.scale (5915 / 64) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (174533514242 / 1000000000000) (174533514685 / 1000000000000), orderedInterval (-44095174296 / 1000000000000) (-44095173853 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 4) <| besselDerivativeNearFromState (1366010736902357 / 25600000000000) 4 (IntervalRat.scale (5915 / 64) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-73307917537 / 1000000000000) (-73307917536 / 1000000000000), orderedInterval (-80286607071 / 1000000000000) (-80286607070 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 4) <| besselDerivativeNearFromState (3708984877621569 / 25600000000000) 4 (IntervalRat.scale (5915 / 64) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (60599051115 / 1000000000000) (60599051116 / 1000000000000), orderedInterval (26656978226 / 1000000000000) (26656978227 / 1000000000000)))) (orderedInterval (-26483001951 / 1000000000000) (-26483001909 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 4) <| besselDerivativeNearFromState (2732021473805897 / 25600000000000) 4 (IntervalRat.scale (5915 / 64) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (49143187337 / 1000000000000) (49143187338 / 1000000000000), orderedInterval (59354240807 / 1000000000000) (59354240808 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 4) <| besselDerivativeNearFromState (4681365361180781 / 25600000000000) 4 (IntervalRat.scale (5915 / 64) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (58484724218 / 1000000000000) (58484724226 / 1000000000000), orderedInterval (7642229053 / 1000000000000) (7642229061 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 4) <| besselDerivativeNearFromState (3448272536951879 / 25600000000000) 4 (IntervalRat.scale (5915 / 64) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-26399568439 / 1000000000000) (-26399568438 / 1000000000000), orderedInterval (-63379210551 / 1000000000000) (-63379210550 / 1000000000000)))) (orderedInterval (-30664541138 / 1000000000000) (-30664541079 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate204_chunkChecks4_1 :
    compactCertificate204.chunkChecks (4 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 4) <| besselDerivativeNearFromState (5290536834763817 / 25600000000000) 4 (IntervalRat.scale (5915 / 64) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (5611278452 / 1000000000000) (5611278454 / 1000000000000), orderedInterval (55204321836 / 1000000000000) (55204321838 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 4) <| besselDerivativeNearFromState (3054492865708193 / 25600000000000) 4 (IntervalRat.scale (5915 / 64) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (48162195970 / 1000000000000) (48162195971 / 1000000000000), orderedInterval (54716124054 / 1000000000000) (54716124055 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 4) <| besselDerivativeNearFromState (5420251191428437 / 25600000000000) 4 (IntervalRat.scale (5915 / 64) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-49234347549 / 1000000000000) (-49234331878 / 1000000000000), orderedInterval (24256429840 / 1000000000000) (24256445512 / 1000000000000)))) (orderedInterval (-209064290071 / 1000000000000) (-209064227334 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 4) <| besselDerivativeNearFromState (5064301759524553 / 25600000000000) 4 (IntervalRat.scale (5915 / 64) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-36053474887 / 1000000000000) (-36053474886 / 1000000000000), orderedInterval (-43706776982 / 1000000000000) (-43706776981 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 4) <| besselDerivativeNearFromState (3614124698087449 / 25600000000000) 4 (IntervalRat.scale (5915 / 64) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-37337682047 / 1000000000000) (-37337682046 / 1000000000000), orderedInterval (-55682543248 / 1000000000000) (-55682543247 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 4) <| besselDerivativeNearFromState (4098032210707071 / 25600000000000) 4 (IntervalRat.scale (5915 / 64) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-37800878893 / 1000000000000) (-37800878892 / 1000000000000), orderedInterval (-50359644599 / 1000000000000) (-50359644598 / 1000000000000)))) (orderedInterval (-4047589966 / 1000000000000) (-4047589877 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 4) <| besselDerivativeNearFromState (3416512015952399 / 25600000000000) 4 (IntervalRat.scale (5915 / 64) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (51729349956 / 1000000000000) (51729456226 / 1000000000000), orderedInterval (-45957053192 / 1000000000000) (-45956946922 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 4) <| besselDerivativeNearFromState (3018591978508379 / 25600000000000) 4 (IntervalRat.scale (5915 / 64) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-46341216568 / 1000000000000) (-46341189555 / 1000000000000), orderedInterval (57218692611 / 1000000000000) (57218719625 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 4) <| besselDerivativeNearFromState (874905610645521 / 5120000000000) 4 (IntervalRat.scale (5915 / 64) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (55017073360 / 1000000000000) (55017085225 / 1000000000000), orderedInterval (-26592936368 / 1000000000000) (-26592924503 / 1000000000000)))) (orderedInterval (25806536674 / 1000000000000) (25806549892 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate204_chunkChecks4_2 :
    compactCertificate204.chunkChecks (4 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 4) <| besselDerivativeNearFromState (2420034962805187 / 25600000000000) 4 (IntervalRat.scale (5915 / 64) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (71942598380 / 1000000000000) (71942598381 / 1000000000000), orderedInterval (39098662629 / 1000000000000) (39098662630 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 4) <| besselDerivativeNearFromState (2051490439123307 / 25600000000000) 4 (IntervalRat.scale (5915 / 64) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-61482308742 / 1000000000000) (-61482244224 / 1000000000000), orderedInterval (64913745064 / 1000000000000) (64913809583 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 4) <| besselDerivativeNearFromState (1283727463048121 / 25600000000000) 4 (IntervalRat.scale (5915 / 64) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (69349758212 / 1000000000000) (69349758213 / 1000000000000), orderedInterval (88112803192 / 1000000000000) (88112803193 / 1000000000000)))) (orderedInterval (-10611436051 / 1000000000000) (-10611433916 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 4) <| besselDerivativeNearFromState (690392899112007 / 25600000000000) 4 (IntervalRat.scale (5915 / 64) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (77013710819 / 1000000000000) (77013719755 / 1000000000000), orderedInterval (-134382151693 / 1000000000000) (-134382142757 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 4) <| besselDerivativeNearFromState (1874551021637021 / 25600000000000) 4 (IntervalRat.scale (5915 / 64) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-91719167289 / 1000000000000) (-91719166947 / 1000000000000), orderedInterval (17403285065 / 1000000000000) (17403285407 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 4) <| besselDerivativeNearFromState (2559539159749117 / 25600000000000) 4 (IntervalRat.scale (5915 / 64) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (18593824290 / 1000000000000) (18593824291 / 1000000000000), orderedInterval (77506530682 / 1000000000000) (77506530683 / 1000000000000)))) (orderedInterval (-1307506689 / 1000000000000) (-1307506673 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 4) <| besselDerivativeNearFromState (1082272536951879 / 25600000000000) 4 (IntervalRat.scale (5915 / 64) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-97893327141 / 1000000000000) (-97893284591 / 1000000000000), orderedInterval (75152011254 / 1000000000000) (75152053805 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 4) <| besselDerivativeNearFromState (4399377776734759 / 25600000000000) 4 (IntervalRat.scale (5915 / 64) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (9229690989 / 1000000000000) (9229691028 / 1000000000000), orderedInterval (-60187648266 / 1000000000000) (-60187648227 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 4) <| besselDerivativeNearFromState (2938580469815081 / 25600000000000) 4 (IntervalRat.scale (5915 / 64) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (46030487001 / 1000000000000) (46030510598 / 1000000000000), orderedInterval (-58743136188 / 1000000000000) (-58743112591 / 1000000000000)))) (orderedInterval (-28412864831 / 1000000000000) (-28412853933 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate204_chunkChecks4 :
    compactCertificate204.chunkChecks (4 : Fin 5) 0 9 = true :=
  compactCertificate204.chunkChecks_nine_of_three (4 : Fin 5) compactCertificate204_chunkChecks4_0
    compactCertificate204_chunkChecks4_1 compactCertificate204_chunkChecks4_2

theorem compactCertificate204_chunks :
    ∀ r : Fin 5, ∀ b, compactCertificate204.chunkCheck r b = true :=
  compactCertificate204.chunkChecks_all (by
    intro r
    fin_cases r
    · exact compactCertificate204_chunkChecks0
    · exact compactCertificate204_chunkChecks1
    · exact compactCertificate204_chunkChecks2
    · exact compactCertificate204_chunkChecks3
    · exact compactCertificate204_chunkChecks4)

theorem compactCertificate204_coefficient0 :
    compactCertificate204.coefficientCheck (0 : Fin 5) = true := by
  norm_num [CompactCertificate.coefficientCheck, intervalFinSumHull,
    compactCertificate204, rationalIntervalSubset, orderedInterval, Fin.sum_univ_succ]

theorem compactCertificate204_coefficient1 :
    compactCertificate204.coefficientCheck (1 : Fin 5) = true := by
  norm_num [CompactCertificate.coefficientCheck, intervalFinSumHull,
    compactCertificate204, rationalIntervalSubset, orderedInterval, Fin.sum_univ_succ]

theorem compactCertificate204_coefficient2 :
    compactCertificate204.coefficientCheck (2 : Fin 5) = true := by
  norm_num [CompactCertificate.coefficientCheck, intervalFinSumHull,
    compactCertificate204, rationalIntervalSubset, orderedInterval, Fin.sum_univ_succ]

theorem compactCertificate204_coefficient3 :
    compactCertificate204.coefficientCheck (3 : Fin 5) = true := by
  norm_num [CompactCertificate.coefficientCheck, intervalFinSumHull,
    compactCertificate204, rationalIntervalSubset, orderedInterval, Fin.sum_univ_succ]

theorem compactCertificate204_coefficient4 :
    compactCertificate204.coefficientCheck (4 : Fin 5) = true := by
  norm_num [CompactCertificate.coefficientCheck, intervalFinSumHull,
    compactCertificate204, rationalIntervalSubset, orderedInterval, Fin.sum_univ_succ]

theorem compactCertificate204_coefficients : ∀ r : Fin 5,
    compactCertificate204.coefficientCheck r = true := by
  intro r
  fin_cases r
  · exact compactCertificate204_coefficient0
  · exact compactCertificate204_coefficient1
  · exact compactCertificate204_coefficient2
  · exact compactCertificate204_coefficient3
  · exact compactCertificate204_coefficient4

theorem compactCertificate204_lower : (1 : ℚ) ≤ compactCertificate204.output.lo := by
  norm_num [CompactCertificate.output, CompactCertificate.interval,
    CompactCertificate.coefficientTargetNat, compactCertificate204, dualConstant,
    intervalTaylorSum, intervalPow, intervalSub, intervalMaxAbs, widenInterval,
    rationalErrorInterval, orderedInterval, IntervalRat.add, IntervalRat.mul, IntervalRat.scale,
    IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4]

theorem compactCertificate204_proves {t : ℝ} (ht : t ∈ compactCertificate204.interval) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t :=
  compactCertificate204.proves compactCertificate204_states compactCertificate204_chunks
    compactCertificate204_coefficients compactCertificate204_lower ht

end Erdos232
