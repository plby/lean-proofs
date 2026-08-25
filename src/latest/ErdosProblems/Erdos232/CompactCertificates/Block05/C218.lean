/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, OpenAI Codex
-/
import ErdosProblems.Erdos232.CompactBase

open LeanCert.Core
namespace Erdos232

def compactCertificate218 : CompactCertificate where
  left := 98
  right := 197 / 2
  center := 393 / 4
  grid := fun i =>
    match i.val with
    | 0 => 31
    | 1 => 23
    | 2 => 37
    | 3 => 7
    | 4 => 18
    | 5 => 49
    | 6 => 36
    | 7 => 62
    | 8 => 46
    | 9 => 70
    | 10 => 40
    | 11 => 72
    | 12 => 67
    | 13 => 48
    | 14 => 54
    | 15 => 45
    | 16 => 40
    | 17 => 58
    | 18 => 32
    | 19 => 27
    | 20 => 17
    | 21 => 9
    | 22 => 25
    | 23 => 34
    | 24 => 14
    | 25 => 58
    | _ => 39
  point := fun i =>
    match i.val with
    | 0 => 393 / 4
    | 1 => 578964042525093 / 8000000000000
    | 2 => 187225075785669 / 1600000000000
    | 3 => 168940263651951 / 8000000000000
    | 4 => 453797311582947 / 8000000000000
    | 5 => 1232147977096599 / 8000000000000
    | 6 => 907594623166287 / 8000000000000
    | 7 => 1555178856250251 / 8000000000000
    | 8 => 1145537706696609 / 8000000000000
    | 9 => 1757549430314607 / 8000000000000
    | 10 => 1014721636706103 / 8000000000000
    | 11 => 1800641350998627 / 8000000000000
    | 12 => 1682392723155663 / 8000000000000
    | 13 => 1200634832078079 / 8000000000000
    | 14 => 1361391934748841 / 8000000000000
    | 15 => 1134986662949529 / 8000000000000
    | 16 => 1002795137408109 / 8000000000000
    | 17 => 290649116638791 / 1600000000000
    | 18 => 803950752647877 / 8000000000000
    | 19 => 681517956530397 / 8000000000000
    | 20 => 426462293303391 / 8000000000000
    | 21 => 229352839688097 / 8000000000000
    | 22 => 622737575235291 / 8000000000000
    | 23 => 850294919510907 / 8000000000000
    | 24 => 359537706696609 / 8000000000000
    | 25 => 1461500816785089 / 8000000000000
    | _ => 976214813725551 / 8000000000000
  state := fun i =>
    match i.val with
    | 0 => (orderedInterval (-80275340709 / 1000000000000) (-80275340614 / 1000000000000), orderedInterval (6356394281 / 1000000000000) (6356394376 / 1000000000000))
    | 1 => (orderedInterval (-73324489281 / 1000000000000) (-73324489280 / 1000000000000), orderedInterval (-57975456125 / 1000000000000) (-57975456124 / 1000000000000))
    | 2 => (orderedInterval (-73755691321 / 1000000000000) (-73755691289 / 1000000000000), orderedInterval (-401947418 / 1000000000000) (-401947386 / 1000000000000))
    | 3 => (orderedInterval (16317124587 / 1000000000000) (16317124634 / 1000000000000), orderedInterval (-173269110906 / 1000000000000) (-173269110858 / 1000000000000))
    | 4 => (orderedInterval (86733120397 / 1000000000000) (86733120398 / 1000000000000), orderedInterval (60064797944 / 1000000000000) (60064797945 / 1000000000000))
    | 5 => (orderedInterval (-48933656641 / 1000000000000) (-48933656640 / 1000000000000), orderedInterval (-41541168643 / 1000000000000) (-41541168642 / 1000000000000))
    | 6 => (orderedInterval (67948732401 / 1000000000000) (67948732402 / 1000000000000), orderedInterval (31235037324 / 1000000000000) (31235037325 / 1000000000000))
    | 7 => (orderedInterval (22462272615 / 1000000000000) (22462272616 / 1000000000000), orderedInterval (52575783940 / 1000000000000) (52575783941 / 1000000000000))
    | 8 => (orderedInterval (-34082256363 / 1000000000000) (-34082250653 / 1000000000000), orderedInterval (57428021757 / 1000000000000) (57428027467 / 1000000000000))
    | 9 => (orderedInterval (28913735624 / 1000000000000) (28913735625 / 1000000000000), orderedInterval (45340803764 / 1000000000000) (45340803765 / 1000000000000))
    | 10 => (orderedInterval (65522192563 / 1000000000000) (65522197839 / 1000000000000), orderedInterval (-27200509556 / 1000000000000) (-27200504280 / 1000000000000))
    | 11 => (orderedInterval (-17216365199 / 1000000000000) (-17216364878 / 1000000000000), orderedInterval (50357383313 / 1000000000000) (50357383635 / 1000000000000))
    | 12 => (orderedInterval (-30938751552 / 1000000000000) (-30938751551 / 1000000000000), orderedInterval (-45423782595 / 1000000000000) (-45423782594 / 1000000000000))
    | 13 => (orderedInterval (4391085857 / 1000000000000) (4391085859 / 1000000000000), orderedInterval (64967133268 / 1000000000000) (64967133270 / 1000000000000))
    | 14 => (orderedInterval (59136900480 / 1000000000000) (59136900481 / 1000000000000), orderedInterval (15440545611 / 1000000000000) (15440545613 / 1000000000000))
    | 15 => (orderedInterval (-64291761455 / 1000000000000) (-64291761454 / 1000000000000), orderedInterval (-18582634146 / 1000000000000) (-18582634145 / 1000000000000))
    | 16 => (orderedInterval (32280538821 / 1000000000000) (32280538822 / 1000000000000), orderedInterval (63406686407 / 1000000000000) (63406686408 / 1000000000000))
    | 17 => (orderedInterval (13382708889 / 1000000000000) (13382708890 / 1000000000000), orderedInterval (57629928665 / 1000000000000) (57629928666 / 1000000000000))
    | 18 => (orderedInterval (54079776222 / 1000000000000) (54079776223 / 1000000000000), orderedInterval (58128684327 / 1000000000000) (58128684328 / 1000000000000))
    | 19 => (orderedInterval (-78928162810 / 1000000000000) (-78928162809 / 1000000000000), orderedInterval (-34796117500 / 1000000000000) (-34796117499 / 1000000000000))
    | 20 => (orderedInterval (-69033087051 / 1000000000000) (-69033087050 / 1000000000000), orderedInterval (-84069029861 / 1000000000000) (-84069029860 / 1000000000000))
    | 21 => (orderedInterval (-137531740361 / 1000000000000) (-137531740360 / 1000000000000), orderedInterval (-54946920497 / 1000000000000) (-54946920496 / 1000000000000))
    | 22 => (orderedInterval (-7783266330 / 1000000000000) (-7783266328 / 1000000000000), orderedInterval (-90049534372 / 1000000000000) (-90049534369 / 1000000000000))
    | 23 => (orderedInterval (19666872205 / 1000000000000) (19666872206 / 1000000000000), orderedInterval (74760067019 / 1000000000000) (74760067020 / 1000000000000))
    | 24 => (orderedInterval (117263591229 / 1000000000000) (117263591485 / 1000000000000), orderedInterval (-21644594767 / 1000000000000) (-21644594512 / 1000000000000))
    | 25 => (orderedInterval (56202391685 / 1000000000000) (56202391686 / 1000000000000), orderedInterval (17902367767 / 1000000000000) (17902367768 / 1000000000000))
    | _ => (orderedInterval (-20592527582 / 1000000000000) (-20592527581 / 1000000000000), orderedInterval (-69147344596 / 1000000000000) (-69147344595 / 1000000000000))
  chunkTarget := fun r b =>
    match r.val with
    | 0 =>
      match b.val with
      | 0 => orderedInterval (-36829644901 / 1000000000000) (-36829644854 / 1000000000000)
      | 1 => orderedInterval (6468424505 / 1000000000000) (6468424519 / 1000000000000)
      | 2 => orderedInterval (-1516527254 / 1000000000000) (-1516527110 / 1000000000000)
      | 3 => orderedInterval (-2730374201 / 1000000000000) (-2730373725 / 1000000000000)
      | 4 => orderedInterval (674506820 / 1000000000000) (674506833 / 1000000000000)
      | 5 => orderedInterval (-2247077809 / 1000000000000) (-2247077799 / 1000000000000)
      | 6 => orderedInterval (-6427007811 / 1000000000000) (-6427007785 / 1000000000000)
      | 7 => orderedInterval (1208870697 / 1000000000000) (1208870710 / 1000000000000)
      | _ => orderedInterval (-4366746 / 1000000000000) (-4366717 / 1000000000000)
    | 1 =>
      match b.val with
      | 0 => orderedInterval (2093437683 / 1000000000000) (2093437732 / 1000000000000)
      | 1 => orderedInterval (6299624961 / 1000000000000) (6299624976 / 1000000000000)
      | 2 => orderedInterval (-1185795161 / 1000000000000) (-1185794949 / 1000000000000)
      | 3 => orderedInterval (-4217117769 / 1000000000000) (-4217117078 / 1000000000000)
      | 4 => orderedInterval (11004231479 / 1000000000000) (11004231499 / 1000000000000)
      | 5 => orderedInterval (-2211077108 / 1000000000000) (-2211077094 / 1000000000000)
      | 6 => orderedInterval (-9283903807 / 1000000000000) (-9283903783 / 1000000000000)
      | 7 => orderedInterval (-4283549251 / 1000000000000) (-4283549239 / 1000000000000)
      | _ => orderedInterval (13344217234 / 1000000000000) (13344217274 / 1000000000000)
    | 2 =>
      match b.val with
      | 0 => orderedInterval (38307010289 / 1000000000000) (38307010339 / 1000000000000)
      | 1 => orderedInterval (-9660125430 / 1000000000000) (-9660125411 / 1000000000000)
      | 2 => orderedInterval (4474000987 / 1000000000000) (4474001300 / 1000000000000)
      | 3 => orderedInterval (30484392659 / 1000000000000) (30484393731 / 1000000000000)
      | 4 => orderedInterval (-2742042993 / 1000000000000) (-2742042960 / 1000000000000)
      | 5 => orderedInterval (3406113715 / 1000000000000) (3406113736 / 1000000000000)
      | 6 => orderedInterval (6443914239 / 1000000000000) (6443914261 / 1000000000000)
      | 7 => orderedInterval (1480444418 / 1000000000000) (1480444430 / 1000000000000)
      | _ => orderedInterval (9573864134 / 1000000000000) (9573864193 / 1000000000000)
    | 3 =>
      match b.val with
      | 0 => orderedInterval (-2653378911 / 1000000000000) (-2653378858 / 1000000000000)
      | 1 => orderedInterval (-11718178277 / 1000000000000) (-11718178248 / 1000000000000)
      | 2 => orderedInterval (8218896447 / 1000000000000) (8218896909 / 1000000000000)
      | 3 => orderedInterval (8032088842 / 1000000000000) (8032090624 / 1000000000000)
      | 4 => orderedInterval (-29503401965 / 1000000000000) (-29503401910 / 1000000000000)
      | 5 => orderedInterval (-1179645538 / 1000000000000) (-1179645506 / 1000000000000)
      | 6 => orderedInterval (9032548155 / 1000000000000) (9032548177 / 1000000000000)
      | 7 => orderedInterval (6196962149 / 1000000000000) (6196962160 / 1000000000000)
      | _ => orderedInterval (-15571393464 / 1000000000000) (-15571393376 / 1000000000000)
    | _ =>
      match b.val with
      | 0 => orderedInterval (-40669924496 / 1000000000000) (-40669924440 / 1000000000000)
      | 1 => orderedInterval (21596560888 / 1000000000000) (21596560932 / 1000000000000)
      | 2 => orderedInterval (-14501508304 / 1000000000000) (-14501507614 / 1000000000000)
      | 3 => orderedInterval (-182525838641 / 1000000000000) (-182525835423 / 1000000000000)
      | 4 => orderedInterval (11891537765 / 1000000000000) (11891537859 / 1000000000000)
      | 5 => orderedInterval (-4093723378 / 1000000000000) (-4093723328 / 1000000000000)
      | 6 => orderedInterval (-7317264949 / 1000000000000) (-7317264927 / 1000000000000)
      | 7 => orderedInterval (-2102299364 / 1000000000000) (-2102299351 / 1000000000000)
      | _ => orderedInterval (-45145634300 / 1000000000000) (-45145634158 / 1000000000000)
  coefficientTarget := fun i =>
    match i.val with
    | 0 => orderedInterval (-41403196700 / 1000000000000) (-41403195928 / 1000000000000)
    | 1 => orderedInterval (11560068261 / 1000000000000) (11560069338 / 1000000000000)
    | 2 => orderedInterval (81767572018 / 1000000000000) (81767573619 / 1000000000000)
    | 3 => orderedInterval (-29145502562 / 1000000000000) (-29145500028 / 1000000000000)
    | _ => orderedInterval (-262868094779 / 1000000000000) (-262868090450 / 1000000000000)

theorem compactCertificate218_stateChecks0 :
    compactCertificate218.stateChecks 0 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 31 12 (393 / 4)) (orderedInterval (-80275340709 / 1000000000000) (-80275340614 / 1000000000000), orderedInterval (6356394281 / 1000000000000) (6356394376 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 23 12 (578964042525093 / 8000000000000)) (orderedInterval (-73324489281 / 1000000000000) (-73324489280 / 1000000000000), orderedInterval (-57975456125 / 1000000000000) (-57975456124 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 37 12 (187225075785669 / 1600000000000)) (orderedInterval (-73755691321 / 1000000000000) (-73755691289 / 1000000000000), orderedInterval (-401947418 / 1000000000000) (-401947386 / 1000000000000))) = true
  norm_num [besselStateAtRationalPoint, besselIntervalStepZero,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, besselZeroTransition,
    besselInitial, besselGridStateAt, besselGridStateBlock00, besselGridStateBlock01,
    besselGridStateBlock02, besselGridStateBlock03, besselGridStateBlock04,
    besselGridStateBlock05, besselGridStateBlock06, besselGridStateBlock07,
    besselGridStateBlock08, besselGridStateBlock09, besselGridStateBlock10,
    besselGridStateBlock11, besselGridStateBlock12, besselGridStateBlock13,
    besselGridStateBlock14, besselGridState007, besselGridState009, besselGridState014, besselGridState017, besselGridState018, besselGridState023, besselGridState025, besselGridState027, besselGridState031, besselGridState032, besselGridState034, besselGridState036, besselGridState037, besselGridState039, besselGridState040, besselGridState045, besselGridState046, besselGridState048, besselGridState049, besselGridState054, besselGridState058, besselGridState062, besselGridState067, besselGridState070, besselGridState072, besselStateSubset, linearInterval, widenInterval,
    rationalErrorInterval, rationalIntervalSubset, orderedInterval, Finset.sum_range_succ,
    IntervalRat.add, IntervalRat.mul, IntervalRat.scale, IntervalRat.singleton]

theorem compactCertificate218_stateChecks1 :
    compactCertificate218.stateChecks 3 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 7 12 (168940263651951 / 8000000000000)) (orderedInterval (16317124587 / 1000000000000) (16317124634 / 1000000000000), orderedInterval (-173269110906 / 1000000000000) (-173269110858 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 18 12 (453797311582947 / 8000000000000)) (orderedInterval (86733120397 / 1000000000000) (86733120398 / 1000000000000), orderedInterval (60064797944 / 1000000000000) (60064797945 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 49 12 (1232147977096599 / 8000000000000)) (orderedInterval (-48933656641 / 1000000000000) (-48933656640 / 1000000000000), orderedInterval (-41541168643 / 1000000000000) (-41541168642 / 1000000000000))) = true
  norm_num [besselStateAtRationalPoint, besselIntervalStepZero,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, besselZeroTransition,
    besselInitial, besselGridStateAt, besselGridStateBlock00, besselGridStateBlock01,
    besselGridStateBlock02, besselGridStateBlock03, besselGridStateBlock04,
    besselGridStateBlock05, besselGridStateBlock06, besselGridStateBlock07,
    besselGridStateBlock08, besselGridStateBlock09, besselGridStateBlock10,
    besselGridStateBlock11, besselGridStateBlock12, besselGridStateBlock13,
    besselGridStateBlock14, besselGridState007, besselGridState009, besselGridState014, besselGridState017, besselGridState018, besselGridState023, besselGridState025, besselGridState027, besselGridState031, besselGridState032, besselGridState034, besselGridState036, besselGridState037, besselGridState039, besselGridState040, besselGridState045, besselGridState046, besselGridState048, besselGridState049, besselGridState054, besselGridState058, besselGridState062, besselGridState067, besselGridState070, besselGridState072, besselStateSubset, linearInterval, widenInterval,
    rationalErrorInterval, rationalIntervalSubset, orderedInterval, Finset.sum_range_succ,
    IntervalRat.add, IntervalRat.mul, IntervalRat.scale, IntervalRat.singleton]

theorem compactCertificate218_stateChecks2 :
    compactCertificate218.stateChecks 6 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 36 12 (907594623166287 / 8000000000000)) (orderedInterval (67948732401 / 1000000000000) (67948732402 / 1000000000000), orderedInterval (31235037324 / 1000000000000) (31235037325 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 62 12 (1555178856250251 / 8000000000000)) (orderedInterval (22462272615 / 1000000000000) (22462272616 / 1000000000000), orderedInterval (52575783940 / 1000000000000) (52575783941 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 46 12 (1145537706696609 / 8000000000000)) (orderedInterval (-34082256363 / 1000000000000) (-34082250653 / 1000000000000), orderedInterval (57428021757 / 1000000000000) (57428027467 / 1000000000000))) = true
  norm_num [besselStateAtRationalPoint, besselIntervalStepZero,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, besselZeroTransition,
    besselInitial, besselGridStateAt, besselGridStateBlock00, besselGridStateBlock01,
    besselGridStateBlock02, besselGridStateBlock03, besselGridStateBlock04,
    besselGridStateBlock05, besselGridStateBlock06, besselGridStateBlock07,
    besselGridStateBlock08, besselGridStateBlock09, besselGridStateBlock10,
    besselGridStateBlock11, besselGridStateBlock12, besselGridStateBlock13,
    besselGridStateBlock14, besselGridState007, besselGridState009, besselGridState014, besselGridState017, besselGridState018, besselGridState023, besselGridState025, besselGridState027, besselGridState031, besselGridState032, besselGridState034, besselGridState036, besselGridState037, besselGridState039, besselGridState040, besselGridState045, besselGridState046, besselGridState048, besselGridState049, besselGridState054, besselGridState058, besselGridState062, besselGridState067, besselGridState070, besselGridState072, besselStateSubset, linearInterval, widenInterval,
    rationalErrorInterval, rationalIntervalSubset, orderedInterval, Finset.sum_range_succ,
    IntervalRat.add, IntervalRat.mul, IntervalRat.scale, IntervalRat.singleton]

theorem compactCertificate218_stateChecks3 :
    compactCertificate218.stateChecks 9 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 70 12 (1757549430314607 / 8000000000000)) (orderedInterval (28913735624 / 1000000000000) (28913735625 / 1000000000000), orderedInterval (45340803764 / 1000000000000) (45340803765 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 40 12 (1014721636706103 / 8000000000000)) (orderedInterval (65522192563 / 1000000000000) (65522197839 / 1000000000000), orderedInterval (-27200509556 / 1000000000000) (-27200504280 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 72 12 (1800641350998627 / 8000000000000)) (orderedInterval (-17216365199 / 1000000000000) (-17216364878 / 1000000000000), orderedInterval (50357383313 / 1000000000000) (50357383635 / 1000000000000))) = true
  norm_num [besselStateAtRationalPoint, besselIntervalStepZero,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, besselZeroTransition,
    besselInitial, besselGridStateAt, besselGridStateBlock00, besselGridStateBlock01,
    besselGridStateBlock02, besselGridStateBlock03, besselGridStateBlock04,
    besselGridStateBlock05, besselGridStateBlock06, besselGridStateBlock07,
    besselGridStateBlock08, besselGridStateBlock09, besselGridStateBlock10,
    besselGridStateBlock11, besselGridStateBlock12, besselGridStateBlock13,
    besselGridStateBlock14, besselGridState007, besselGridState009, besselGridState014, besselGridState017, besselGridState018, besselGridState023, besselGridState025, besselGridState027, besselGridState031, besselGridState032, besselGridState034, besselGridState036, besselGridState037, besselGridState039, besselGridState040, besselGridState045, besselGridState046, besselGridState048, besselGridState049, besselGridState054, besselGridState058, besselGridState062, besselGridState067, besselGridState070, besselGridState072, besselStateSubset, linearInterval, widenInterval,
    rationalErrorInterval, rationalIntervalSubset, orderedInterval, Finset.sum_range_succ,
    IntervalRat.add, IntervalRat.mul, IntervalRat.scale, IntervalRat.singleton]

theorem compactCertificate218_stateChecks4 :
    compactCertificate218.stateChecks 12 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 67 12 (1682392723155663 / 8000000000000)) (orderedInterval (-30938751552 / 1000000000000) (-30938751551 / 1000000000000), orderedInterval (-45423782595 / 1000000000000) (-45423782594 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 48 12 (1200634832078079 / 8000000000000)) (orderedInterval (4391085857 / 1000000000000) (4391085859 / 1000000000000), orderedInterval (64967133268 / 1000000000000) (64967133270 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 54 12 (1361391934748841 / 8000000000000)) (orderedInterval (59136900480 / 1000000000000) (59136900481 / 1000000000000), orderedInterval (15440545611 / 1000000000000) (15440545613 / 1000000000000))) = true
  norm_num [besselStateAtRationalPoint, besselIntervalStepZero,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, besselZeroTransition,
    besselInitial, besselGridStateAt, besselGridStateBlock00, besselGridStateBlock01,
    besselGridStateBlock02, besselGridStateBlock03, besselGridStateBlock04,
    besselGridStateBlock05, besselGridStateBlock06, besselGridStateBlock07,
    besselGridStateBlock08, besselGridStateBlock09, besselGridStateBlock10,
    besselGridStateBlock11, besselGridStateBlock12, besselGridStateBlock13,
    besselGridStateBlock14, besselGridState007, besselGridState009, besselGridState014, besselGridState017, besselGridState018, besselGridState023, besselGridState025, besselGridState027, besselGridState031, besselGridState032, besselGridState034, besselGridState036, besselGridState037, besselGridState039, besselGridState040, besselGridState045, besselGridState046, besselGridState048, besselGridState049, besselGridState054, besselGridState058, besselGridState062, besselGridState067, besselGridState070, besselGridState072, besselStateSubset, linearInterval, widenInterval,
    rationalErrorInterval, rationalIntervalSubset, orderedInterval, Finset.sum_range_succ,
    IntervalRat.add, IntervalRat.mul, IntervalRat.scale, IntervalRat.singleton]

theorem compactCertificate218_stateChecks5 :
    compactCertificate218.stateChecks 15 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 45 12 (1134986662949529 / 8000000000000)) (orderedInterval (-64291761455 / 1000000000000) (-64291761454 / 1000000000000), orderedInterval (-18582634146 / 1000000000000) (-18582634145 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 40 12 (1002795137408109 / 8000000000000)) (orderedInterval (32280538821 / 1000000000000) (32280538822 / 1000000000000), orderedInterval (63406686407 / 1000000000000) (63406686408 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 58 12 (290649116638791 / 1600000000000)) (orderedInterval (13382708889 / 1000000000000) (13382708890 / 1000000000000), orderedInterval (57629928665 / 1000000000000) (57629928666 / 1000000000000))) = true
  norm_num [besselStateAtRationalPoint, besselIntervalStepZero,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, besselZeroTransition,
    besselInitial, besselGridStateAt, besselGridStateBlock00, besselGridStateBlock01,
    besselGridStateBlock02, besselGridStateBlock03, besselGridStateBlock04,
    besselGridStateBlock05, besselGridStateBlock06, besselGridStateBlock07,
    besselGridStateBlock08, besselGridStateBlock09, besselGridStateBlock10,
    besselGridStateBlock11, besselGridStateBlock12, besselGridStateBlock13,
    besselGridStateBlock14, besselGridState007, besselGridState009, besselGridState014, besselGridState017, besselGridState018, besselGridState023, besselGridState025, besselGridState027, besselGridState031, besselGridState032, besselGridState034, besselGridState036, besselGridState037, besselGridState039, besselGridState040, besselGridState045, besselGridState046, besselGridState048, besselGridState049, besselGridState054, besselGridState058, besselGridState062, besselGridState067, besselGridState070, besselGridState072, besselStateSubset, linearInterval, widenInterval,
    rationalErrorInterval, rationalIntervalSubset, orderedInterval, Finset.sum_range_succ,
    IntervalRat.add, IntervalRat.mul, IntervalRat.scale, IntervalRat.singleton]

theorem compactCertificate218_stateChecks6 :
    compactCertificate218.stateChecks 18 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 32 12 (803950752647877 / 8000000000000)) (orderedInterval (54079776222 / 1000000000000) (54079776223 / 1000000000000), orderedInterval (58128684327 / 1000000000000) (58128684328 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 27 12 (681517956530397 / 8000000000000)) (orderedInterval (-78928162810 / 1000000000000) (-78928162809 / 1000000000000), orderedInterval (-34796117500 / 1000000000000) (-34796117499 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 17 12 (426462293303391 / 8000000000000)) (orderedInterval (-69033087051 / 1000000000000) (-69033087050 / 1000000000000), orderedInterval (-84069029861 / 1000000000000) (-84069029860 / 1000000000000))) = true
  norm_num [besselStateAtRationalPoint, besselIntervalStepZero,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, besselZeroTransition,
    besselInitial, besselGridStateAt, besselGridStateBlock00, besselGridStateBlock01,
    besselGridStateBlock02, besselGridStateBlock03, besselGridStateBlock04,
    besselGridStateBlock05, besselGridStateBlock06, besselGridStateBlock07,
    besselGridStateBlock08, besselGridStateBlock09, besselGridStateBlock10,
    besselGridStateBlock11, besselGridStateBlock12, besselGridStateBlock13,
    besselGridStateBlock14, besselGridState007, besselGridState009, besselGridState014, besselGridState017, besselGridState018, besselGridState023, besselGridState025, besselGridState027, besselGridState031, besselGridState032, besselGridState034, besselGridState036, besselGridState037, besselGridState039, besselGridState040, besselGridState045, besselGridState046, besselGridState048, besselGridState049, besselGridState054, besselGridState058, besselGridState062, besselGridState067, besselGridState070, besselGridState072, besselStateSubset, linearInterval, widenInterval,
    rationalErrorInterval, rationalIntervalSubset, orderedInterval, Finset.sum_range_succ,
    IntervalRat.add, IntervalRat.mul, IntervalRat.scale, IntervalRat.singleton]

theorem compactCertificate218_stateChecks7 :
    compactCertificate218.stateChecks 21 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 9 12 (229352839688097 / 8000000000000)) (orderedInterval (-137531740361 / 1000000000000) (-137531740360 / 1000000000000), orderedInterval (-54946920497 / 1000000000000) (-54946920496 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 25 12 (622737575235291 / 8000000000000)) (orderedInterval (-7783266330 / 1000000000000) (-7783266328 / 1000000000000), orderedInterval (-90049534372 / 1000000000000) (-90049534369 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 34 12 (850294919510907 / 8000000000000)) (orderedInterval (19666872205 / 1000000000000) (19666872206 / 1000000000000), orderedInterval (74760067019 / 1000000000000) (74760067020 / 1000000000000))) = true
  norm_num [besselStateAtRationalPoint, besselIntervalStepZero,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, besselZeroTransition,
    besselInitial, besselGridStateAt, besselGridStateBlock00, besselGridStateBlock01,
    besselGridStateBlock02, besselGridStateBlock03, besselGridStateBlock04,
    besselGridStateBlock05, besselGridStateBlock06, besselGridStateBlock07,
    besselGridStateBlock08, besselGridStateBlock09, besselGridStateBlock10,
    besselGridStateBlock11, besselGridStateBlock12, besselGridStateBlock13,
    besselGridStateBlock14, besselGridState007, besselGridState009, besselGridState014, besselGridState017, besselGridState018, besselGridState023, besselGridState025, besselGridState027, besselGridState031, besselGridState032, besselGridState034, besselGridState036, besselGridState037, besselGridState039, besselGridState040, besselGridState045, besselGridState046, besselGridState048, besselGridState049, besselGridState054, besselGridState058, besselGridState062, besselGridState067, besselGridState070, besselGridState072, besselStateSubset, linearInterval, widenInterval,
    rationalErrorInterval, rationalIntervalSubset, orderedInterval, Finset.sum_range_succ,
    IntervalRat.add, IntervalRat.mul, IntervalRat.scale, IntervalRat.singleton]

theorem compactCertificate218_stateChecks8 :
    compactCertificate218.stateChecks 24 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 14 12 (359537706696609 / 8000000000000)) (orderedInterval (117263591229 / 1000000000000) (117263591485 / 1000000000000), orderedInterval (-21644594767 / 1000000000000) (-21644594512 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 58 12 (1461500816785089 / 8000000000000)) (orderedInterval (56202391685 / 1000000000000) (56202391686 / 1000000000000), orderedInterval (17902367767 / 1000000000000) (17902367768 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 39 12 (976214813725551 / 8000000000000)) (orderedInterval (-20592527582 / 1000000000000) (-20592527581 / 1000000000000), orderedInterval (-69147344596 / 1000000000000) (-69147344595 / 1000000000000))) = true
  norm_num [besselStateAtRationalPoint, besselIntervalStepZero,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, besselZeroTransition,
    besselInitial, besselGridStateAt, besselGridStateBlock00, besselGridStateBlock01,
    besselGridStateBlock02, besselGridStateBlock03, besselGridStateBlock04,
    besselGridStateBlock05, besselGridStateBlock06, besselGridStateBlock07,
    besselGridStateBlock08, besselGridStateBlock09, besselGridStateBlock10,
    besselGridStateBlock11, besselGridStateBlock12, besselGridStateBlock13,
    besselGridStateBlock14, besselGridState007, besselGridState009, besselGridState014, besselGridState017, besselGridState018, besselGridState023, besselGridState025, besselGridState027, besselGridState031, besselGridState032, besselGridState034, besselGridState036, besselGridState037, besselGridState039, besselGridState040, besselGridState045, besselGridState046, besselGridState048, besselGridState049, besselGridState054, besselGridState058, besselGridState062, besselGridState067, besselGridState070, besselGridState072, besselStateSubset, linearInterval, widenInterval,
    rationalErrorInterval, rationalIntervalSubset, orderedInterval, Finset.sum_range_succ,
    IntervalRat.add, IntervalRat.mul, IntervalRat.scale, IntervalRat.singleton]

theorem compactCertificate218_states : ∀ j,
    BesselStateValid (compactCertificate218.point j) (compactCertificate218.state j) :=
  compactCertificate218.statesValid_of_checks3 compactCertificate218_stateChecks0
    compactCertificate218_stateChecks1 compactCertificate218_stateChecks2
    compactCertificate218_stateChecks3 compactCertificate218_stateChecks4
    compactCertificate218_stateChecks5 compactCertificate218_stateChecks6
    compactCertificate218_stateChecks7 compactCertificate218_stateChecks8

theorem compactCertificate218_chunkChecks0_0 :
    compactCertificate218.chunkChecks (0 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 0) <| besselDerivativeNearFromState (393 / 4) 0 (IntervalRat.scale (393 / 4) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-80275340709 / 1000000000000) (-80275340614 / 1000000000000), orderedInterval (6356394281 / 1000000000000) (6356394376 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 0) <| besselDerivativeNearFromState (578964042525093 / 8000000000000) 0 (IntervalRat.scale (393 / 4) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-73324489281 / 1000000000000) (-73324489280 / 1000000000000), orderedInterval (-57975456125 / 1000000000000) (-57975456124 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 0) <| besselDerivativeNearFromState (187225075785669 / 1600000000000) 0 (IntervalRat.scale (393 / 4) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-73755691321 / 1000000000000) (-73755691289 / 1000000000000), orderedInterval (-401947418 / 1000000000000) (-401947386 / 1000000000000)))) (orderedInterval (-36829644901 / 1000000000000) (-36829644854 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 0) <| besselDerivativeNearFromState (168940263651951 / 8000000000000) 0 (IntervalRat.scale (393 / 4) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (16317124587 / 1000000000000) (16317124634 / 1000000000000), orderedInterval (-173269110906 / 1000000000000) (-173269110858 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 0) <| besselDerivativeNearFromState (453797311582947 / 8000000000000) 0 (IntervalRat.scale (393 / 4) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (86733120397 / 1000000000000) (86733120398 / 1000000000000), orderedInterval (60064797944 / 1000000000000) (60064797945 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 0) <| besselDerivativeNearFromState (1232147977096599 / 8000000000000) 0 (IntervalRat.scale (393 / 4) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-48933656641 / 1000000000000) (-48933656640 / 1000000000000), orderedInterval (-41541168643 / 1000000000000) (-41541168642 / 1000000000000)))) (orderedInterval (6468424505 / 1000000000000) (6468424519 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 0) <| besselDerivativeNearFromState (907594623166287 / 8000000000000) 0 (IntervalRat.scale (393 / 4) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (67948732401 / 1000000000000) (67948732402 / 1000000000000), orderedInterval (31235037324 / 1000000000000) (31235037325 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 0) <| besselDerivativeNearFromState (1555178856250251 / 8000000000000) 0 (IntervalRat.scale (393 / 4) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (22462272615 / 1000000000000) (22462272616 / 1000000000000), orderedInterval (52575783940 / 1000000000000) (52575783941 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 0) <| besselDerivativeNearFromState (1145537706696609 / 8000000000000) 0 (IntervalRat.scale (393 / 4) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-34082256363 / 1000000000000) (-34082250653 / 1000000000000), orderedInterval (57428021757 / 1000000000000) (57428027467 / 1000000000000)))) (orderedInterval (-1516527254 / 1000000000000) (-1516527110 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate218_chunkChecks0_1 :
    compactCertificate218.chunkChecks (0 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 0) <| besselDerivativeNearFromState (1757549430314607 / 8000000000000) 0 (IntervalRat.scale (393 / 4) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (28913735624 / 1000000000000) (28913735625 / 1000000000000), orderedInterval (45340803764 / 1000000000000) (45340803765 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 0) <| besselDerivativeNearFromState (1014721636706103 / 8000000000000) 0 (IntervalRat.scale (393 / 4) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (65522192563 / 1000000000000) (65522197839 / 1000000000000), orderedInterval (-27200509556 / 1000000000000) (-27200504280 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 0) <| besselDerivativeNearFromState (1800641350998627 / 8000000000000) 0 (IntervalRat.scale (393 / 4) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-17216365199 / 1000000000000) (-17216364878 / 1000000000000), orderedInterval (50357383313 / 1000000000000) (50357383635 / 1000000000000)))) (orderedInterval (-2730374201 / 1000000000000) (-2730373725 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 0) <| besselDerivativeNearFromState (1682392723155663 / 8000000000000) 0 (IntervalRat.scale (393 / 4) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-30938751552 / 1000000000000) (-30938751551 / 1000000000000), orderedInterval (-45423782595 / 1000000000000) (-45423782594 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 0) <| besselDerivativeNearFromState (1200634832078079 / 8000000000000) 0 (IntervalRat.scale (393 / 4) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (4391085857 / 1000000000000) (4391085859 / 1000000000000), orderedInterval (64967133268 / 1000000000000) (64967133270 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 0) <| besselDerivativeNearFromState (1361391934748841 / 8000000000000) 0 (IntervalRat.scale (393 / 4) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (59136900480 / 1000000000000) (59136900481 / 1000000000000), orderedInterval (15440545611 / 1000000000000) (15440545613 / 1000000000000)))) (orderedInterval (674506820 / 1000000000000) (674506833 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 0) <| besselDerivativeNearFromState (1134986662949529 / 8000000000000) 0 (IntervalRat.scale (393 / 4) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-64291761455 / 1000000000000) (-64291761454 / 1000000000000), orderedInterval (-18582634146 / 1000000000000) (-18582634145 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 0) <| besselDerivativeNearFromState (1002795137408109 / 8000000000000) 0 (IntervalRat.scale (393 / 4) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (32280538821 / 1000000000000) (32280538822 / 1000000000000), orderedInterval (63406686407 / 1000000000000) (63406686408 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 0) <| besselDerivativeNearFromState (290649116638791 / 1600000000000) 0 (IntervalRat.scale (393 / 4) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (13382708889 / 1000000000000) (13382708890 / 1000000000000), orderedInterval (57629928665 / 1000000000000) (57629928666 / 1000000000000)))) (orderedInterval (-2247077809 / 1000000000000) (-2247077799 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate218_chunkChecks0_2 :
    compactCertificate218.chunkChecks (0 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 0) <| besselDerivativeNearFromState (803950752647877 / 8000000000000) 0 (IntervalRat.scale (393 / 4) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (54079776222 / 1000000000000) (54079776223 / 1000000000000), orderedInterval (58128684327 / 1000000000000) (58128684328 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 0) <| besselDerivativeNearFromState (681517956530397 / 8000000000000) 0 (IntervalRat.scale (393 / 4) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-78928162810 / 1000000000000) (-78928162809 / 1000000000000), orderedInterval (-34796117500 / 1000000000000) (-34796117499 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 0) <| besselDerivativeNearFromState (426462293303391 / 8000000000000) 0 (IntervalRat.scale (393 / 4) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-69033087051 / 1000000000000) (-69033087050 / 1000000000000), orderedInterval (-84069029861 / 1000000000000) (-84069029860 / 1000000000000)))) (orderedInterval (-6427007811 / 1000000000000) (-6427007785 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 0) <| besselDerivativeNearFromState (229352839688097 / 8000000000000) 0 (IntervalRat.scale (393 / 4) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-137531740361 / 1000000000000) (-137531740360 / 1000000000000), orderedInterval (-54946920497 / 1000000000000) (-54946920496 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 0) <| besselDerivativeNearFromState (622737575235291 / 8000000000000) 0 (IntervalRat.scale (393 / 4) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-7783266330 / 1000000000000) (-7783266328 / 1000000000000), orderedInterval (-90049534372 / 1000000000000) (-90049534369 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 0) <| besselDerivativeNearFromState (850294919510907 / 8000000000000) 0 (IntervalRat.scale (393 / 4) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (19666872205 / 1000000000000) (19666872206 / 1000000000000), orderedInterval (74760067019 / 1000000000000) (74760067020 / 1000000000000)))) (orderedInterval (1208870697 / 1000000000000) (1208870710 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 0) <| besselDerivativeNearFromState (359537706696609 / 8000000000000) 0 (IntervalRat.scale (393 / 4) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (117263591229 / 1000000000000) (117263591485 / 1000000000000), orderedInterval (-21644594767 / 1000000000000) (-21644594512 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 0) <| besselDerivativeNearFromState (1461500816785089 / 8000000000000) 0 (IntervalRat.scale (393 / 4) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (56202391685 / 1000000000000) (56202391686 / 1000000000000), orderedInterval (17902367767 / 1000000000000) (17902367768 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 0) <| besselDerivativeNearFromState (976214813725551 / 8000000000000) 0 (IntervalRat.scale (393 / 4) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-20592527582 / 1000000000000) (-20592527581 / 1000000000000), orderedInterval (-69147344596 / 1000000000000) (-69147344595 / 1000000000000)))) (orderedInterval (-4366746 / 1000000000000) (-4366717 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate218_chunkChecks0 :
    compactCertificate218.chunkChecks (0 : Fin 5) 0 9 = true :=
  compactCertificate218.chunkChecks_nine_of_three (0 : Fin 5) compactCertificate218_chunkChecks0_0
    compactCertificate218_chunkChecks0_1 compactCertificate218_chunkChecks0_2

theorem compactCertificate218_chunkChecks1_0 :
    compactCertificate218.chunkChecks (1 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 1) <| besselDerivativeNearFromState (393 / 4) 1 (IntervalRat.scale (393 / 4) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-80275340709 / 1000000000000) (-80275340614 / 1000000000000), orderedInterval (6356394281 / 1000000000000) (6356394376 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 1) <| besselDerivativeNearFromState (578964042525093 / 8000000000000) 1 (IntervalRat.scale (393 / 4) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-73324489281 / 1000000000000) (-73324489280 / 1000000000000), orderedInterval (-57975456125 / 1000000000000) (-57975456124 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 1) <| besselDerivativeNearFromState (187225075785669 / 1600000000000) 1 (IntervalRat.scale (393 / 4) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-73755691321 / 1000000000000) (-73755691289 / 1000000000000), orderedInterval (-401947418 / 1000000000000) (-401947386 / 1000000000000)))) (orderedInterval (2093437683 / 1000000000000) (2093437732 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 1) <| besselDerivativeNearFromState (168940263651951 / 8000000000000) 1 (IntervalRat.scale (393 / 4) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (16317124587 / 1000000000000) (16317124634 / 1000000000000), orderedInterval (-173269110906 / 1000000000000) (-173269110858 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 1) <| besselDerivativeNearFromState (453797311582947 / 8000000000000) 1 (IntervalRat.scale (393 / 4) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (86733120397 / 1000000000000) (86733120398 / 1000000000000), orderedInterval (60064797944 / 1000000000000) (60064797945 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 1) <| besselDerivativeNearFromState (1232147977096599 / 8000000000000) 1 (IntervalRat.scale (393 / 4) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-48933656641 / 1000000000000) (-48933656640 / 1000000000000), orderedInterval (-41541168643 / 1000000000000) (-41541168642 / 1000000000000)))) (orderedInterval (6299624961 / 1000000000000) (6299624976 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 1) <| besselDerivativeNearFromState (907594623166287 / 8000000000000) 1 (IntervalRat.scale (393 / 4) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (67948732401 / 1000000000000) (67948732402 / 1000000000000), orderedInterval (31235037324 / 1000000000000) (31235037325 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 1) <| besselDerivativeNearFromState (1555178856250251 / 8000000000000) 1 (IntervalRat.scale (393 / 4) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (22462272615 / 1000000000000) (22462272616 / 1000000000000), orderedInterval (52575783940 / 1000000000000) (52575783941 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 1) <| besselDerivativeNearFromState (1145537706696609 / 8000000000000) 1 (IntervalRat.scale (393 / 4) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-34082256363 / 1000000000000) (-34082250653 / 1000000000000), orderedInterval (57428021757 / 1000000000000) (57428027467 / 1000000000000)))) (orderedInterval (-1185795161 / 1000000000000) (-1185794949 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate218_chunkChecks1_1 :
    compactCertificate218.chunkChecks (1 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 1) <| besselDerivativeNearFromState (1757549430314607 / 8000000000000) 1 (IntervalRat.scale (393 / 4) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (28913735624 / 1000000000000) (28913735625 / 1000000000000), orderedInterval (45340803764 / 1000000000000) (45340803765 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 1) <| besselDerivativeNearFromState (1014721636706103 / 8000000000000) 1 (IntervalRat.scale (393 / 4) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (65522192563 / 1000000000000) (65522197839 / 1000000000000), orderedInterval (-27200509556 / 1000000000000) (-27200504280 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 1) <| besselDerivativeNearFromState (1800641350998627 / 8000000000000) 1 (IntervalRat.scale (393 / 4) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-17216365199 / 1000000000000) (-17216364878 / 1000000000000), orderedInterval (50357383313 / 1000000000000) (50357383635 / 1000000000000)))) (orderedInterval (-4217117769 / 1000000000000) (-4217117078 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 1) <| besselDerivativeNearFromState (1682392723155663 / 8000000000000) 1 (IntervalRat.scale (393 / 4) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-30938751552 / 1000000000000) (-30938751551 / 1000000000000), orderedInterval (-45423782595 / 1000000000000) (-45423782594 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 1) <| besselDerivativeNearFromState (1200634832078079 / 8000000000000) 1 (IntervalRat.scale (393 / 4) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (4391085857 / 1000000000000) (4391085859 / 1000000000000), orderedInterval (64967133268 / 1000000000000) (64967133270 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 1) <| besselDerivativeNearFromState (1361391934748841 / 8000000000000) 1 (IntervalRat.scale (393 / 4) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (59136900480 / 1000000000000) (59136900481 / 1000000000000), orderedInterval (15440545611 / 1000000000000) (15440545613 / 1000000000000)))) (orderedInterval (11004231479 / 1000000000000) (11004231499 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 1) <| besselDerivativeNearFromState (1134986662949529 / 8000000000000) 1 (IntervalRat.scale (393 / 4) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-64291761455 / 1000000000000) (-64291761454 / 1000000000000), orderedInterval (-18582634146 / 1000000000000) (-18582634145 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 1) <| besselDerivativeNearFromState (1002795137408109 / 8000000000000) 1 (IntervalRat.scale (393 / 4) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (32280538821 / 1000000000000) (32280538822 / 1000000000000), orderedInterval (63406686407 / 1000000000000) (63406686408 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 1) <| besselDerivativeNearFromState (290649116638791 / 1600000000000) 1 (IntervalRat.scale (393 / 4) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (13382708889 / 1000000000000) (13382708890 / 1000000000000), orderedInterval (57629928665 / 1000000000000) (57629928666 / 1000000000000)))) (orderedInterval (-2211077108 / 1000000000000) (-2211077094 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate218_chunkChecks1_2 :
    compactCertificate218.chunkChecks (1 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 1) <| besselDerivativeNearFromState (803950752647877 / 8000000000000) 1 (IntervalRat.scale (393 / 4) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (54079776222 / 1000000000000) (54079776223 / 1000000000000), orderedInterval (58128684327 / 1000000000000) (58128684328 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 1) <| besselDerivativeNearFromState (681517956530397 / 8000000000000) 1 (IntervalRat.scale (393 / 4) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-78928162810 / 1000000000000) (-78928162809 / 1000000000000), orderedInterval (-34796117500 / 1000000000000) (-34796117499 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 1) <| besselDerivativeNearFromState (426462293303391 / 8000000000000) 1 (IntervalRat.scale (393 / 4) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-69033087051 / 1000000000000) (-69033087050 / 1000000000000), orderedInterval (-84069029861 / 1000000000000) (-84069029860 / 1000000000000)))) (orderedInterval (-9283903807 / 1000000000000) (-9283903783 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 1) <| besselDerivativeNearFromState (229352839688097 / 8000000000000) 1 (IntervalRat.scale (393 / 4) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-137531740361 / 1000000000000) (-137531740360 / 1000000000000), orderedInterval (-54946920497 / 1000000000000) (-54946920496 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 1) <| besselDerivativeNearFromState (622737575235291 / 8000000000000) 1 (IntervalRat.scale (393 / 4) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-7783266330 / 1000000000000) (-7783266328 / 1000000000000), orderedInterval (-90049534372 / 1000000000000) (-90049534369 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 1) <| besselDerivativeNearFromState (850294919510907 / 8000000000000) 1 (IntervalRat.scale (393 / 4) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (19666872205 / 1000000000000) (19666872206 / 1000000000000), orderedInterval (74760067019 / 1000000000000) (74760067020 / 1000000000000)))) (orderedInterval (-4283549251 / 1000000000000) (-4283549239 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 1) <| besselDerivativeNearFromState (359537706696609 / 8000000000000) 1 (IntervalRat.scale (393 / 4) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (117263591229 / 1000000000000) (117263591485 / 1000000000000), orderedInterval (-21644594767 / 1000000000000) (-21644594512 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 1) <| besselDerivativeNearFromState (1461500816785089 / 8000000000000) 1 (IntervalRat.scale (393 / 4) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (56202391685 / 1000000000000) (56202391686 / 1000000000000), orderedInterval (17902367767 / 1000000000000) (17902367768 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 1) <| besselDerivativeNearFromState (976214813725551 / 8000000000000) 1 (IntervalRat.scale (393 / 4) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-20592527582 / 1000000000000) (-20592527581 / 1000000000000), orderedInterval (-69147344596 / 1000000000000) (-69147344595 / 1000000000000)))) (orderedInterval (13344217234 / 1000000000000) (13344217274 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate218_chunkChecks1 :
    compactCertificate218.chunkChecks (1 : Fin 5) 0 9 = true :=
  compactCertificate218.chunkChecks_nine_of_three (1 : Fin 5) compactCertificate218_chunkChecks1_0
    compactCertificate218_chunkChecks1_1 compactCertificate218_chunkChecks1_2

theorem compactCertificate218_chunkChecks2_0 :
    compactCertificate218.chunkChecks (2 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 2) <| besselDerivativeNearFromState (393 / 4) 2 (IntervalRat.scale (393 / 4) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-80275340709 / 1000000000000) (-80275340614 / 1000000000000), orderedInterval (6356394281 / 1000000000000) (6356394376 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 2) <| besselDerivativeNearFromState (578964042525093 / 8000000000000) 2 (IntervalRat.scale (393 / 4) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-73324489281 / 1000000000000) (-73324489280 / 1000000000000), orderedInterval (-57975456125 / 1000000000000) (-57975456124 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 2) <| besselDerivativeNearFromState (187225075785669 / 1600000000000) 2 (IntervalRat.scale (393 / 4) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-73755691321 / 1000000000000) (-73755691289 / 1000000000000), orderedInterval (-401947418 / 1000000000000) (-401947386 / 1000000000000)))) (orderedInterval (38307010289 / 1000000000000) (38307010339 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 2) <| besselDerivativeNearFromState (168940263651951 / 8000000000000) 2 (IntervalRat.scale (393 / 4) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (16317124587 / 1000000000000) (16317124634 / 1000000000000), orderedInterval (-173269110906 / 1000000000000) (-173269110858 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 2) <| besselDerivativeNearFromState (453797311582947 / 8000000000000) 2 (IntervalRat.scale (393 / 4) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (86733120397 / 1000000000000) (86733120398 / 1000000000000), orderedInterval (60064797944 / 1000000000000) (60064797945 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 2) <| besselDerivativeNearFromState (1232147977096599 / 8000000000000) 2 (IntervalRat.scale (393 / 4) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-48933656641 / 1000000000000) (-48933656640 / 1000000000000), orderedInterval (-41541168643 / 1000000000000) (-41541168642 / 1000000000000)))) (orderedInterval (-9660125430 / 1000000000000) (-9660125411 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 2) <| besselDerivativeNearFromState (907594623166287 / 8000000000000) 2 (IntervalRat.scale (393 / 4) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (67948732401 / 1000000000000) (67948732402 / 1000000000000), orderedInterval (31235037324 / 1000000000000) (31235037325 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 2) <| besselDerivativeNearFromState (1555178856250251 / 8000000000000) 2 (IntervalRat.scale (393 / 4) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (22462272615 / 1000000000000) (22462272616 / 1000000000000), orderedInterval (52575783940 / 1000000000000) (52575783941 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 2) <| besselDerivativeNearFromState (1145537706696609 / 8000000000000) 2 (IntervalRat.scale (393 / 4) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-34082256363 / 1000000000000) (-34082250653 / 1000000000000), orderedInterval (57428021757 / 1000000000000) (57428027467 / 1000000000000)))) (orderedInterval (4474000987 / 1000000000000) (4474001300 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate218_chunkChecks2_1 :
    compactCertificate218.chunkChecks (2 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 2) <| besselDerivativeNearFromState (1757549430314607 / 8000000000000) 2 (IntervalRat.scale (393 / 4) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (28913735624 / 1000000000000) (28913735625 / 1000000000000), orderedInterval (45340803764 / 1000000000000) (45340803765 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 2) <| besselDerivativeNearFromState (1014721636706103 / 8000000000000) 2 (IntervalRat.scale (393 / 4) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (65522192563 / 1000000000000) (65522197839 / 1000000000000), orderedInterval (-27200509556 / 1000000000000) (-27200504280 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 2) <| besselDerivativeNearFromState (1800641350998627 / 8000000000000) 2 (IntervalRat.scale (393 / 4) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-17216365199 / 1000000000000) (-17216364878 / 1000000000000), orderedInterval (50357383313 / 1000000000000) (50357383635 / 1000000000000)))) (orderedInterval (30484392659 / 1000000000000) (30484393731 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 2) <| besselDerivativeNearFromState (1682392723155663 / 8000000000000) 2 (IntervalRat.scale (393 / 4) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-30938751552 / 1000000000000) (-30938751551 / 1000000000000), orderedInterval (-45423782595 / 1000000000000) (-45423782594 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 2) <| besselDerivativeNearFromState (1200634832078079 / 8000000000000) 2 (IntervalRat.scale (393 / 4) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (4391085857 / 1000000000000) (4391085859 / 1000000000000), orderedInterval (64967133268 / 1000000000000) (64967133270 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 2) <| besselDerivativeNearFromState (1361391934748841 / 8000000000000) 2 (IntervalRat.scale (393 / 4) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (59136900480 / 1000000000000) (59136900481 / 1000000000000), orderedInterval (15440545611 / 1000000000000) (15440545613 / 1000000000000)))) (orderedInterval (-2742042993 / 1000000000000) (-2742042960 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 2) <| besselDerivativeNearFromState (1134986662949529 / 8000000000000) 2 (IntervalRat.scale (393 / 4) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-64291761455 / 1000000000000) (-64291761454 / 1000000000000), orderedInterval (-18582634146 / 1000000000000) (-18582634145 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 2) <| besselDerivativeNearFromState (1002795137408109 / 8000000000000) 2 (IntervalRat.scale (393 / 4) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (32280538821 / 1000000000000) (32280538822 / 1000000000000), orderedInterval (63406686407 / 1000000000000) (63406686408 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 2) <| besselDerivativeNearFromState (290649116638791 / 1600000000000) 2 (IntervalRat.scale (393 / 4) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (13382708889 / 1000000000000) (13382708890 / 1000000000000), orderedInterval (57629928665 / 1000000000000) (57629928666 / 1000000000000)))) (orderedInterval (3406113715 / 1000000000000) (3406113736 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate218_chunkChecks2_2 :
    compactCertificate218.chunkChecks (2 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 2) <| besselDerivativeNearFromState (803950752647877 / 8000000000000) 2 (IntervalRat.scale (393 / 4) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (54079776222 / 1000000000000) (54079776223 / 1000000000000), orderedInterval (58128684327 / 1000000000000) (58128684328 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 2) <| besselDerivativeNearFromState (681517956530397 / 8000000000000) 2 (IntervalRat.scale (393 / 4) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-78928162810 / 1000000000000) (-78928162809 / 1000000000000), orderedInterval (-34796117500 / 1000000000000) (-34796117499 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 2) <| besselDerivativeNearFromState (426462293303391 / 8000000000000) 2 (IntervalRat.scale (393 / 4) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-69033087051 / 1000000000000) (-69033087050 / 1000000000000), orderedInterval (-84069029861 / 1000000000000) (-84069029860 / 1000000000000)))) (orderedInterval (6443914239 / 1000000000000) (6443914261 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 2) <| besselDerivativeNearFromState (229352839688097 / 8000000000000) 2 (IntervalRat.scale (393 / 4) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-137531740361 / 1000000000000) (-137531740360 / 1000000000000), orderedInterval (-54946920497 / 1000000000000) (-54946920496 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 2) <| besselDerivativeNearFromState (622737575235291 / 8000000000000) 2 (IntervalRat.scale (393 / 4) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-7783266330 / 1000000000000) (-7783266328 / 1000000000000), orderedInterval (-90049534372 / 1000000000000) (-90049534369 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 2) <| besselDerivativeNearFromState (850294919510907 / 8000000000000) 2 (IntervalRat.scale (393 / 4) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (19666872205 / 1000000000000) (19666872206 / 1000000000000), orderedInterval (74760067019 / 1000000000000) (74760067020 / 1000000000000)))) (orderedInterval (1480444418 / 1000000000000) (1480444430 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 2) <| besselDerivativeNearFromState (359537706696609 / 8000000000000) 2 (IntervalRat.scale (393 / 4) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (117263591229 / 1000000000000) (117263591485 / 1000000000000), orderedInterval (-21644594767 / 1000000000000) (-21644594512 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 2) <| besselDerivativeNearFromState (1461500816785089 / 8000000000000) 2 (IntervalRat.scale (393 / 4) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (56202391685 / 1000000000000) (56202391686 / 1000000000000), orderedInterval (17902367767 / 1000000000000) (17902367768 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 2) <| besselDerivativeNearFromState (976214813725551 / 8000000000000) 2 (IntervalRat.scale (393 / 4) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-20592527582 / 1000000000000) (-20592527581 / 1000000000000), orderedInterval (-69147344596 / 1000000000000) (-69147344595 / 1000000000000)))) (orderedInterval (9573864134 / 1000000000000) (9573864193 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate218_chunkChecks2 :
    compactCertificate218.chunkChecks (2 : Fin 5) 0 9 = true :=
  compactCertificate218.chunkChecks_nine_of_three (2 : Fin 5) compactCertificate218_chunkChecks2_0
    compactCertificate218_chunkChecks2_1 compactCertificate218_chunkChecks2_2

theorem compactCertificate218_chunkChecks3_0 :
    compactCertificate218.chunkChecks (3 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 3) <| besselDerivativeNearFromState (393 / 4) 3 (IntervalRat.scale (393 / 4) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-80275340709 / 1000000000000) (-80275340614 / 1000000000000), orderedInterval (6356394281 / 1000000000000) (6356394376 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 3) <| besselDerivativeNearFromState (578964042525093 / 8000000000000) 3 (IntervalRat.scale (393 / 4) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-73324489281 / 1000000000000) (-73324489280 / 1000000000000), orderedInterval (-57975456125 / 1000000000000) (-57975456124 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 3) <| besselDerivativeNearFromState (187225075785669 / 1600000000000) 3 (IntervalRat.scale (393 / 4) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-73755691321 / 1000000000000) (-73755691289 / 1000000000000), orderedInterval (-401947418 / 1000000000000) (-401947386 / 1000000000000)))) (orderedInterval (-2653378911 / 1000000000000) (-2653378858 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 3) <| besselDerivativeNearFromState (168940263651951 / 8000000000000) 3 (IntervalRat.scale (393 / 4) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (16317124587 / 1000000000000) (16317124634 / 1000000000000), orderedInterval (-173269110906 / 1000000000000) (-173269110858 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 3) <| besselDerivativeNearFromState (453797311582947 / 8000000000000) 3 (IntervalRat.scale (393 / 4) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (86733120397 / 1000000000000) (86733120398 / 1000000000000), orderedInterval (60064797944 / 1000000000000) (60064797945 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 3) <| besselDerivativeNearFromState (1232147977096599 / 8000000000000) 3 (IntervalRat.scale (393 / 4) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-48933656641 / 1000000000000) (-48933656640 / 1000000000000), orderedInterval (-41541168643 / 1000000000000) (-41541168642 / 1000000000000)))) (orderedInterval (-11718178277 / 1000000000000) (-11718178248 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 3) <| besselDerivativeNearFromState (907594623166287 / 8000000000000) 3 (IntervalRat.scale (393 / 4) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (67948732401 / 1000000000000) (67948732402 / 1000000000000), orderedInterval (31235037324 / 1000000000000) (31235037325 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 3) <| besselDerivativeNearFromState (1555178856250251 / 8000000000000) 3 (IntervalRat.scale (393 / 4) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (22462272615 / 1000000000000) (22462272616 / 1000000000000), orderedInterval (52575783940 / 1000000000000) (52575783941 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 3) <| besselDerivativeNearFromState (1145537706696609 / 8000000000000) 3 (IntervalRat.scale (393 / 4) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-34082256363 / 1000000000000) (-34082250653 / 1000000000000), orderedInterval (57428021757 / 1000000000000) (57428027467 / 1000000000000)))) (orderedInterval (8218896447 / 1000000000000) (8218896909 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate218_chunkChecks3_1 :
    compactCertificate218.chunkChecks (3 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 3) <| besselDerivativeNearFromState (1757549430314607 / 8000000000000) 3 (IntervalRat.scale (393 / 4) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (28913735624 / 1000000000000) (28913735625 / 1000000000000), orderedInterval (45340803764 / 1000000000000) (45340803765 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 3) <| besselDerivativeNearFromState (1014721636706103 / 8000000000000) 3 (IntervalRat.scale (393 / 4) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (65522192563 / 1000000000000) (65522197839 / 1000000000000), orderedInterval (-27200509556 / 1000000000000) (-27200504280 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 3) <| besselDerivativeNearFromState (1800641350998627 / 8000000000000) 3 (IntervalRat.scale (393 / 4) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-17216365199 / 1000000000000) (-17216364878 / 1000000000000), orderedInterval (50357383313 / 1000000000000) (50357383635 / 1000000000000)))) (orderedInterval (8032088842 / 1000000000000) (8032090624 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 3) <| besselDerivativeNearFromState (1682392723155663 / 8000000000000) 3 (IntervalRat.scale (393 / 4) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-30938751552 / 1000000000000) (-30938751551 / 1000000000000), orderedInterval (-45423782595 / 1000000000000) (-45423782594 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 3) <| besselDerivativeNearFromState (1200634832078079 / 8000000000000) 3 (IntervalRat.scale (393 / 4) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (4391085857 / 1000000000000) (4391085859 / 1000000000000), orderedInterval (64967133268 / 1000000000000) (64967133270 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 3) <| besselDerivativeNearFromState (1361391934748841 / 8000000000000) 3 (IntervalRat.scale (393 / 4) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (59136900480 / 1000000000000) (59136900481 / 1000000000000), orderedInterval (15440545611 / 1000000000000) (15440545613 / 1000000000000)))) (orderedInterval (-29503401965 / 1000000000000) (-29503401910 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 3) <| besselDerivativeNearFromState (1134986662949529 / 8000000000000) 3 (IntervalRat.scale (393 / 4) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-64291761455 / 1000000000000) (-64291761454 / 1000000000000), orderedInterval (-18582634146 / 1000000000000) (-18582634145 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 3) <| besselDerivativeNearFromState (1002795137408109 / 8000000000000) 3 (IntervalRat.scale (393 / 4) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (32280538821 / 1000000000000) (32280538822 / 1000000000000), orderedInterval (63406686407 / 1000000000000) (63406686408 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 3) <| besselDerivativeNearFromState (290649116638791 / 1600000000000) 3 (IntervalRat.scale (393 / 4) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (13382708889 / 1000000000000) (13382708890 / 1000000000000), orderedInterval (57629928665 / 1000000000000) (57629928666 / 1000000000000)))) (orderedInterval (-1179645538 / 1000000000000) (-1179645506 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate218_chunkChecks3_2 :
    compactCertificate218.chunkChecks (3 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 3) <| besselDerivativeNearFromState (803950752647877 / 8000000000000) 3 (IntervalRat.scale (393 / 4) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (54079776222 / 1000000000000) (54079776223 / 1000000000000), orderedInterval (58128684327 / 1000000000000) (58128684328 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 3) <| besselDerivativeNearFromState (681517956530397 / 8000000000000) 3 (IntervalRat.scale (393 / 4) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-78928162810 / 1000000000000) (-78928162809 / 1000000000000), orderedInterval (-34796117500 / 1000000000000) (-34796117499 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 3) <| besselDerivativeNearFromState (426462293303391 / 8000000000000) 3 (IntervalRat.scale (393 / 4) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-69033087051 / 1000000000000) (-69033087050 / 1000000000000), orderedInterval (-84069029861 / 1000000000000) (-84069029860 / 1000000000000)))) (orderedInterval (9032548155 / 1000000000000) (9032548177 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 3) <| besselDerivativeNearFromState (229352839688097 / 8000000000000) 3 (IntervalRat.scale (393 / 4) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-137531740361 / 1000000000000) (-137531740360 / 1000000000000), orderedInterval (-54946920497 / 1000000000000) (-54946920496 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 3) <| besselDerivativeNearFromState (622737575235291 / 8000000000000) 3 (IntervalRat.scale (393 / 4) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-7783266330 / 1000000000000) (-7783266328 / 1000000000000), orderedInterval (-90049534372 / 1000000000000) (-90049534369 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 3) <| besselDerivativeNearFromState (850294919510907 / 8000000000000) 3 (IntervalRat.scale (393 / 4) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (19666872205 / 1000000000000) (19666872206 / 1000000000000), orderedInterval (74760067019 / 1000000000000) (74760067020 / 1000000000000)))) (orderedInterval (6196962149 / 1000000000000) (6196962160 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 3) <| besselDerivativeNearFromState (359537706696609 / 8000000000000) 3 (IntervalRat.scale (393 / 4) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (117263591229 / 1000000000000) (117263591485 / 1000000000000), orderedInterval (-21644594767 / 1000000000000) (-21644594512 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 3) <| besselDerivativeNearFromState (1461500816785089 / 8000000000000) 3 (IntervalRat.scale (393 / 4) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (56202391685 / 1000000000000) (56202391686 / 1000000000000), orderedInterval (17902367767 / 1000000000000) (17902367768 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 3) <| besselDerivativeNearFromState (976214813725551 / 8000000000000) 3 (IntervalRat.scale (393 / 4) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-20592527582 / 1000000000000) (-20592527581 / 1000000000000), orderedInterval (-69147344596 / 1000000000000) (-69147344595 / 1000000000000)))) (orderedInterval (-15571393464 / 1000000000000) (-15571393376 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate218_chunkChecks3 :
    compactCertificate218.chunkChecks (3 : Fin 5) 0 9 = true :=
  compactCertificate218.chunkChecks_nine_of_three (3 : Fin 5) compactCertificate218_chunkChecks3_0
    compactCertificate218_chunkChecks3_1 compactCertificate218_chunkChecks3_2

theorem compactCertificate218_chunkChecks4_0 :
    compactCertificate218.chunkChecks (4 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 4) <| besselDerivativeNearFromState (393 / 4) 4 (IntervalRat.scale (393 / 4) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-80275340709 / 1000000000000) (-80275340614 / 1000000000000), orderedInterval (6356394281 / 1000000000000) (6356394376 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 4) <| besselDerivativeNearFromState (578964042525093 / 8000000000000) 4 (IntervalRat.scale (393 / 4) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-73324489281 / 1000000000000) (-73324489280 / 1000000000000), orderedInterval (-57975456125 / 1000000000000) (-57975456124 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 4) <| besselDerivativeNearFromState (187225075785669 / 1600000000000) 4 (IntervalRat.scale (393 / 4) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-73755691321 / 1000000000000) (-73755691289 / 1000000000000), orderedInterval (-401947418 / 1000000000000) (-401947386 / 1000000000000)))) (orderedInterval (-40669924496 / 1000000000000) (-40669924440 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 4) <| besselDerivativeNearFromState (168940263651951 / 8000000000000) 4 (IntervalRat.scale (393 / 4) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (16317124587 / 1000000000000) (16317124634 / 1000000000000), orderedInterval (-173269110906 / 1000000000000) (-173269110858 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 4) <| besselDerivativeNearFromState (453797311582947 / 8000000000000) 4 (IntervalRat.scale (393 / 4) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (86733120397 / 1000000000000) (86733120398 / 1000000000000), orderedInterval (60064797944 / 1000000000000) (60064797945 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 4) <| besselDerivativeNearFromState (1232147977096599 / 8000000000000) 4 (IntervalRat.scale (393 / 4) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-48933656641 / 1000000000000) (-48933656640 / 1000000000000), orderedInterval (-41541168643 / 1000000000000) (-41541168642 / 1000000000000)))) (orderedInterval (21596560888 / 1000000000000) (21596560932 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 4) <| besselDerivativeNearFromState (907594623166287 / 8000000000000) 4 (IntervalRat.scale (393 / 4) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (67948732401 / 1000000000000) (67948732402 / 1000000000000), orderedInterval (31235037324 / 1000000000000) (31235037325 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 4) <| besselDerivativeNearFromState (1555178856250251 / 8000000000000) 4 (IntervalRat.scale (393 / 4) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (22462272615 / 1000000000000) (22462272616 / 1000000000000), orderedInterval (52575783940 / 1000000000000) (52575783941 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 4) <| besselDerivativeNearFromState (1145537706696609 / 8000000000000) 4 (IntervalRat.scale (393 / 4) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-34082256363 / 1000000000000) (-34082250653 / 1000000000000), orderedInterval (57428021757 / 1000000000000) (57428027467 / 1000000000000)))) (orderedInterval (-14501508304 / 1000000000000) (-14501507614 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate218_chunkChecks4_1 :
    compactCertificate218.chunkChecks (4 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 4) <| besselDerivativeNearFromState (1757549430314607 / 8000000000000) 4 (IntervalRat.scale (393 / 4) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (28913735624 / 1000000000000) (28913735625 / 1000000000000), orderedInterval (45340803764 / 1000000000000) (45340803765 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 4) <| besselDerivativeNearFromState (1014721636706103 / 8000000000000) 4 (IntervalRat.scale (393 / 4) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (65522192563 / 1000000000000) (65522197839 / 1000000000000), orderedInterval (-27200509556 / 1000000000000) (-27200504280 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 4) <| besselDerivativeNearFromState (1800641350998627 / 8000000000000) 4 (IntervalRat.scale (393 / 4) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-17216365199 / 1000000000000) (-17216364878 / 1000000000000), orderedInterval (50357383313 / 1000000000000) (50357383635 / 1000000000000)))) (orderedInterval (-182525838641 / 1000000000000) (-182525835423 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 4) <| besselDerivativeNearFromState (1682392723155663 / 8000000000000) 4 (IntervalRat.scale (393 / 4) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-30938751552 / 1000000000000) (-30938751551 / 1000000000000), orderedInterval (-45423782595 / 1000000000000) (-45423782594 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 4) <| besselDerivativeNearFromState (1200634832078079 / 8000000000000) 4 (IntervalRat.scale (393 / 4) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (4391085857 / 1000000000000) (4391085859 / 1000000000000), orderedInterval (64967133268 / 1000000000000) (64967133270 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 4) <| besselDerivativeNearFromState (1361391934748841 / 8000000000000) 4 (IntervalRat.scale (393 / 4) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (59136900480 / 1000000000000) (59136900481 / 1000000000000), orderedInterval (15440545611 / 1000000000000) (15440545613 / 1000000000000)))) (orderedInterval (11891537765 / 1000000000000) (11891537859 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 4) <| besselDerivativeNearFromState (1134986662949529 / 8000000000000) 4 (IntervalRat.scale (393 / 4) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-64291761455 / 1000000000000) (-64291761454 / 1000000000000), orderedInterval (-18582634146 / 1000000000000) (-18582634145 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 4) <| besselDerivativeNearFromState (1002795137408109 / 8000000000000) 4 (IntervalRat.scale (393 / 4) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (32280538821 / 1000000000000) (32280538822 / 1000000000000), orderedInterval (63406686407 / 1000000000000) (63406686408 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 4) <| besselDerivativeNearFromState (290649116638791 / 1600000000000) 4 (IntervalRat.scale (393 / 4) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (13382708889 / 1000000000000) (13382708890 / 1000000000000), orderedInterval (57629928665 / 1000000000000) (57629928666 / 1000000000000)))) (orderedInterval (-4093723378 / 1000000000000) (-4093723328 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate218_chunkChecks4_2 :
    compactCertificate218.chunkChecks (4 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 4) <| besselDerivativeNearFromState (803950752647877 / 8000000000000) 4 (IntervalRat.scale (393 / 4) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (54079776222 / 1000000000000) (54079776223 / 1000000000000), orderedInterval (58128684327 / 1000000000000) (58128684328 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 4) <| besselDerivativeNearFromState (681517956530397 / 8000000000000) 4 (IntervalRat.scale (393 / 4) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-78928162810 / 1000000000000) (-78928162809 / 1000000000000), orderedInterval (-34796117500 / 1000000000000) (-34796117499 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 4) <| besselDerivativeNearFromState (426462293303391 / 8000000000000) 4 (IntervalRat.scale (393 / 4) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-69033087051 / 1000000000000) (-69033087050 / 1000000000000), orderedInterval (-84069029861 / 1000000000000) (-84069029860 / 1000000000000)))) (orderedInterval (-7317264949 / 1000000000000) (-7317264927 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 4) <| besselDerivativeNearFromState (229352839688097 / 8000000000000) 4 (IntervalRat.scale (393 / 4) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-137531740361 / 1000000000000) (-137531740360 / 1000000000000), orderedInterval (-54946920497 / 1000000000000) (-54946920496 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 4) <| besselDerivativeNearFromState (622737575235291 / 8000000000000) 4 (IntervalRat.scale (393 / 4) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-7783266330 / 1000000000000) (-7783266328 / 1000000000000), orderedInterval (-90049534372 / 1000000000000) (-90049534369 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 4) <| besselDerivativeNearFromState (850294919510907 / 8000000000000) 4 (IntervalRat.scale (393 / 4) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (19666872205 / 1000000000000) (19666872206 / 1000000000000), orderedInterval (74760067019 / 1000000000000) (74760067020 / 1000000000000)))) (orderedInterval (-2102299364 / 1000000000000) (-2102299351 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 4) <| besselDerivativeNearFromState (359537706696609 / 8000000000000) 4 (IntervalRat.scale (393 / 4) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (117263591229 / 1000000000000) (117263591485 / 1000000000000), orderedInterval (-21644594767 / 1000000000000) (-21644594512 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 4) <| besselDerivativeNearFromState (1461500816785089 / 8000000000000) 4 (IntervalRat.scale (393 / 4) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (56202391685 / 1000000000000) (56202391686 / 1000000000000), orderedInterval (17902367767 / 1000000000000) (17902367768 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 4) <| besselDerivativeNearFromState (976214813725551 / 8000000000000) 4 (IntervalRat.scale (393 / 4) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-20592527582 / 1000000000000) (-20592527581 / 1000000000000), orderedInterval (-69147344596 / 1000000000000) (-69147344595 / 1000000000000)))) (orderedInterval (-45145634300 / 1000000000000) (-45145634158 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate218_chunkChecks4 :
    compactCertificate218.chunkChecks (4 : Fin 5) 0 9 = true :=
  compactCertificate218.chunkChecks_nine_of_three (4 : Fin 5) compactCertificate218_chunkChecks4_0
    compactCertificate218_chunkChecks4_1 compactCertificate218_chunkChecks4_2

theorem compactCertificate218_chunks :
    ∀ r : Fin 5, ∀ b, compactCertificate218.chunkCheck r b = true :=
  compactCertificate218.chunkChecks_all (by
    intro r
    fin_cases r
    · exact compactCertificate218_chunkChecks0
    · exact compactCertificate218_chunkChecks1
    · exact compactCertificate218_chunkChecks2
    · exact compactCertificate218_chunkChecks3
    · exact compactCertificate218_chunkChecks4)

theorem compactCertificate218_coefficient0 :
    compactCertificate218.coefficientCheck (0 : Fin 5) = true := by
  norm_num [CompactCertificate.coefficientCheck, intervalFinSumHull,
    compactCertificate218, rationalIntervalSubset, orderedInterval, Fin.sum_univ_succ]

theorem compactCertificate218_coefficient1 :
    compactCertificate218.coefficientCheck (1 : Fin 5) = true := by
  norm_num [CompactCertificate.coefficientCheck, intervalFinSumHull,
    compactCertificate218, rationalIntervalSubset, orderedInterval, Fin.sum_univ_succ]

theorem compactCertificate218_coefficient2 :
    compactCertificate218.coefficientCheck (2 : Fin 5) = true := by
  norm_num [CompactCertificate.coefficientCheck, intervalFinSumHull,
    compactCertificate218, rationalIntervalSubset, orderedInterval, Fin.sum_univ_succ]

theorem compactCertificate218_coefficient3 :
    compactCertificate218.coefficientCheck (3 : Fin 5) = true := by
  norm_num [CompactCertificate.coefficientCheck, intervalFinSumHull,
    compactCertificate218, rationalIntervalSubset, orderedInterval, Fin.sum_univ_succ]

theorem compactCertificate218_coefficient4 :
    compactCertificate218.coefficientCheck (4 : Fin 5) = true := by
  norm_num [CompactCertificate.coefficientCheck, intervalFinSumHull,
    compactCertificate218, rationalIntervalSubset, orderedInterval, Fin.sum_univ_succ]

theorem compactCertificate218_coefficients : ∀ r : Fin 5,
    compactCertificate218.coefficientCheck r = true := by
  intro r
  fin_cases r
  · exact compactCertificate218_coefficient0
  · exact compactCertificate218_coefficient1
  · exact compactCertificate218_coefficient2
  · exact compactCertificate218_coefficient3
  · exact compactCertificate218_coefficient4

theorem compactCertificate218_lower : (1 : ℚ) ≤ compactCertificate218.output.lo := by
  norm_num [CompactCertificate.output, CompactCertificate.interval,
    CompactCertificate.coefficientTargetNat, compactCertificate218, dualConstant,
    intervalTaylorSum, intervalPow, intervalSub, intervalMaxAbs, widenInterval,
    rationalErrorInterval, orderedInterval, IntervalRat.add, IntervalRat.mul, IntervalRat.scale,
    IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4]

theorem compactCertificate218_proves {t : ℝ} (ht : t ∈ compactCertificate218.interval) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t :=
  compactCertificate218.proves compactCertificate218_states compactCertificate218_chunks
    compactCertificate218_coefficients compactCertificate218_lower ht

end Erdos232
