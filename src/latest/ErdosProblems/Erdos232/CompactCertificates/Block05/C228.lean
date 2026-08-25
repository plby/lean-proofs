/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, OpenAI Codex
-/
import ErdosProblems.Erdos232.CompactBase

open LeanCert.Core
namespace Erdos232

def compactCertificate228 : CompactCertificate where
  left := 211 / 2
  right := 106
  center := 423 / 4
  grid := fun i =>
    match i.val with
    | 0 => 34
    | 1 => 25
    | 2 => 40
    | 3 => 7
    | 4 => 19
    | 5 => 53
    | 6 => 39
    | 7 => 67
    | 8 => 49
    | 9 => 75
    | 10 => 43
    | 11 => 77
    | 12 => 72
    | 13 => 51
    | 14 => 58
    | 15 => 49
    | 16 => 43
    | 17 => 62
    | 18 => 34
    | 19 => 29
    | 20 => 18
    | 21 => 10
    | 22 => 27
    | 23 => 36
    | 24 => 15
    | 25 => 63
    | _ => 42
  point := fun i =>
    match i.val with
    | 0 => 423 / 4
    | 1 => 623159770962123 / 8000000000000
    | 2 => 201517066303659 / 1600000000000
    | 3 => 181836466984161 / 8000000000000
    | 4 => 488438327734317 / 8000000000000
    | 5 => 1326205074584889 / 8000000000000
    | 6 => 976876655469057 / 8000000000000
    | 7 => 1673894799475461 / 8000000000000
    | 8 => 1232983333161999 / 8000000000000
    | 9 => 1891713508964577 / 8000000000000
    | 10 => 1092181303630233 / 8000000000000
    | 11 => 1938094889242797 / 8000000000000
    | 12 => 1810819648587393 / 8000000000000
    | 13 => 1292286345977169 / 8000000000000
    | 14 => 1465314983202951 / 8000000000000
    | 15 => 1221626866228119 / 8000000000000
    | 16 => 1079344384538499 / 8000000000000
    | 17 => 312836072107401 / 1600000000000
    | 18 => 865321039109547 / 8000000000000
    | 19 => 733542228021267 / 8000000000000
    | 20 => 459016666838001 / 8000000000000
    | 21 => 246860690045967 / 8000000000000
    | 22 => 670274794718901 / 8000000000000
    | 23 => 915202928633877 / 8000000000000
    | 24 => 386983333161999 / 8000000000000
    | 25 => 1573065764631279 / 8000000000000
    | _ => 1050735028513761 / 8000000000000
  state := fun i =>
    match i.val with
    | 0 => (orderedInterval (-21437106172 / 1000000000000) (-21437105805 / 1000000000000), orderedInterval (74670468084 / 1000000000000) (74670468451 / 1000000000000))
    | 1 => (orderedInterval (-12520933453 / 1000000000000) (-12520933452 / 1000000000000), orderedInterval (-89452782357 / 1000000000000) (-89452782356 / 1000000000000))
    | 2 => (orderedInterval (62326305255 / 1000000000000) (62326305256 / 1000000000000), orderedInterval (33958240476 / 1000000000000) (33958240477 / 1000000000000))
    | 3 => (orderedInterval (-167106677261 / 1000000000000) (-167106677252 / 1000000000000), orderedInterval (-5106112297 / 1000000000000) (-5106112289 / 1000000000000))
    | 4 => (orderedInterval (-85574863635 / 1000000000000) (-85574839348 / 1000000000000), orderedInterval (56412746558 / 1000000000000) (56412770845 / 1000000000000))
    | 5 => (orderedInterval (-3460306576 / 1000000000000) (-3460306574 / 1000000000000), orderedInterval (-61862764269 / 1000000000000) (-61862764267 / 1000000000000))
    | 6 => (orderedInterval (-26234228550 / 1000000000000) (-26234228549 / 1000000000000), orderedInterval (-67163001123 / 1000000000000) (-67163001122 / 1000000000000))
    | 7 => (orderedInterval (24737593392 / 1000000000000) (24737595221 / 1000000000000), orderedInterval (-49360597385 / 1000000000000) (-49360595556 / 1000000000000))
    | 8 => (orderedInterval (-52995549663 / 1000000000000) (-52995549662 / 1000000000000), orderedInterval (-36188241155 / 1000000000000) (-36188241154 / 1000000000000))
    | 9 => (orderedInterval (-51797089036 / 1000000000000) (-51797088835 / 1000000000000), orderedInterval (3159380582 / 1000000000000) (3159380783 / 1000000000000))
    | 10 => (orderedInterval (-54450081963 / 1000000000000) (-54450017996 / 1000000000000), orderedInterval (41409699380 / 1000000000000) (41409763347 / 1000000000000))
    | 11 => (orderedInterval (-46666101823 / 1000000000000) (-46666101822 / 1000000000000), orderedInterval (-21118964427 / 1000000000000) (-21118964426 / 1000000000000))
    | 12 => (orderedInterval (42909444022 / 1000000000000) (42909444023 / 1000000000000), orderedInterval (31070788369 / 1000000000000) (31070788370 / 1000000000000))
    | 13 => (orderedInterval (-54215796861 / 1000000000000) (-54215772346 / 1000000000000), orderedInterval (31817190940 / 1000000000000) (31817215455 / 1000000000000))
    | 14 => (orderedInterval (58145122638 / 1000000000000) (58145123204 / 1000000000000), orderedInterval (-9895617348 / 1000000000000) (-9895616782 / 1000000000000))
    | 15 => (orderedInterval (28090615494 / 1000000000000) (28090617625 / 1000000000000), orderedInterval (-58229123261 / 1000000000000) (-58229121130 / 1000000000000))
    | 16 => (orderedInterval (-39578073223 / 1000000000000) (-39578073222 / 1000000000000), orderedInterval (-55997369393 / 1000000000000) (-55997369392 / 1000000000000))
    | 17 => (orderedInterval (57010314103 / 1000000000000) (57010314139 / 1000000000000), orderedInterval (2263592331 / 1000000000000) (2263592367 / 1000000000000))
    | 18 => (orderedInterval (64818231788 / 1000000000000) (64818258523 / 1000000000000), orderedInterval (-41338597318 / 1000000000000) (-41338570583 / 1000000000000))
    | 19 => (orderedInterval (-81660097326 / 1000000000000) (-81660097324 / 1000000000000), orderedInterval (-16122723191 / 1000000000000) (-16122723189 / 1000000000000))
    | 20 => (orderedInterval (105244720445 / 1000000000000) (105244720490 / 1000000000000), orderedInterval (-5217727073 / 1000000000000) (-5217727028 / 1000000000000))
    | 21 => (orderedInterval (31764912591 / 1000000000000) (31764912592 / 1000000000000), orderedInterval (139572297414 / 1000000000000) (139572297415 / 1000000000000))
    | 22 => (orderedInterval (21966180508 / 1000000000000) (21966180812 / 1000000000000), orderedInterval (-84486988233 / 1000000000000) (-84486987929 / 1000000000000))
    | 23 => (orderedInterval (64865002088 / 1000000000000) (64865019639 / 1000000000000), orderedInterval (-37125644985 / 1000000000000) (-37125627434 / 1000000000000))
    | 24 => (orderedInterval (-102739067154 / 1000000000000) (-102739059755 / 1000000000000), orderedInterval (52100304548 / 1000000000000) (52100311948 / 1000000000000))
    | 25 => (orderedInterval (27396702546 / 1000000000000) (27396705523 / 1000000000000), orderedInterval (-49939761823 / 1000000000000) (-49939758846 / 1000000000000))
    | _ => (orderedInterval (12425322348 / 1000000000000) (12425322349 / 1000000000000), orderedInterval (68455892922 / 1000000000000) (68455892923 / 1000000000000))
  chunkTarget := fun r b =>
    match r.val with
    | 0 =>
      match b.val with
      | 0 => orderedInterval (-4956210607 / 1000000000000) (-4956210453 / 1000000000000)
      | 1 => orderedInterval (-1065506770 / 1000000000000) (-1065505870 / 1000000000000)
      | 2 => orderedInterval (-2043804290 / 1000000000000) (-2043804227 / 1000000000000)
      | 3 => orderedInterval (-1464447068 / 1000000000000) (-1464442250 / 1000000000000)
      | 4 => orderedInterval (-6195696839 / 1000000000000) (-6195694504 / 1000000000000)
      | 5 => orderedInterval (4048991997 / 1000000000000) (4048992033 / 1000000000000)
      | 6 => orderedInterval (-2315721344 / 1000000000000) (-2315717041 / 1000000000000)
      | 7 => orderedInterval (-6056068355 / 1000000000000) (-6056066989 / 1000000000000)
      | _ => orderedInterval (-5180805403 / 1000000000000) (-5180805086 / 1000000000000)
    | 1 =>
      match b.val with
      | 0 => orderedInterval (31356101754 / 1000000000000) (31356101908 / 1000000000000)
      | 1 => orderedInterval (8095165826 / 1000000000000) (8095166354 / 1000000000000)
      | 2 => orderedInterval (1737710635 / 1000000000000) (1737710758 / 1000000000000)
      | 3 => orderedInterval (-4172052195 / 1000000000000) (-4172045909 / 1000000000000)
      | 4 => orderedInterval (3482011537 / 1000000000000) (3482015105 / 1000000000000)
      | 5 => orderedInterval (3224616977 / 1000000000000) (3224617030 / 1000000000000)
      | 6 => orderedInterval (7459756562 / 1000000000000) (7459760961 / 1000000000000)
      | 7 => orderedInterval (3844595153 / 1000000000000) (3844596626 / 1000000000000)
      | _ => orderedInterval (-8249932587 / 1000000000000) (-8249932074 / 1000000000000)
    | 2 =>
      match b.val with
      | 0 => orderedInterval (3075793871 / 1000000000000) (3075794028 / 1000000000000)
      | 1 => orderedInterval (276682169 / 1000000000000) (276682491 / 1000000000000)
      | 2 => orderedInterval (5691161177 / 1000000000000) (5691161418 / 1000000000000)
      | 3 => orderedInterval (-4439555864 / 1000000000000) (-4439547540 / 1000000000000)
      | 4 => orderedInterval (16361412585 / 1000000000000) (16361418071 / 1000000000000)
      | 5 => orderedInterval (-9383447269 / 1000000000000) (-9383447192 / 1000000000000)
      | 6 => orderedInterval (6288706002 / 1000000000000) (6288710540 / 1000000000000)
      | 7 => orderedInterval (6144136354 / 1000000000000) (6144137959 / 1000000000000)
      | _ => orderedInterval (11514383519 / 1000000000000) (11514384432 / 1000000000000)
    | 3 =>
      match b.val with
      | 0 => orderedInterval (-32656413206 / 1000000000000) (-32656413047 / 1000000000000)
      | 1 => orderedInterval (-17340522877 / 1000000000000) (-17340522672 / 1000000000000)
      | 2 => orderedInterval (-9139162818 / 1000000000000) (-9139162345 / 1000000000000)
      | 3 => orderedInterval (35811891247 / 1000000000000) (35811902330 / 1000000000000)
      | 4 => orderedInterval (-5637695504 / 1000000000000) (-5637687117 / 1000000000000)
      | 5 => orderedInterval (-4907496736 / 1000000000000) (-4907496621 / 1000000000000)
      | 6 => orderedInterval (-7699546067 / 1000000000000) (-7699541428 / 1000000000000)
      | 7 => orderedInterval (-4549156067 / 1000000000000) (-4549154333 / 1000000000000)
      | _ => orderedInterval (-1666076138 / 1000000000000) (-1666074473 / 1000000000000)
    | _ =>
      match b.val with
      | 0 => orderedInterval (-554451295 / 1000000000000) (-554451133 / 1000000000000)
      | 1 => orderedInterval (1470207673 / 1000000000000) (1470207823 / 1000000000000)
      | 2 => orderedInterval (-17299218929 / 1000000000000) (-17299217994 / 1000000000000)
      | 3 => orderedInterval (35489269944 / 1000000000000) (35489285111 / 1000000000000)
      | 4 => orderedInterval (-46712848786 / 1000000000000) (-46712835883 / 1000000000000)
      | 5 => orderedInterval (24561091571 / 1000000000000) (24561091744 / 1000000000000)
      | 6 => orderedInterval (-8288116094 / 1000000000000) (-8288111307 / 1000000000000)
      | 7 => orderedInterval (-6922475782 / 1000000000000) (-6922473893 / 1000000000000)
      | _ => orderedInterval (-32200676729 / 1000000000000) (-32200673649 / 1000000000000)
  coefficientTarget := fun i =>
    match i.val with
    | 0 => orderedInterval (-25229268679 / 1000000000000) (-25229254387 / 1000000000000)
    | 1 => orderedInterval (46777973662 / 1000000000000) (46777990759 / 1000000000000)
    | 2 => orderedInterval (35529272544 / 1000000000000) (35529294207 / 1000000000000)
    | 3 => orderedInterval (-47784178166 / 1000000000000) (-47784149706 / 1000000000000)
    | _ => orderedInterval (-50457218427 / 1000000000000) (-50457179181 / 1000000000000)

theorem compactCertificate228_stateChecks0 :
    compactCertificate228.stateChecks 0 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 34 12 (423 / 4)) (orderedInterval (-21437106172 / 1000000000000) (-21437105805 / 1000000000000), orderedInterval (74670468084 / 1000000000000) (74670468451 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 25 12 (623159770962123 / 8000000000000)) (orderedInterval (-12520933453 / 1000000000000) (-12520933452 / 1000000000000), orderedInterval (-89452782357 / 1000000000000) (-89452782356 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 40 12 (201517066303659 / 1600000000000)) (orderedInterval (62326305255 / 1000000000000) (62326305256 / 1000000000000), orderedInterval (33958240476 / 1000000000000) (33958240477 / 1000000000000))) = true
  norm_num [besselStateAtRationalPoint, besselIntervalStepZero,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, besselZeroTransition,
    besselInitial, besselGridStateAt, besselGridStateBlock00, besselGridStateBlock01,
    besselGridStateBlock02, besselGridStateBlock03, besselGridStateBlock04,
    besselGridStateBlock05, besselGridStateBlock06, besselGridStateBlock07,
    besselGridStateBlock08, besselGridStateBlock09, besselGridStateBlock10,
    besselGridStateBlock11, besselGridStateBlock12, besselGridStateBlock13,
    besselGridStateBlock14, besselGridState007, besselGridState010, besselGridState015, besselGridState018, besselGridState019, besselGridState025, besselGridState027, besselGridState029, besselGridState034, besselGridState036, besselGridState039, besselGridState040, besselGridState042, besselGridState043, besselGridState049, besselGridState051, besselGridState053, besselGridState058, besselGridState062, besselGridState063, besselGridState067, besselGridState072, besselGridState075, besselGridState077, besselStateSubset, linearInterval, widenInterval,
    rationalErrorInterval, rationalIntervalSubset, orderedInterval, Finset.sum_range_succ,
    IntervalRat.add, IntervalRat.mul, IntervalRat.scale, IntervalRat.singleton]

theorem compactCertificate228_stateChecks1 :
    compactCertificate228.stateChecks 3 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 7 12 (181836466984161 / 8000000000000)) (orderedInterval (-167106677261 / 1000000000000) (-167106677252 / 1000000000000), orderedInterval (-5106112297 / 1000000000000) (-5106112289 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 19 12 (488438327734317 / 8000000000000)) (orderedInterval (-85574863635 / 1000000000000) (-85574839348 / 1000000000000), orderedInterval (56412746558 / 1000000000000) (56412770845 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 53 12 (1326205074584889 / 8000000000000)) (orderedInterval (-3460306576 / 1000000000000) (-3460306574 / 1000000000000), orderedInterval (-61862764269 / 1000000000000) (-61862764267 / 1000000000000))) = true
  norm_num [besselStateAtRationalPoint, besselIntervalStepZero,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, besselZeroTransition,
    besselInitial, besselGridStateAt, besselGridStateBlock00, besselGridStateBlock01,
    besselGridStateBlock02, besselGridStateBlock03, besselGridStateBlock04,
    besselGridStateBlock05, besselGridStateBlock06, besselGridStateBlock07,
    besselGridStateBlock08, besselGridStateBlock09, besselGridStateBlock10,
    besselGridStateBlock11, besselGridStateBlock12, besselGridStateBlock13,
    besselGridStateBlock14, besselGridState007, besselGridState010, besselGridState015, besselGridState018, besselGridState019, besselGridState025, besselGridState027, besselGridState029, besselGridState034, besselGridState036, besselGridState039, besselGridState040, besselGridState042, besselGridState043, besselGridState049, besselGridState051, besselGridState053, besselGridState058, besselGridState062, besselGridState063, besselGridState067, besselGridState072, besselGridState075, besselGridState077, besselStateSubset, linearInterval, widenInterval,
    rationalErrorInterval, rationalIntervalSubset, orderedInterval, Finset.sum_range_succ,
    IntervalRat.add, IntervalRat.mul, IntervalRat.scale, IntervalRat.singleton]

theorem compactCertificate228_stateChecks2 :
    compactCertificate228.stateChecks 6 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 39 12 (976876655469057 / 8000000000000)) (orderedInterval (-26234228550 / 1000000000000) (-26234228549 / 1000000000000), orderedInterval (-67163001123 / 1000000000000) (-67163001122 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 67 12 (1673894799475461 / 8000000000000)) (orderedInterval (24737593392 / 1000000000000) (24737595221 / 1000000000000), orderedInterval (-49360597385 / 1000000000000) (-49360595556 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 49 12 (1232983333161999 / 8000000000000)) (orderedInterval (-52995549663 / 1000000000000) (-52995549662 / 1000000000000), orderedInterval (-36188241155 / 1000000000000) (-36188241154 / 1000000000000))) = true
  norm_num [besselStateAtRationalPoint, besselIntervalStepZero,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, besselZeroTransition,
    besselInitial, besselGridStateAt, besselGridStateBlock00, besselGridStateBlock01,
    besselGridStateBlock02, besselGridStateBlock03, besselGridStateBlock04,
    besselGridStateBlock05, besselGridStateBlock06, besselGridStateBlock07,
    besselGridStateBlock08, besselGridStateBlock09, besselGridStateBlock10,
    besselGridStateBlock11, besselGridStateBlock12, besselGridStateBlock13,
    besselGridStateBlock14, besselGridState007, besselGridState010, besselGridState015, besselGridState018, besselGridState019, besselGridState025, besselGridState027, besselGridState029, besselGridState034, besselGridState036, besselGridState039, besselGridState040, besselGridState042, besselGridState043, besselGridState049, besselGridState051, besselGridState053, besselGridState058, besselGridState062, besselGridState063, besselGridState067, besselGridState072, besselGridState075, besselGridState077, besselStateSubset, linearInterval, widenInterval,
    rationalErrorInterval, rationalIntervalSubset, orderedInterval, Finset.sum_range_succ,
    IntervalRat.add, IntervalRat.mul, IntervalRat.scale, IntervalRat.singleton]

theorem compactCertificate228_stateChecks3 :
    compactCertificate228.stateChecks 9 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 75 12 (1891713508964577 / 8000000000000)) (orderedInterval (-51797089036 / 1000000000000) (-51797088835 / 1000000000000), orderedInterval (3159380582 / 1000000000000) (3159380783 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 43 12 (1092181303630233 / 8000000000000)) (orderedInterval (-54450081963 / 1000000000000) (-54450017996 / 1000000000000), orderedInterval (41409699380 / 1000000000000) (41409763347 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 77 12 (1938094889242797 / 8000000000000)) (orderedInterval (-46666101823 / 1000000000000) (-46666101822 / 1000000000000), orderedInterval (-21118964427 / 1000000000000) (-21118964426 / 1000000000000))) = true
  norm_num [besselStateAtRationalPoint, besselIntervalStepZero,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, besselZeroTransition,
    besselInitial, besselGridStateAt, besselGridStateBlock00, besselGridStateBlock01,
    besselGridStateBlock02, besselGridStateBlock03, besselGridStateBlock04,
    besselGridStateBlock05, besselGridStateBlock06, besselGridStateBlock07,
    besselGridStateBlock08, besselGridStateBlock09, besselGridStateBlock10,
    besselGridStateBlock11, besselGridStateBlock12, besselGridStateBlock13,
    besselGridStateBlock14, besselGridState007, besselGridState010, besselGridState015, besselGridState018, besselGridState019, besselGridState025, besselGridState027, besselGridState029, besselGridState034, besselGridState036, besselGridState039, besselGridState040, besselGridState042, besselGridState043, besselGridState049, besselGridState051, besselGridState053, besselGridState058, besselGridState062, besselGridState063, besselGridState067, besselGridState072, besselGridState075, besselGridState077, besselStateSubset, linearInterval, widenInterval,
    rationalErrorInterval, rationalIntervalSubset, orderedInterval, Finset.sum_range_succ,
    IntervalRat.add, IntervalRat.mul, IntervalRat.scale, IntervalRat.singleton]

theorem compactCertificate228_stateChecks4 :
    compactCertificate228.stateChecks 12 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 72 12 (1810819648587393 / 8000000000000)) (orderedInterval (42909444022 / 1000000000000) (42909444023 / 1000000000000), orderedInterval (31070788369 / 1000000000000) (31070788370 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 51 12 (1292286345977169 / 8000000000000)) (orderedInterval (-54215796861 / 1000000000000) (-54215772346 / 1000000000000), orderedInterval (31817190940 / 1000000000000) (31817215455 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 58 12 (1465314983202951 / 8000000000000)) (orderedInterval (58145122638 / 1000000000000) (58145123204 / 1000000000000), orderedInterval (-9895617348 / 1000000000000) (-9895616782 / 1000000000000))) = true
  norm_num [besselStateAtRationalPoint, besselIntervalStepZero,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, besselZeroTransition,
    besselInitial, besselGridStateAt, besselGridStateBlock00, besselGridStateBlock01,
    besselGridStateBlock02, besselGridStateBlock03, besselGridStateBlock04,
    besselGridStateBlock05, besselGridStateBlock06, besselGridStateBlock07,
    besselGridStateBlock08, besselGridStateBlock09, besselGridStateBlock10,
    besselGridStateBlock11, besselGridStateBlock12, besselGridStateBlock13,
    besselGridStateBlock14, besselGridState007, besselGridState010, besselGridState015, besselGridState018, besselGridState019, besselGridState025, besselGridState027, besselGridState029, besselGridState034, besselGridState036, besselGridState039, besselGridState040, besselGridState042, besselGridState043, besselGridState049, besselGridState051, besselGridState053, besselGridState058, besselGridState062, besselGridState063, besselGridState067, besselGridState072, besselGridState075, besselGridState077, besselStateSubset, linearInterval, widenInterval,
    rationalErrorInterval, rationalIntervalSubset, orderedInterval, Finset.sum_range_succ,
    IntervalRat.add, IntervalRat.mul, IntervalRat.scale, IntervalRat.singleton]

theorem compactCertificate228_stateChecks5 :
    compactCertificate228.stateChecks 15 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 49 12 (1221626866228119 / 8000000000000)) (orderedInterval (28090615494 / 1000000000000) (28090617625 / 1000000000000), orderedInterval (-58229123261 / 1000000000000) (-58229121130 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 43 12 (1079344384538499 / 8000000000000)) (orderedInterval (-39578073223 / 1000000000000) (-39578073222 / 1000000000000), orderedInterval (-55997369393 / 1000000000000) (-55997369392 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 62 12 (312836072107401 / 1600000000000)) (orderedInterval (57010314103 / 1000000000000) (57010314139 / 1000000000000), orderedInterval (2263592331 / 1000000000000) (2263592367 / 1000000000000))) = true
  norm_num [besselStateAtRationalPoint, besselIntervalStepZero,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, besselZeroTransition,
    besselInitial, besselGridStateAt, besselGridStateBlock00, besselGridStateBlock01,
    besselGridStateBlock02, besselGridStateBlock03, besselGridStateBlock04,
    besselGridStateBlock05, besselGridStateBlock06, besselGridStateBlock07,
    besselGridStateBlock08, besselGridStateBlock09, besselGridStateBlock10,
    besselGridStateBlock11, besselGridStateBlock12, besselGridStateBlock13,
    besselGridStateBlock14, besselGridState007, besselGridState010, besselGridState015, besselGridState018, besselGridState019, besselGridState025, besselGridState027, besselGridState029, besselGridState034, besselGridState036, besselGridState039, besselGridState040, besselGridState042, besselGridState043, besselGridState049, besselGridState051, besselGridState053, besselGridState058, besselGridState062, besselGridState063, besselGridState067, besselGridState072, besselGridState075, besselGridState077, besselStateSubset, linearInterval, widenInterval,
    rationalErrorInterval, rationalIntervalSubset, orderedInterval, Finset.sum_range_succ,
    IntervalRat.add, IntervalRat.mul, IntervalRat.scale, IntervalRat.singleton]

theorem compactCertificate228_stateChecks6 :
    compactCertificate228.stateChecks 18 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 34 12 (865321039109547 / 8000000000000)) (orderedInterval (64818231788 / 1000000000000) (64818258523 / 1000000000000), orderedInterval (-41338597318 / 1000000000000) (-41338570583 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 29 12 (733542228021267 / 8000000000000)) (orderedInterval (-81660097326 / 1000000000000) (-81660097324 / 1000000000000), orderedInterval (-16122723191 / 1000000000000) (-16122723189 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 18 12 (459016666838001 / 8000000000000)) (orderedInterval (105244720445 / 1000000000000) (105244720490 / 1000000000000), orderedInterval (-5217727073 / 1000000000000) (-5217727028 / 1000000000000))) = true
  norm_num [besselStateAtRationalPoint, besselIntervalStepZero,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, besselZeroTransition,
    besselInitial, besselGridStateAt, besselGridStateBlock00, besselGridStateBlock01,
    besselGridStateBlock02, besselGridStateBlock03, besselGridStateBlock04,
    besselGridStateBlock05, besselGridStateBlock06, besselGridStateBlock07,
    besselGridStateBlock08, besselGridStateBlock09, besselGridStateBlock10,
    besselGridStateBlock11, besselGridStateBlock12, besselGridStateBlock13,
    besselGridStateBlock14, besselGridState007, besselGridState010, besselGridState015, besselGridState018, besselGridState019, besselGridState025, besselGridState027, besselGridState029, besselGridState034, besselGridState036, besselGridState039, besselGridState040, besselGridState042, besselGridState043, besselGridState049, besselGridState051, besselGridState053, besselGridState058, besselGridState062, besselGridState063, besselGridState067, besselGridState072, besselGridState075, besselGridState077, besselStateSubset, linearInterval, widenInterval,
    rationalErrorInterval, rationalIntervalSubset, orderedInterval, Finset.sum_range_succ,
    IntervalRat.add, IntervalRat.mul, IntervalRat.scale, IntervalRat.singleton]

theorem compactCertificate228_stateChecks7 :
    compactCertificate228.stateChecks 21 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 10 12 (246860690045967 / 8000000000000)) (orderedInterval (31764912591 / 1000000000000) (31764912592 / 1000000000000), orderedInterval (139572297414 / 1000000000000) (139572297415 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 27 12 (670274794718901 / 8000000000000)) (orderedInterval (21966180508 / 1000000000000) (21966180812 / 1000000000000), orderedInterval (-84486988233 / 1000000000000) (-84486987929 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 36 12 (915202928633877 / 8000000000000)) (orderedInterval (64865002088 / 1000000000000) (64865019639 / 1000000000000), orderedInterval (-37125644985 / 1000000000000) (-37125627434 / 1000000000000))) = true
  norm_num [besselStateAtRationalPoint, besselIntervalStepZero,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, besselZeroTransition,
    besselInitial, besselGridStateAt, besselGridStateBlock00, besselGridStateBlock01,
    besselGridStateBlock02, besselGridStateBlock03, besselGridStateBlock04,
    besselGridStateBlock05, besselGridStateBlock06, besselGridStateBlock07,
    besselGridStateBlock08, besselGridStateBlock09, besselGridStateBlock10,
    besselGridStateBlock11, besselGridStateBlock12, besselGridStateBlock13,
    besselGridStateBlock14, besselGridState007, besselGridState010, besselGridState015, besselGridState018, besselGridState019, besselGridState025, besselGridState027, besselGridState029, besselGridState034, besselGridState036, besselGridState039, besselGridState040, besselGridState042, besselGridState043, besselGridState049, besselGridState051, besselGridState053, besselGridState058, besselGridState062, besselGridState063, besselGridState067, besselGridState072, besselGridState075, besselGridState077, besselStateSubset, linearInterval, widenInterval,
    rationalErrorInterval, rationalIntervalSubset, orderedInterval, Finset.sum_range_succ,
    IntervalRat.add, IntervalRat.mul, IntervalRat.scale, IntervalRat.singleton]

theorem compactCertificate228_stateChecks8 :
    compactCertificate228.stateChecks 24 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 15 12 (386983333161999 / 8000000000000)) (orderedInterval (-102739067154 / 1000000000000) (-102739059755 / 1000000000000), orderedInterval (52100304548 / 1000000000000) (52100311948 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 63 12 (1573065764631279 / 8000000000000)) (orderedInterval (27396702546 / 1000000000000) (27396705523 / 1000000000000), orderedInterval (-49939761823 / 1000000000000) (-49939758846 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 42 12 (1050735028513761 / 8000000000000)) (orderedInterval (12425322348 / 1000000000000) (12425322349 / 1000000000000), orderedInterval (68455892922 / 1000000000000) (68455892923 / 1000000000000))) = true
  norm_num [besselStateAtRationalPoint, besselIntervalStepZero,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, besselZeroTransition,
    besselInitial, besselGridStateAt, besselGridStateBlock00, besselGridStateBlock01,
    besselGridStateBlock02, besselGridStateBlock03, besselGridStateBlock04,
    besselGridStateBlock05, besselGridStateBlock06, besselGridStateBlock07,
    besselGridStateBlock08, besselGridStateBlock09, besselGridStateBlock10,
    besselGridStateBlock11, besselGridStateBlock12, besselGridStateBlock13,
    besselGridStateBlock14, besselGridState007, besselGridState010, besselGridState015, besselGridState018, besselGridState019, besselGridState025, besselGridState027, besselGridState029, besselGridState034, besselGridState036, besselGridState039, besselGridState040, besselGridState042, besselGridState043, besselGridState049, besselGridState051, besselGridState053, besselGridState058, besselGridState062, besselGridState063, besselGridState067, besselGridState072, besselGridState075, besselGridState077, besselStateSubset, linearInterval, widenInterval,
    rationalErrorInterval, rationalIntervalSubset, orderedInterval, Finset.sum_range_succ,
    IntervalRat.add, IntervalRat.mul, IntervalRat.scale, IntervalRat.singleton]

theorem compactCertificate228_states : ∀ j,
    BesselStateValid (compactCertificate228.point j) (compactCertificate228.state j) :=
  compactCertificate228.statesValid_of_checks3 compactCertificate228_stateChecks0
    compactCertificate228_stateChecks1 compactCertificate228_stateChecks2
    compactCertificate228_stateChecks3 compactCertificate228_stateChecks4
    compactCertificate228_stateChecks5 compactCertificate228_stateChecks6
    compactCertificate228_stateChecks7 compactCertificate228_stateChecks8

theorem compactCertificate228_chunkChecks0_0 :
    compactCertificate228.chunkChecks (0 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 0) <| besselDerivativeNearFromState (423 / 4) 0 (IntervalRat.scale (423 / 4) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-21437106172 / 1000000000000) (-21437105805 / 1000000000000), orderedInterval (74670468084 / 1000000000000) (74670468451 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 0) <| besselDerivativeNearFromState (623159770962123 / 8000000000000) 0 (IntervalRat.scale (423 / 4) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-12520933453 / 1000000000000) (-12520933452 / 1000000000000), orderedInterval (-89452782357 / 1000000000000) (-89452782356 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 0) <| besselDerivativeNearFromState (201517066303659 / 1600000000000) 0 (IntervalRat.scale (423 / 4) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (62326305255 / 1000000000000) (62326305256 / 1000000000000), orderedInterval (33958240476 / 1000000000000) (33958240477 / 1000000000000)))) (orderedInterval (-4956210607 / 1000000000000) (-4956210453 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 0) <| besselDerivativeNearFromState (181836466984161 / 8000000000000) 0 (IntervalRat.scale (423 / 4) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-167106677261 / 1000000000000) (-167106677252 / 1000000000000), orderedInterval (-5106112297 / 1000000000000) (-5106112289 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 0) <| besselDerivativeNearFromState (488438327734317 / 8000000000000) 0 (IntervalRat.scale (423 / 4) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-85574863635 / 1000000000000) (-85574839348 / 1000000000000), orderedInterval (56412746558 / 1000000000000) (56412770845 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 0) <| besselDerivativeNearFromState (1326205074584889 / 8000000000000) 0 (IntervalRat.scale (423 / 4) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-3460306576 / 1000000000000) (-3460306574 / 1000000000000), orderedInterval (-61862764269 / 1000000000000) (-61862764267 / 1000000000000)))) (orderedInterval (-1065506770 / 1000000000000) (-1065505870 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 0) <| besselDerivativeNearFromState (976876655469057 / 8000000000000) 0 (IntervalRat.scale (423 / 4) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-26234228550 / 1000000000000) (-26234228549 / 1000000000000), orderedInterval (-67163001123 / 1000000000000) (-67163001122 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 0) <| besselDerivativeNearFromState (1673894799475461 / 8000000000000) 0 (IntervalRat.scale (423 / 4) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (24737593392 / 1000000000000) (24737595221 / 1000000000000), orderedInterval (-49360597385 / 1000000000000) (-49360595556 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 0) <| besselDerivativeNearFromState (1232983333161999 / 8000000000000) 0 (IntervalRat.scale (423 / 4) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-52995549663 / 1000000000000) (-52995549662 / 1000000000000), orderedInterval (-36188241155 / 1000000000000) (-36188241154 / 1000000000000)))) (orderedInterval (-2043804290 / 1000000000000) (-2043804227 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate228_chunkChecks0_1 :
    compactCertificate228.chunkChecks (0 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 0) <| besselDerivativeNearFromState (1891713508964577 / 8000000000000) 0 (IntervalRat.scale (423 / 4) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-51797089036 / 1000000000000) (-51797088835 / 1000000000000), orderedInterval (3159380582 / 1000000000000) (3159380783 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 0) <| besselDerivativeNearFromState (1092181303630233 / 8000000000000) 0 (IntervalRat.scale (423 / 4) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-54450081963 / 1000000000000) (-54450017996 / 1000000000000), orderedInterval (41409699380 / 1000000000000) (41409763347 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 0) <| besselDerivativeNearFromState (1938094889242797 / 8000000000000) 0 (IntervalRat.scale (423 / 4) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-46666101823 / 1000000000000) (-46666101822 / 1000000000000), orderedInterval (-21118964427 / 1000000000000) (-21118964426 / 1000000000000)))) (orderedInterval (-1464447068 / 1000000000000) (-1464442250 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 0) <| besselDerivativeNearFromState (1810819648587393 / 8000000000000) 0 (IntervalRat.scale (423 / 4) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (42909444022 / 1000000000000) (42909444023 / 1000000000000), orderedInterval (31070788369 / 1000000000000) (31070788370 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 0) <| besselDerivativeNearFromState (1292286345977169 / 8000000000000) 0 (IntervalRat.scale (423 / 4) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-54215796861 / 1000000000000) (-54215772346 / 1000000000000), orderedInterval (31817190940 / 1000000000000) (31817215455 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 0) <| besselDerivativeNearFromState (1465314983202951 / 8000000000000) 0 (IntervalRat.scale (423 / 4) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (58145122638 / 1000000000000) (58145123204 / 1000000000000), orderedInterval (-9895617348 / 1000000000000) (-9895616782 / 1000000000000)))) (orderedInterval (-6195696839 / 1000000000000) (-6195694504 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 0) <| besselDerivativeNearFromState (1221626866228119 / 8000000000000) 0 (IntervalRat.scale (423 / 4) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (28090615494 / 1000000000000) (28090617625 / 1000000000000), orderedInterval (-58229123261 / 1000000000000) (-58229121130 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 0) <| besselDerivativeNearFromState (1079344384538499 / 8000000000000) 0 (IntervalRat.scale (423 / 4) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-39578073223 / 1000000000000) (-39578073222 / 1000000000000), orderedInterval (-55997369393 / 1000000000000) (-55997369392 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 0) <| besselDerivativeNearFromState (312836072107401 / 1600000000000) 0 (IntervalRat.scale (423 / 4) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (57010314103 / 1000000000000) (57010314139 / 1000000000000), orderedInterval (2263592331 / 1000000000000) (2263592367 / 1000000000000)))) (orderedInterval (4048991997 / 1000000000000) (4048992033 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate228_chunkChecks0_2 :
    compactCertificate228.chunkChecks (0 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 0) <| besselDerivativeNearFromState (865321039109547 / 8000000000000) 0 (IntervalRat.scale (423 / 4) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (64818231788 / 1000000000000) (64818258523 / 1000000000000), orderedInterval (-41338597318 / 1000000000000) (-41338570583 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 0) <| besselDerivativeNearFromState (733542228021267 / 8000000000000) 0 (IntervalRat.scale (423 / 4) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-81660097326 / 1000000000000) (-81660097324 / 1000000000000), orderedInterval (-16122723191 / 1000000000000) (-16122723189 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 0) <| besselDerivativeNearFromState (459016666838001 / 8000000000000) 0 (IntervalRat.scale (423 / 4) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (105244720445 / 1000000000000) (105244720490 / 1000000000000), orderedInterval (-5217727073 / 1000000000000) (-5217727028 / 1000000000000)))) (orderedInterval (-2315721344 / 1000000000000) (-2315717041 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 0) <| besselDerivativeNearFromState (246860690045967 / 8000000000000) 0 (IntervalRat.scale (423 / 4) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (31764912591 / 1000000000000) (31764912592 / 1000000000000), orderedInterval (139572297414 / 1000000000000) (139572297415 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 0) <| besselDerivativeNearFromState (670274794718901 / 8000000000000) 0 (IntervalRat.scale (423 / 4) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (21966180508 / 1000000000000) (21966180812 / 1000000000000), orderedInterval (-84486988233 / 1000000000000) (-84486987929 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 0) <| besselDerivativeNearFromState (915202928633877 / 8000000000000) 0 (IntervalRat.scale (423 / 4) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (64865002088 / 1000000000000) (64865019639 / 1000000000000), orderedInterval (-37125644985 / 1000000000000) (-37125627434 / 1000000000000)))) (orderedInterval (-6056068355 / 1000000000000) (-6056066989 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 0) <| besselDerivativeNearFromState (386983333161999 / 8000000000000) 0 (IntervalRat.scale (423 / 4) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-102739067154 / 1000000000000) (-102739059755 / 1000000000000), orderedInterval (52100304548 / 1000000000000) (52100311948 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 0) <| besselDerivativeNearFromState (1573065764631279 / 8000000000000) 0 (IntervalRat.scale (423 / 4) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (27396702546 / 1000000000000) (27396705523 / 1000000000000), orderedInterval (-49939761823 / 1000000000000) (-49939758846 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 0) <| besselDerivativeNearFromState (1050735028513761 / 8000000000000) 0 (IntervalRat.scale (423 / 4) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (12425322348 / 1000000000000) (12425322349 / 1000000000000), orderedInterval (68455892922 / 1000000000000) (68455892923 / 1000000000000)))) (orderedInterval (-5180805403 / 1000000000000) (-5180805086 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate228_chunkChecks0 :
    compactCertificate228.chunkChecks (0 : Fin 5) 0 9 = true :=
  compactCertificate228.chunkChecks_nine_of_three (0 : Fin 5) compactCertificate228_chunkChecks0_0
    compactCertificate228_chunkChecks0_1 compactCertificate228_chunkChecks0_2

theorem compactCertificate228_chunkChecks1_0 :
    compactCertificate228.chunkChecks (1 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 1) <| besselDerivativeNearFromState (423 / 4) 1 (IntervalRat.scale (423 / 4) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-21437106172 / 1000000000000) (-21437105805 / 1000000000000), orderedInterval (74670468084 / 1000000000000) (74670468451 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 1) <| besselDerivativeNearFromState (623159770962123 / 8000000000000) 1 (IntervalRat.scale (423 / 4) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-12520933453 / 1000000000000) (-12520933452 / 1000000000000), orderedInterval (-89452782357 / 1000000000000) (-89452782356 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 1) <| besselDerivativeNearFromState (201517066303659 / 1600000000000) 1 (IntervalRat.scale (423 / 4) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (62326305255 / 1000000000000) (62326305256 / 1000000000000), orderedInterval (33958240476 / 1000000000000) (33958240477 / 1000000000000)))) (orderedInterval (31356101754 / 1000000000000) (31356101908 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 1) <| besselDerivativeNearFromState (181836466984161 / 8000000000000) 1 (IntervalRat.scale (423 / 4) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-167106677261 / 1000000000000) (-167106677252 / 1000000000000), orderedInterval (-5106112297 / 1000000000000) (-5106112289 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 1) <| besselDerivativeNearFromState (488438327734317 / 8000000000000) 1 (IntervalRat.scale (423 / 4) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-85574863635 / 1000000000000) (-85574839348 / 1000000000000), orderedInterval (56412746558 / 1000000000000) (56412770845 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 1) <| besselDerivativeNearFromState (1326205074584889 / 8000000000000) 1 (IntervalRat.scale (423 / 4) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-3460306576 / 1000000000000) (-3460306574 / 1000000000000), orderedInterval (-61862764269 / 1000000000000) (-61862764267 / 1000000000000)))) (orderedInterval (8095165826 / 1000000000000) (8095166354 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 1) <| besselDerivativeNearFromState (976876655469057 / 8000000000000) 1 (IntervalRat.scale (423 / 4) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-26234228550 / 1000000000000) (-26234228549 / 1000000000000), orderedInterval (-67163001123 / 1000000000000) (-67163001122 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 1) <| besselDerivativeNearFromState (1673894799475461 / 8000000000000) 1 (IntervalRat.scale (423 / 4) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (24737593392 / 1000000000000) (24737595221 / 1000000000000), orderedInterval (-49360597385 / 1000000000000) (-49360595556 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 1) <| besselDerivativeNearFromState (1232983333161999 / 8000000000000) 1 (IntervalRat.scale (423 / 4) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-52995549663 / 1000000000000) (-52995549662 / 1000000000000), orderedInterval (-36188241155 / 1000000000000) (-36188241154 / 1000000000000)))) (orderedInterval (1737710635 / 1000000000000) (1737710758 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate228_chunkChecks1_1 :
    compactCertificate228.chunkChecks (1 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 1) <| besselDerivativeNearFromState (1891713508964577 / 8000000000000) 1 (IntervalRat.scale (423 / 4) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-51797089036 / 1000000000000) (-51797088835 / 1000000000000), orderedInterval (3159380582 / 1000000000000) (3159380783 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 1) <| besselDerivativeNearFromState (1092181303630233 / 8000000000000) 1 (IntervalRat.scale (423 / 4) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-54450081963 / 1000000000000) (-54450017996 / 1000000000000), orderedInterval (41409699380 / 1000000000000) (41409763347 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 1) <| besselDerivativeNearFromState (1938094889242797 / 8000000000000) 1 (IntervalRat.scale (423 / 4) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-46666101823 / 1000000000000) (-46666101822 / 1000000000000), orderedInterval (-21118964427 / 1000000000000) (-21118964426 / 1000000000000)))) (orderedInterval (-4172052195 / 1000000000000) (-4172045909 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 1) <| besselDerivativeNearFromState (1810819648587393 / 8000000000000) 1 (IntervalRat.scale (423 / 4) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (42909444022 / 1000000000000) (42909444023 / 1000000000000), orderedInterval (31070788369 / 1000000000000) (31070788370 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 1) <| besselDerivativeNearFromState (1292286345977169 / 8000000000000) 1 (IntervalRat.scale (423 / 4) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-54215796861 / 1000000000000) (-54215772346 / 1000000000000), orderedInterval (31817190940 / 1000000000000) (31817215455 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 1) <| besselDerivativeNearFromState (1465314983202951 / 8000000000000) 1 (IntervalRat.scale (423 / 4) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (58145122638 / 1000000000000) (58145123204 / 1000000000000), orderedInterval (-9895617348 / 1000000000000) (-9895616782 / 1000000000000)))) (orderedInterval (3482011537 / 1000000000000) (3482015105 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 1) <| besselDerivativeNearFromState (1221626866228119 / 8000000000000) 1 (IntervalRat.scale (423 / 4) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (28090615494 / 1000000000000) (28090617625 / 1000000000000), orderedInterval (-58229123261 / 1000000000000) (-58229121130 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 1) <| besselDerivativeNearFromState (1079344384538499 / 8000000000000) 1 (IntervalRat.scale (423 / 4) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-39578073223 / 1000000000000) (-39578073222 / 1000000000000), orderedInterval (-55997369393 / 1000000000000) (-55997369392 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 1) <| besselDerivativeNearFromState (312836072107401 / 1600000000000) 1 (IntervalRat.scale (423 / 4) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (57010314103 / 1000000000000) (57010314139 / 1000000000000), orderedInterval (2263592331 / 1000000000000) (2263592367 / 1000000000000)))) (orderedInterval (3224616977 / 1000000000000) (3224617030 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate228_chunkChecks1_2 :
    compactCertificate228.chunkChecks (1 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 1) <| besselDerivativeNearFromState (865321039109547 / 8000000000000) 1 (IntervalRat.scale (423 / 4) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (64818231788 / 1000000000000) (64818258523 / 1000000000000), orderedInterval (-41338597318 / 1000000000000) (-41338570583 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 1) <| besselDerivativeNearFromState (733542228021267 / 8000000000000) 1 (IntervalRat.scale (423 / 4) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-81660097326 / 1000000000000) (-81660097324 / 1000000000000), orderedInterval (-16122723191 / 1000000000000) (-16122723189 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 1) <| besselDerivativeNearFromState (459016666838001 / 8000000000000) 1 (IntervalRat.scale (423 / 4) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (105244720445 / 1000000000000) (105244720490 / 1000000000000), orderedInterval (-5217727073 / 1000000000000) (-5217727028 / 1000000000000)))) (orderedInterval (7459756562 / 1000000000000) (7459760961 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 1) <| besselDerivativeNearFromState (246860690045967 / 8000000000000) 1 (IntervalRat.scale (423 / 4) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (31764912591 / 1000000000000) (31764912592 / 1000000000000), orderedInterval (139572297414 / 1000000000000) (139572297415 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 1) <| besselDerivativeNearFromState (670274794718901 / 8000000000000) 1 (IntervalRat.scale (423 / 4) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (21966180508 / 1000000000000) (21966180812 / 1000000000000), orderedInterval (-84486988233 / 1000000000000) (-84486987929 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 1) <| besselDerivativeNearFromState (915202928633877 / 8000000000000) 1 (IntervalRat.scale (423 / 4) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (64865002088 / 1000000000000) (64865019639 / 1000000000000), orderedInterval (-37125644985 / 1000000000000) (-37125627434 / 1000000000000)))) (orderedInterval (3844595153 / 1000000000000) (3844596626 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 1) <| besselDerivativeNearFromState (386983333161999 / 8000000000000) 1 (IntervalRat.scale (423 / 4) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-102739067154 / 1000000000000) (-102739059755 / 1000000000000), orderedInterval (52100304548 / 1000000000000) (52100311948 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 1) <| besselDerivativeNearFromState (1573065764631279 / 8000000000000) 1 (IntervalRat.scale (423 / 4) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (27396702546 / 1000000000000) (27396705523 / 1000000000000), orderedInterval (-49939761823 / 1000000000000) (-49939758846 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 1) <| besselDerivativeNearFromState (1050735028513761 / 8000000000000) 1 (IntervalRat.scale (423 / 4) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (12425322348 / 1000000000000) (12425322349 / 1000000000000), orderedInterval (68455892922 / 1000000000000) (68455892923 / 1000000000000)))) (orderedInterval (-8249932587 / 1000000000000) (-8249932074 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate228_chunkChecks1 :
    compactCertificate228.chunkChecks (1 : Fin 5) 0 9 = true :=
  compactCertificate228.chunkChecks_nine_of_three (1 : Fin 5) compactCertificate228_chunkChecks1_0
    compactCertificate228_chunkChecks1_1 compactCertificate228_chunkChecks1_2

theorem compactCertificate228_chunkChecks2_0 :
    compactCertificate228.chunkChecks (2 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 2) <| besselDerivativeNearFromState (423 / 4) 2 (IntervalRat.scale (423 / 4) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-21437106172 / 1000000000000) (-21437105805 / 1000000000000), orderedInterval (74670468084 / 1000000000000) (74670468451 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 2) <| besselDerivativeNearFromState (623159770962123 / 8000000000000) 2 (IntervalRat.scale (423 / 4) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-12520933453 / 1000000000000) (-12520933452 / 1000000000000), orderedInterval (-89452782357 / 1000000000000) (-89452782356 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 2) <| besselDerivativeNearFromState (201517066303659 / 1600000000000) 2 (IntervalRat.scale (423 / 4) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (62326305255 / 1000000000000) (62326305256 / 1000000000000), orderedInterval (33958240476 / 1000000000000) (33958240477 / 1000000000000)))) (orderedInterval (3075793871 / 1000000000000) (3075794028 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 2) <| besselDerivativeNearFromState (181836466984161 / 8000000000000) 2 (IntervalRat.scale (423 / 4) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-167106677261 / 1000000000000) (-167106677252 / 1000000000000), orderedInterval (-5106112297 / 1000000000000) (-5106112289 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 2) <| besselDerivativeNearFromState (488438327734317 / 8000000000000) 2 (IntervalRat.scale (423 / 4) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-85574863635 / 1000000000000) (-85574839348 / 1000000000000), orderedInterval (56412746558 / 1000000000000) (56412770845 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 2) <| besselDerivativeNearFromState (1326205074584889 / 8000000000000) 2 (IntervalRat.scale (423 / 4) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-3460306576 / 1000000000000) (-3460306574 / 1000000000000), orderedInterval (-61862764269 / 1000000000000) (-61862764267 / 1000000000000)))) (orderedInterval (276682169 / 1000000000000) (276682491 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 2) <| besselDerivativeNearFromState (976876655469057 / 8000000000000) 2 (IntervalRat.scale (423 / 4) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-26234228550 / 1000000000000) (-26234228549 / 1000000000000), orderedInterval (-67163001123 / 1000000000000) (-67163001122 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 2) <| besselDerivativeNearFromState (1673894799475461 / 8000000000000) 2 (IntervalRat.scale (423 / 4) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (24737593392 / 1000000000000) (24737595221 / 1000000000000), orderedInterval (-49360597385 / 1000000000000) (-49360595556 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 2) <| besselDerivativeNearFromState (1232983333161999 / 8000000000000) 2 (IntervalRat.scale (423 / 4) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-52995549663 / 1000000000000) (-52995549662 / 1000000000000), orderedInterval (-36188241155 / 1000000000000) (-36188241154 / 1000000000000)))) (orderedInterval (5691161177 / 1000000000000) (5691161418 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate228_chunkChecks2_1 :
    compactCertificate228.chunkChecks (2 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 2) <| besselDerivativeNearFromState (1891713508964577 / 8000000000000) 2 (IntervalRat.scale (423 / 4) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-51797089036 / 1000000000000) (-51797088835 / 1000000000000), orderedInterval (3159380582 / 1000000000000) (3159380783 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 2) <| besselDerivativeNearFromState (1092181303630233 / 8000000000000) 2 (IntervalRat.scale (423 / 4) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-54450081963 / 1000000000000) (-54450017996 / 1000000000000), orderedInterval (41409699380 / 1000000000000) (41409763347 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 2) <| besselDerivativeNearFromState (1938094889242797 / 8000000000000) 2 (IntervalRat.scale (423 / 4) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-46666101823 / 1000000000000) (-46666101822 / 1000000000000), orderedInterval (-21118964427 / 1000000000000) (-21118964426 / 1000000000000)))) (orderedInterval (-4439555864 / 1000000000000) (-4439547540 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 2) <| besselDerivativeNearFromState (1810819648587393 / 8000000000000) 2 (IntervalRat.scale (423 / 4) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (42909444022 / 1000000000000) (42909444023 / 1000000000000), orderedInterval (31070788369 / 1000000000000) (31070788370 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 2) <| besselDerivativeNearFromState (1292286345977169 / 8000000000000) 2 (IntervalRat.scale (423 / 4) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-54215796861 / 1000000000000) (-54215772346 / 1000000000000), orderedInterval (31817190940 / 1000000000000) (31817215455 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 2) <| besselDerivativeNearFromState (1465314983202951 / 8000000000000) 2 (IntervalRat.scale (423 / 4) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (58145122638 / 1000000000000) (58145123204 / 1000000000000), orderedInterval (-9895617348 / 1000000000000) (-9895616782 / 1000000000000)))) (orderedInterval (16361412585 / 1000000000000) (16361418071 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 2) <| besselDerivativeNearFromState (1221626866228119 / 8000000000000) 2 (IntervalRat.scale (423 / 4) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (28090615494 / 1000000000000) (28090617625 / 1000000000000), orderedInterval (-58229123261 / 1000000000000) (-58229121130 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 2) <| besselDerivativeNearFromState (1079344384538499 / 8000000000000) 2 (IntervalRat.scale (423 / 4) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-39578073223 / 1000000000000) (-39578073222 / 1000000000000), orderedInterval (-55997369393 / 1000000000000) (-55997369392 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 2) <| besselDerivativeNearFromState (312836072107401 / 1600000000000) 2 (IntervalRat.scale (423 / 4) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (57010314103 / 1000000000000) (57010314139 / 1000000000000), orderedInterval (2263592331 / 1000000000000) (2263592367 / 1000000000000)))) (orderedInterval (-9383447269 / 1000000000000) (-9383447192 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate228_chunkChecks2_2 :
    compactCertificate228.chunkChecks (2 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 2) <| besselDerivativeNearFromState (865321039109547 / 8000000000000) 2 (IntervalRat.scale (423 / 4) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (64818231788 / 1000000000000) (64818258523 / 1000000000000), orderedInterval (-41338597318 / 1000000000000) (-41338570583 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 2) <| besselDerivativeNearFromState (733542228021267 / 8000000000000) 2 (IntervalRat.scale (423 / 4) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-81660097326 / 1000000000000) (-81660097324 / 1000000000000), orderedInterval (-16122723191 / 1000000000000) (-16122723189 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 2) <| besselDerivativeNearFromState (459016666838001 / 8000000000000) 2 (IntervalRat.scale (423 / 4) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (105244720445 / 1000000000000) (105244720490 / 1000000000000), orderedInterval (-5217727073 / 1000000000000) (-5217727028 / 1000000000000)))) (orderedInterval (6288706002 / 1000000000000) (6288710540 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 2) <| besselDerivativeNearFromState (246860690045967 / 8000000000000) 2 (IntervalRat.scale (423 / 4) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (31764912591 / 1000000000000) (31764912592 / 1000000000000), orderedInterval (139572297414 / 1000000000000) (139572297415 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 2) <| besselDerivativeNearFromState (670274794718901 / 8000000000000) 2 (IntervalRat.scale (423 / 4) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (21966180508 / 1000000000000) (21966180812 / 1000000000000), orderedInterval (-84486988233 / 1000000000000) (-84486987929 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 2) <| besselDerivativeNearFromState (915202928633877 / 8000000000000) 2 (IntervalRat.scale (423 / 4) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (64865002088 / 1000000000000) (64865019639 / 1000000000000), orderedInterval (-37125644985 / 1000000000000) (-37125627434 / 1000000000000)))) (orderedInterval (6144136354 / 1000000000000) (6144137959 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 2) <| besselDerivativeNearFromState (386983333161999 / 8000000000000) 2 (IntervalRat.scale (423 / 4) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-102739067154 / 1000000000000) (-102739059755 / 1000000000000), orderedInterval (52100304548 / 1000000000000) (52100311948 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 2) <| besselDerivativeNearFromState (1573065764631279 / 8000000000000) 2 (IntervalRat.scale (423 / 4) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (27396702546 / 1000000000000) (27396705523 / 1000000000000), orderedInterval (-49939761823 / 1000000000000) (-49939758846 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 2) <| besselDerivativeNearFromState (1050735028513761 / 8000000000000) 2 (IntervalRat.scale (423 / 4) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (12425322348 / 1000000000000) (12425322349 / 1000000000000), orderedInterval (68455892922 / 1000000000000) (68455892923 / 1000000000000)))) (orderedInterval (11514383519 / 1000000000000) (11514384432 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate228_chunkChecks2 :
    compactCertificate228.chunkChecks (2 : Fin 5) 0 9 = true :=
  compactCertificate228.chunkChecks_nine_of_three (2 : Fin 5) compactCertificate228_chunkChecks2_0
    compactCertificate228_chunkChecks2_1 compactCertificate228_chunkChecks2_2

theorem compactCertificate228_chunkChecks3_0 :
    compactCertificate228.chunkChecks (3 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 3) <| besselDerivativeNearFromState (423 / 4) 3 (IntervalRat.scale (423 / 4) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-21437106172 / 1000000000000) (-21437105805 / 1000000000000), orderedInterval (74670468084 / 1000000000000) (74670468451 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 3) <| besselDerivativeNearFromState (623159770962123 / 8000000000000) 3 (IntervalRat.scale (423 / 4) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-12520933453 / 1000000000000) (-12520933452 / 1000000000000), orderedInterval (-89452782357 / 1000000000000) (-89452782356 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 3) <| besselDerivativeNearFromState (201517066303659 / 1600000000000) 3 (IntervalRat.scale (423 / 4) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (62326305255 / 1000000000000) (62326305256 / 1000000000000), orderedInterval (33958240476 / 1000000000000) (33958240477 / 1000000000000)))) (orderedInterval (-32656413206 / 1000000000000) (-32656413047 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 3) <| besselDerivativeNearFromState (181836466984161 / 8000000000000) 3 (IntervalRat.scale (423 / 4) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-167106677261 / 1000000000000) (-167106677252 / 1000000000000), orderedInterval (-5106112297 / 1000000000000) (-5106112289 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 3) <| besselDerivativeNearFromState (488438327734317 / 8000000000000) 3 (IntervalRat.scale (423 / 4) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-85574863635 / 1000000000000) (-85574839348 / 1000000000000), orderedInterval (56412746558 / 1000000000000) (56412770845 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 3) <| besselDerivativeNearFromState (1326205074584889 / 8000000000000) 3 (IntervalRat.scale (423 / 4) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-3460306576 / 1000000000000) (-3460306574 / 1000000000000), orderedInterval (-61862764269 / 1000000000000) (-61862764267 / 1000000000000)))) (orderedInterval (-17340522877 / 1000000000000) (-17340522672 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 3) <| besselDerivativeNearFromState (976876655469057 / 8000000000000) 3 (IntervalRat.scale (423 / 4) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-26234228550 / 1000000000000) (-26234228549 / 1000000000000), orderedInterval (-67163001123 / 1000000000000) (-67163001122 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 3) <| besselDerivativeNearFromState (1673894799475461 / 8000000000000) 3 (IntervalRat.scale (423 / 4) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (24737593392 / 1000000000000) (24737595221 / 1000000000000), orderedInterval (-49360597385 / 1000000000000) (-49360595556 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 3) <| besselDerivativeNearFromState (1232983333161999 / 8000000000000) 3 (IntervalRat.scale (423 / 4) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-52995549663 / 1000000000000) (-52995549662 / 1000000000000), orderedInterval (-36188241155 / 1000000000000) (-36188241154 / 1000000000000)))) (orderedInterval (-9139162818 / 1000000000000) (-9139162345 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate228_chunkChecks3_1 :
    compactCertificate228.chunkChecks (3 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 3) <| besselDerivativeNearFromState (1891713508964577 / 8000000000000) 3 (IntervalRat.scale (423 / 4) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-51797089036 / 1000000000000) (-51797088835 / 1000000000000), orderedInterval (3159380582 / 1000000000000) (3159380783 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 3) <| besselDerivativeNearFromState (1092181303630233 / 8000000000000) 3 (IntervalRat.scale (423 / 4) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-54450081963 / 1000000000000) (-54450017996 / 1000000000000), orderedInterval (41409699380 / 1000000000000) (41409763347 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 3) <| besselDerivativeNearFromState (1938094889242797 / 8000000000000) 3 (IntervalRat.scale (423 / 4) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-46666101823 / 1000000000000) (-46666101822 / 1000000000000), orderedInterval (-21118964427 / 1000000000000) (-21118964426 / 1000000000000)))) (orderedInterval (35811891247 / 1000000000000) (35811902330 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 3) <| besselDerivativeNearFromState (1810819648587393 / 8000000000000) 3 (IntervalRat.scale (423 / 4) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (42909444022 / 1000000000000) (42909444023 / 1000000000000), orderedInterval (31070788369 / 1000000000000) (31070788370 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 3) <| besselDerivativeNearFromState (1292286345977169 / 8000000000000) 3 (IntervalRat.scale (423 / 4) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-54215796861 / 1000000000000) (-54215772346 / 1000000000000), orderedInterval (31817190940 / 1000000000000) (31817215455 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 3) <| besselDerivativeNearFromState (1465314983202951 / 8000000000000) 3 (IntervalRat.scale (423 / 4) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (58145122638 / 1000000000000) (58145123204 / 1000000000000), orderedInterval (-9895617348 / 1000000000000) (-9895616782 / 1000000000000)))) (orderedInterval (-5637695504 / 1000000000000) (-5637687117 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 3) <| besselDerivativeNearFromState (1221626866228119 / 8000000000000) 3 (IntervalRat.scale (423 / 4) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (28090615494 / 1000000000000) (28090617625 / 1000000000000), orderedInterval (-58229123261 / 1000000000000) (-58229121130 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 3) <| besselDerivativeNearFromState (1079344384538499 / 8000000000000) 3 (IntervalRat.scale (423 / 4) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-39578073223 / 1000000000000) (-39578073222 / 1000000000000), orderedInterval (-55997369393 / 1000000000000) (-55997369392 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 3) <| besselDerivativeNearFromState (312836072107401 / 1600000000000) 3 (IntervalRat.scale (423 / 4) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (57010314103 / 1000000000000) (57010314139 / 1000000000000), orderedInterval (2263592331 / 1000000000000) (2263592367 / 1000000000000)))) (orderedInterval (-4907496736 / 1000000000000) (-4907496621 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate228_chunkChecks3_2 :
    compactCertificate228.chunkChecks (3 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 3) <| besselDerivativeNearFromState (865321039109547 / 8000000000000) 3 (IntervalRat.scale (423 / 4) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (64818231788 / 1000000000000) (64818258523 / 1000000000000), orderedInterval (-41338597318 / 1000000000000) (-41338570583 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 3) <| besselDerivativeNearFromState (733542228021267 / 8000000000000) 3 (IntervalRat.scale (423 / 4) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-81660097326 / 1000000000000) (-81660097324 / 1000000000000), orderedInterval (-16122723191 / 1000000000000) (-16122723189 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 3) <| besselDerivativeNearFromState (459016666838001 / 8000000000000) 3 (IntervalRat.scale (423 / 4) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (105244720445 / 1000000000000) (105244720490 / 1000000000000), orderedInterval (-5217727073 / 1000000000000) (-5217727028 / 1000000000000)))) (orderedInterval (-7699546067 / 1000000000000) (-7699541428 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 3) <| besselDerivativeNearFromState (246860690045967 / 8000000000000) 3 (IntervalRat.scale (423 / 4) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (31764912591 / 1000000000000) (31764912592 / 1000000000000), orderedInterval (139572297414 / 1000000000000) (139572297415 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 3) <| besselDerivativeNearFromState (670274794718901 / 8000000000000) 3 (IntervalRat.scale (423 / 4) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (21966180508 / 1000000000000) (21966180812 / 1000000000000), orderedInterval (-84486988233 / 1000000000000) (-84486987929 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 3) <| besselDerivativeNearFromState (915202928633877 / 8000000000000) 3 (IntervalRat.scale (423 / 4) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (64865002088 / 1000000000000) (64865019639 / 1000000000000), orderedInterval (-37125644985 / 1000000000000) (-37125627434 / 1000000000000)))) (orderedInterval (-4549156067 / 1000000000000) (-4549154333 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 3) <| besselDerivativeNearFromState (386983333161999 / 8000000000000) 3 (IntervalRat.scale (423 / 4) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-102739067154 / 1000000000000) (-102739059755 / 1000000000000), orderedInterval (52100304548 / 1000000000000) (52100311948 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 3) <| besselDerivativeNearFromState (1573065764631279 / 8000000000000) 3 (IntervalRat.scale (423 / 4) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (27396702546 / 1000000000000) (27396705523 / 1000000000000), orderedInterval (-49939761823 / 1000000000000) (-49939758846 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 3) <| besselDerivativeNearFromState (1050735028513761 / 8000000000000) 3 (IntervalRat.scale (423 / 4) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (12425322348 / 1000000000000) (12425322349 / 1000000000000), orderedInterval (68455892922 / 1000000000000) (68455892923 / 1000000000000)))) (orderedInterval (-1666076138 / 1000000000000) (-1666074473 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate228_chunkChecks3 :
    compactCertificate228.chunkChecks (3 : Fin 5) 0 9 = true :=
  compactCertificate228.chunkChecks_nine_of_three (3 : Fin 5) compactCertificate228_chunkChecks3_0
    compactCertificate228_chunkChecks3_1 compactCertificate228_chunkChecks3_2

theorem compactCertificate228_chunkChecks4_0 :
    compactCertificate228.chunkChecks (4 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 4) <| besselDerivativeNearFromState (423 / 4) 4 (IntervalRat.scale (423 / 4) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-21437106172 / 1000000000000) (-21437105805 / 1000000000000), orderedInterval (74670468084 / 1000000000000) (74670468451 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 4) <| besselDerivativeNearFromState (623159770962123 / 8000000000000) 4 (IntervalRat.scale (423 / 4) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-12520933453 / 1000000000000) (-12520933452 / 1000000000000), orderedInterval (-89452782357 / 1000000000000) (-89452782356 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 4) <| besselDerivativeNearFromState (201517066303659 / 1600000000000) 4 (IntervalRat.scale (423 / 4) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (62326305255 / 1000000000000) (62326305256 / 1000000000000), orderedInterval (33958240476 / 1000000000000) (33958240477 / 1000000000000)))) (orderedInterval (-554451295 / 1000000000000) (-554451133 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 4) <| besselDerivativeNearFromState (181836466984161 / 8000000000000) 4 (IntervalRat.scale (423 / 4) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-167106677261 / 1000000000000) (-167106677252 / 1000000000000), orderedInterval (-5106112297 / 1000000000000) (-5106112289 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 4) <| besselDerivativeNearFromState (488438327734317 / 8000000000000) 4 (IntervalRat.scale (423 / 4) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-85574863635 / 1000000000000) (-85574839348 / 1000000000000), orderedInterval (56412746558 / 1000000000000) (56412770845 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 4) <| besselDerivativeNearFromState (1326205074584889 / 8000000000000) 4 (IntervalRat.scale (423 / 4) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-3460306576 / 1000000000000) (-3460306574 / 1000000000000), orderedInterval (-61862764269 / 1000000000000) (-61862764267 / 1000000000000)))) (orderedInterval (1470207673 / 1000000000000) (1470207823 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 4) <| besselDerivativeNearFromState (976876655469057 / 8000000000000) 4 (IntervalRat.scale (423 / 4) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-26234228550 / 1000000000000) (-26234228549 / 1000000000000), orderedInterval (-67163001123 / 1000000000000) (-67163001122 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 4) <| besselDerivativeNearFromState (1673894799475461 / 8000000000000) 4 (IntervalRat.scale (423 / 4) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (24737593392 / 1000000000000) (24737595221 / 1000000000000), orderedInterval (-49360597385 / 1000000000000) (-49360595556 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 4) <| besselDerivativeNearFromState (1232983333161999 / 8000000000000) 4 (IntervalRat.scale (423 / 4) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-52995549663 / 1000000000000) (-52995549662 / 1000000000000), orderedInterval (-36188241155 / 1000000000000) (-36188241154 / 1000000000000)))) (orderedInterval (-17299218929 / 1000000000000) (-17299217994 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate228_chunkChecks4_1 :
    compactCertificate228.chunkChecks (4 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 4) <| besselDerivativeNearFromState (1891713508964577 / 8000000000000) 4 (IntervalRat.scale (423 / 4) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-51797089036 / 1000000000000) (-51797088835 / 1000000000000), orderedInterval (3159380582 / 1000000000000) (3159380783 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 4) <| besselDerivativeNearFromState (1092181303630233 / 8000000000000) 4 (IntervalRat.scale (423 / 4) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-54450081963 / 1000000000000) (-54450017996 / 1000000000000), orderedInterval (41409699380 / 1000000000000) (41409763347 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 4) <| besselDerivativeNearFromState (1938094889242797 / 8000000000000) 4 (IntervalRat.scale (423 / 4) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-46666101823 / 1000000000000) (-46666101822 / 1000000000000), orderedInterval (-21118964427 / 1000000000000) (-21118964426 / 1000000000000)))) (orderedInterval (35489269944 / 1000000000000) (35489285111 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 4) <| besselDerivativeNearFromState (1810819648587393 / 8000000000000) 4 (IntervalRat.scale (423 / 4) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (42909444022 / 1000000000000) (42909444023 / 1000000000000), orderedInterval (31070788369 / 1000000000000) (31070788370 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 4) <| besselDerivativeNearFromState (1292286345977169 / 8000000000000) 4 (IntervalRat.scale (423 / 4) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-54215796861 / 1000000000000) (-54215772346 / 1000000000000), orderedInterval (31817190940 / 1000000000000) (31817215455 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 4) <| besselDerivativeNearFromState (1465314983202951 / 8000000000000) 4 (IntervalRat.scale (423 / 4) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (58145122638 / 1000000000000) (58145123204 / 1000000000000), orderedInterval (-9895617348 / 1000000000000) (-9895616782 / 1000000000000)))) (orderedInterval (-46712848786 / 1000000000000) (-46712835883 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 4) <| besselDerivativeNearFromState (1221626866228119 / 8000000000000) 4 (IntervalRat.scale (423 / 4) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (28090615494 / 1000000000000) (28090617625 / 1000000000000), orderedInterval (-58229123261 / 1000000000000) (-58229121130 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 4) <| besselDerivativeNearFromState (1079344384538499 / 8000000000000) 4 (IntervalRat.scale (423 / 4) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-39578073223 / 1000000000000) (-39578073222 / 1000000000000), orderedInterval (-55997369393 / 1000000000000) (-55997369392 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 4) <| besselDerivativeNearFromState (312836072107401 / 1600000000000) 4 (IntervalRat.scale (423 / 4) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (57010314103 / 1000000000000) (57010314139 / 1000000000000), orderedInterval (2263592331 / 1000000000000) (2263592367 / 1000000000000)))) (orderedInterval (24561091571 / 1000000000000) (24561091744 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate228_chunkChecks4_2 :
    compactCertificate228.chunkChecks (4 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 4) <| besselDerivativeNearFromState (865321039109547 / 8000000000000) 4 (IntervalRat.scale (423 / 4) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (64818231788 / 1000000000000) (64818258523 / 1000000000000), orderedInterval (-41338597318 / 1000000000000) (-41338570583 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 4) <| besselDerivativeNearFromState (733542228021267 / 8000000000000) 4 (IntervalRat.scale (423 / 4) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-81660097326 / 1000000000000) (-81660097324 / 1000000000000), orderedInterval (-16122723191 / 1000000000000) (-16122723189 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 4) <| besselDerivativeNearFromState (459016666838001 / 8000000000000) 4 (IntervalRat.scale (423 / 4) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (105244720445 / 1000000000000) (105244720490 / 1000000000000), orderedInterval (-5217727073 / 1000000000000) (-5217727028 / 1000000000000)))) (orderedInterval (-8288116094 / 1000000000000) (-8288111307 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 4) <| besselDerivativeNearFromState (246860690045967 / 8000000000000) 4 (IntervalRat.scale (423 / 4) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (31764912591 / 1000000000000) (31764912592 / 1000000000000), orderedInterval (139572297414 / 1000000000000) (139572297415 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 4) <| besselDerivativeNearFromState (670274794718901 / 8000000000000) 4 (IntervalRat.scale (423 / 4) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (21966180508 / 1000000000000) (21966180812 / 1000000000000), orderedInterval (-84486988233 / 1000000000000) (-84486987929 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 4) <| besselDerivativeNearFromState (915202928633877 / 8000000000000) 4 (IntervalRat.scale (423 / 4) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (64865002088 / 1000000000000) (64865019639 / 1000000000000), orderedInterval (-37125644985 / 1000000000000) (-37125627434 / 1000000000000)))) (orderedInterval (-6922475782 / 1000000000000) (-6922473893 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 4) <| besselDerivativeNearFromState (386983333161999 / 8000000000000) 4 (IntervalRat.scale (423 / 4) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-102739067154 / 1000000000000) (-102739059755 / 1000000000000), orderedInterval (52100304548 / 1000000000000) (52100311948 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 4) <| besselDerivativeNearFromState (1573065764631279 / 8000000000000) 4 (IntervalRat.scale (423 / 4) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (27396702546 / 1000000000000) (27396705523 / 1000000000000), orderedInterval (-49939761823 / 1000000000000) (-49939758846 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 4) <| besselDerivativeNearFromState (1050735028513761 / 8000000000000) 4 (IntervalRat.scale (423 / 4) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (12425322348 / 1000000000000) (12425322349 / 1000000000000), orderedInterval (68455892922 / 1000000000000) (68455892923 / 1000000000000)))) (orderedInterval (-32200676729 / 1000000000000) (-32200673649 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate228_chunkChecks4 :
    compactCertificate228.chunkChecks (4 : Fin 5) 0 9 = true :=
  compactCertificate228.chunkChecks_nine_of_three (4 : Fin 5) compactCertificate228_chunkChecks4_0
    compactCertificate228_chunkChecks4_1 compactCertificate228_chunkChecks4_2

theorem compactCertificate228_chunks :
    ∀ r : Fin 5, ∀ b, compactCertificate228.chunkCheck r b = true :=
  compactCertificate228.chunkChecks_all (by
    intro r
    fin_cases r
    · exact compactCertificate228_chunkChecks0
    · exact compactCertificate228_chunkChecks1
    · exact compactCertificate228_chunkChecks2
    · exact compactCertificate228_chunkChecks3
    · exact compactCertificate228_chunkChecks4)

theorem compactCertificate228_coefficient0 :
    compactCertificate228.coefficientCheck (0 : Fin 5) = true := by
  norm_num [CompactCertificate.coefficientCheck, intervalFinSumHull,
    compactCertificate228, rationalIntervalSubset, orderedInterval, Fin.sum_univ_succ]

theorem compactCertificate228_coefficient1 :
    compactCertificate228.coefficientCheck (1 : Fin 5) = true := by
  norm_num [CompactCertificate.coefficientCheck, intervalFinSumHull,
    compactCertificate228, rationalIntervalSubset, orderedInterval, Fin.sum_univ_succ]

theorem compactCertificate228_coefficient2 :
    compactCertificate228.coefficientCheck (2 : Fin 5) = true := by
  norm_num [CompactCertificate.coefficientCheck, intervalFinSumHull,
    compactCertificate228, rationalIntervalSubset, orderedInterval, Fin.sum_univ_succ]

theorem compactCertificate228_coefficient3 :
    compactCertificate228.coefficientCheck (3 : Fin 5) = true := by
  norm_num [CompactCertificate.coefficientCheck, intervalFinSumHull,
    compactCertificate228, rationalIntervalSubset, orderedInterval, Fin.sum_univ_succ]

theorem compactCertificate228_coefficient4 :
    compactCertificate228.coefficientCheck (4 : Fin 5) = true := by
  norm_num [CompactCertificate.coefficientCheck, intervalFinSumHull,
    compactCertificate228, rationalIntervalSubset, orderedInterval, Fin.sum_univ_succ]

theorem compactCertificate228_coefficients : ∀ r : Fin 5,
    compactCertificate228.coefficientCheck r = true := by
  intro r
  fin_cases r
  · exact compactCertificate228_coefficient0
  · exact compactCertificate228_coefficient1
  · exact compactCertificate228_coefficient2
  · exact compactCertificate228_coefficient3
  · exact compactCertificate228_coefficient4

theorem compactCertificate228_lower : (1 : ℚ) ≤ compactCertificate228.output.lo := by
  norm_num [CompactCertificate.output, CompactCertificate.interval,
    CompactCertificate.coefficientTargetNat, compactCertificate228, dualConstant,
    intervalTaylorSum, intervalPow, intervalSub, intervalMaxAbs, widenInterval,
    rationalErrorInterval, orderedInterval, IntervalRat.add, IntervalRat.mul, IntervalRat.scale,
    IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4]

theorem compactCertificate228_proves {t : ℝ} (ht : t ∈ compactCertificate228.interval) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t :=
  compactCertificate228.proves compactCertificate228_states compactCertificate228_chunks
    compactCertificate228_coefficients compactCertificate228_lower ht

end Erdos232
