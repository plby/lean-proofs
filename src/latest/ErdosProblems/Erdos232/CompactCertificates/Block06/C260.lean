/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, OpenAI Codex
-/
import ErdosProblems.Erdos232.CompactBase

open LeanCert.Core
namespace Erdos232

def compactCertificate260 : CompactCertificate where
  left := 135
  right := 271 / 2
  center := 541 / 4
  grid := fun i =>
    match i.val with
    | 0 => 43
    | 1 => 32
    | 2 => 51
    | 3 => 9
    | 4 => 25
    | 5 => 68
    | 6 => 50
    | 7 => 85
    | 8 => 63
    | 9 => 96
    | 10 => 56
    | 11 => 99
    | 12 => 92
    | 13 => 66
    | 14 => 75
    | 15 => 62
    | 16 => 55
    | 17 => 80
    | 18 => 44
    | 19 => 37
    | 20 => 23
    | 21 => 13
    | 22 => 34
    | 23 => 47
    | 24 => 20
    | 25 => 80
    | _ => 53
  point := fun i =>
    match i.val with
    | 0 => 541 / 4
    | 1 => 796996302814441 / 8000000000000
    | 2 => 257732229007753 / 1600000000000
    | 3 => 232561533424187 / 8000000000000
    | 4 => 624692991263039 / 8000000000000
    | 5 => 1696162991372163 / 8000000000000
    | 6 => 1249385982526619 / 8000000000000
    | 7 => 2140844176161287 / 8000000000000
    | 8 => 1576936130592533 / 8000000000000
    | 9 => 2419425551654459 / 8000000000000
    | 10 => 1396855993531811 / 8000000000000
    | 11 => 2478745473003199 / 8000000000000
    | 12 => 2315965555285531 / 8000000000000
    | 13 => 1652782300646923 / 8000000000000
    | 14 => 1874078973789117 / 8000000000000
    | 15 => 1562411665790573 / 8000000000000
    | 16 => 1380438089918033 / 8000000000000
    | 17 => 400104763617267 / 1600000000000
    | 18 => 1106710832525449 / 8000000000000
    | 19 => 938171029218689 / 8000000000000
    | 20 => 587063869407467 / 8000000000000
    | 21 => 315724901453589 / 8000000000000
    | 22 => 857254524687767 / 8000000000000
    | 23 => 1170507764517559 / 8000000000000
    | 24 => 494936130592533 / 8000000000000
    | 25 => 2011887892826293 / 8000000000000
    | _ => 1343847873347387 / 8000000000000
  state := fun i =>
    match i.val with
    | 0 => (orderedInterval (-55645708590 / 1000000000000) (-55645708589 / 1000000000000), orderedInterval (-39925701934 / 1000000000000) (-39925701933 / 1000000000000))
    | 1 => (orderedInterval (-9750778576 / 1000000000000) (-9750778533 / 1000000000000), orderedInterval (79391175201 / 1000000000000) (79391175244 / 1000000000000))
    | 2 => (orderedInterval (-62687951495 / 1000000000000) (-62687951345 / 1000000000000), orderedInterval (4920396163 / 1000000000000) (4920396313 / 1000000000000))
    | 3 => (orderedInterval (-147970727714 / 1000000000000) (-147970727692 / 1000000000000), orderedInterval (3456300717 / 1000000000000) (3456300739 / 1000000000000))
    | 4 => (orderedInterval (-29310039922 / 1000000000000) (-29310039921 / 1000000000000), orderedInterval (-85216027071 / 1000000000000) (-85216027070 / 1000000000000))
    | 5 => (orderedInterval (-40180425613 / 1000000000000) (-40180363306 / 1000000000000), orderedInterval (37352877491 / 1000000000000) (37352939797 / 1000000000000))
    | 6 => (orderedInterval (-7756445035 / 1000000000000) (-7756445007 / 1000000000000), orderedInterval (63398539615 / 1000000000000) (63398539643 / 1000000000000))
    | 7 => (orderedInterval (-47643968570 / 1000000000000) (-47643968566 / 1000000000000), orderedInterval (-10351146577 / 1000000000000) (-10351146573 / 1000000000000))
    | 8 => (orderedInterval (1054522774 / 1000000000000) (1054522778 / 1000000000000), orderedInterval (-56823027064 / 1000000000000) (-56823027060 / 1000000000000))
    | 9 => (orderedInterval (45824380970 / 1000000000000) (45824381247 / 1000000000000), orderedInterval (-2345361464 / 1000000000000) (-2345361187 / 1000000000000))
    | 10 => (orderedInterval (-30915419889 / 1000000000000) (-30915414998 / 1000000000000), orderedInterval (51956234577 / 1000000000000) (51956239468 / 1000000000000))
    | 11 => (orderedInterval (17212046949 / 1000000000000) (17212047349 / 1000000000000), orderedInterval (-41961042364 / 1000000000000) (-41961041964 / 1000000000000))
    | 12 => (orderedInterval (44562615555 / 1000000000000) (44562615556 / 1000000000000), orderedInterval (14525615760 / 1000000000000) (14525615762 / 1000000000000))
    | 13 => (orderedInterval (2079253213 / 1000000000000) (2079253215 / 1000000000000), orderedInterval (55466861327 / 1000000000000) (55466861329 / 1000000000000))
    | 14 => (orderedInterval (28337724831 / 1000000000000) (28337730102 / 1000000000000), orderedInterval (-43816114049 / 1000000000000) (-43816108778 / 1000000000000))
    | 15 => (orderedInterval (55125478108 / 1000000000000) (55125478110 / 1000000000000), orderedInterval (14719892732 / 1000000000000) (14719892733 / 1000000000000))
    | 16 => (orderedInterval (-31843264575 / 1000000000000) (-31843264574 / 1000000000000), orderedInterval (-51631919130 / 1000000000000) (-51631919129 / 1000000000000))
    | 17 => (orderedInterval (-23166806640 / 1000000000000) (-23166804982 / 1000000000000), orderedInterval (44869465895 / 1000000000000) (44869467553 / 1000000000000))
    | 18 => (orderedInterval (52853626763 / 1000000000000) (52853626764 / 1000000000000), orderedInterval (42333961934 / 1000000000000) (42333961935 / 1000000000000))
    | 19 => (orderedInterval (-71460813118 / 1000000000000) (-71460812116 / 1000000000000), orderedInterval (18246578645 / 1000000000000) (18246579647 / 1000000000000))
    | 20 => (orderedInterval (-87831626534 / 1000000000000) (-87831624246 / 1000000000000), orderedInterval (31594448931 / 1000000000000) (31594451219 / 1000000000000))
    | 21 => (orderedInterval (70960909561 / 1000000000000) (70960926135 / 1000000000000), orderedInterval (-106236596020 / 1000000000000) (-106236579446 / 1000000000000))
    | 22 => (orderedInterval (69607481005 / 1000000000000) (69607481006 / 1000000000000), orderedInterval (32777606097 / 1000000000000) (32777606098 / 1000000000000))
    | 23 => (orderedInterval (34861567273 / 1000000000000) (34861574204 / 1000000000000), orderedInterval (-56116898336 / 1000000000000) (-56116891405 / 1000000000000))
    | 24 => (orderedInterval (-18306080970 / 1000000000000) (-18306080839 / 1000000000000), orderedInterval (99924355197 / 1000000000000) (99924355328 / 1000000000000))
    | 25 => (orderedInterval (40733791974 / 1000000000000) (40733791975 / 1000000000000), orderedInterval (29451860689 / 1000000000000) (29451860690 / 1000000000000))
    | _ => (orderedInterval (-47462191704 / 1000000000000) (-47462086765 / 1000000000000), orderedInterval (39348031238 / 1000000000000) (39348136176 / 1000000000000))
  chunkTarget := fun r b =>
    match r.val with
    | 0 =>
      match b.val with
      | 0 => orderedInterval (-25825469699 / 1000000000000) (-25825469679 / 1000000000000)
      | 1 => orderedInterval (3391624345 / 1000000000000) (3391628792 / 1000000000000)
      | 2 => orderedInterval (1495016345 / 1000000000000) (1495016353 / 1000000000000)
      | 3 => orderedInterval (-7986223615 / 1000000000000) (-7986223092 / 1000000000000)
      | 4 => orderedInterval (-751277833 / 1000000000000) (-751277790 / 1000000000000)
      | 5 => orderedInterval (1865693280 / 1000000000000) (1865693337 / 1000000000000)
      | 6 => orderedInterval (-7265599052 / 1000000000000) (-7265598886 / 1000000000000)
      | 7 => orderedInterval (-5561228781 / 1000000000000) (-5561227927 / 1000000000000)
      | _ => orderedInterval (5478988374 / 1000000000000) (5479008102 / 1000000000000)
    | 1 =>
      match b.val with
      | 0 => orderedInterval (-14936355553 / 1000000000000) (-14936355531 / 1000000000000)
      | 1 => orderedInterval (-5967084014 / 1000000000000) (-5967077051 / 1000000000000)
      | 2 => orderedInterval (-1369776459 / 1000000000000) (-1369776445 / 1000000000000)
      | 3 => orderedInterval (-7763608812 / 1000000000000) (-7763607992 / 1000000000000)
      | 4 => orderedInterval (7834792073 / 1000000000000) (7834792147 / 1000000000000)
      | 5 => orderedInterval (6139246531 / 1000000000000) (6139246629 / 1000000000000)
      | 6 => orderedInterval (-7260869679 / 1000000000000) (-7260869557 / 1000000000000)
      | 7 => orderedInterval (4635785328 / 1000000000000) (4635786007 / 1000000000000)
      | _ => orderedInterval (-13351689892 / 1000000000000) (-13351665385 / 1000000000000)
    | 2 =>
      match b.val with
      | 0 => orderedInterval (27433761242 / 1000000000000) (27433761268 / 1000000000000)
      | 1 => orderedInterval (-6692750157 / 1000000000000) (-6692739195 / 1000000000000)
      | 2 => orderedInterval (-5797004486 / 1000000000000) (-5797004461 / 1000000000000)
      | 3 => orderedInterval (31745994098 / 1000000000000) (31745995491 / 1000000000000)
      | 4 => orderedInterval (3599307298 / 1000000000000) (3599307423 / 1000000000000)
      | 5 => orderedInterval (-2311189951 / 1000000000000) (-2311189776 / 1000000000000)
      | 6 => orderedInterval (6695913278 / 1000000000000) (6695913375 / 1000000000000)
      | 7 => orderedInterval (4195296611 / 1000000000000) (4195297279 / 1000000000000)
      | _ => orderedInterval (-2150911601 / 1000000000000) (-2150880969 / 1000000000000)
    | 3 =>
      match b.val with
      | 0 => orderedInterval (14838051682 / 1000000000000) (14838051712 / 1000000000000)
      | 1 => orderedInterval (10877744871 / 1000000000000) (10877762053 / 1000000000000)
      | 2 => orderedInterval (1821080906 / 1000000000000) (1821080950 / 1000000000000)
      | 3 => orderedInterval (58540164376 / 1000000000000) (58540166921 / 1000000000000)
      | 4 => orderedInterval (-17301507441 / 1000000000000) (-17301507226 / 1000000000000)
      | 5 => orderedInterval (-13891568014 / 1000000000000) (-13891567701 / 1000000000000)
      | 6 => orderedInterval (7702352576 / 1000000000000) (7702352655 / 1000000000000)
      | 7 => orderedInterval (-5154500500 / 1000000000000) (-5154499800 / 1000000000000)
      | _ => orderedInterval (29514568906 / 1000000000000) (29514606971 / 1000000000000)
    | _ =>
      match b.val with
      | 0 => orderedInterval (-29702318643 / 1000000000000) (-29702318608 / 1000000000000)
      | 1 => orderedInterval (16972998816 / 1000000000000) (16973025875 / 1000000000000)
      | 2 => orderedInterval (22609889326 / 1000000000000) (22609889408 / 1000000000000)
      | 3 => orderedInterval (-143394419230 / 1000000000000) (-143394414237 / 1000000000000)
      | 4 => orderedInterval (-16850692112 / 1000000000000) (-16850691741 / 1000000000000)
      | 5 => orderedInterval (869391235 / 1000000000000) (869391804 / 1000000000000)
      | 6 => orderedInterval (-7324946751 / 1000000000000) (-7324946682 / 1000000000000)
      | 7 => orderedInterval (-4214477700 / 1000000000000) (-4214476944 / 1000000000000)
      | _ => orderedInterval (-18887769475 / 1000000000000) (-18887721877 / 1000000000000)
  coefficientTarget := fun i =>
    match i.val with
    | 0 => orderedInterval (-35158476636 / 1000000000000) (-35158450790 / 1000000000000)
    | 1 => orderedInterval (-32039560477 / 1000000000000) (-32039527178 / 1000000000000)
    | 2 => orderedInterval (56718416332 / 1000000000000) (56718460435 / 1000000000000)
    | 3 => orderedInterval (86946387362 / 1000000000000) (86946446535 / 1000000000000)
    | _ => orderedInterval (-179922344534 / 1000000000000) (-179922263002 / 1000000000000)

theorem compactCertificate260_stateChecks0 :
    compactCertificate260.stateChecks 0 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 43 12 (541 / 4)) (orderedInterval (-55645708590 / 1000000000000) (-55645708589 / 1000000000000), orderedInterval (-39925701934 / 1000000000000) (-39925701933 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 32 12 (796996302814441 / 8000000000000)) (orderedInterval (-9750778576 / 1000000000000) (-9750778533 / 1000000000000), orderedInterval (79391175201 / 1000000000000) (79391175244 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 51 12 (257732229007753 / 1600000000000)) (orderedInterval (-62687951495 / 1000000000000) (-62687951345 / 1000000000000), orderedInterval (4920396163 / 1000000000000) (4920396313 / 1000000000000))) = true
  norm_num [besselStateAtRationalPoint, besselIntervalStepZero,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, besselZeroTransition,
    besselInitial, besselGridStateAt, besselGridStateBlock00, besselGridStateBlock01,
    besselGridStateBlock02, besselGridStateBlock03, besselGridStateBlock04,
    besselGridStateBlock05, besselGridStateBlock06, besselGridStateBlock07,
    besselGridStateBlock08, besselGridStateBlock09, besselGridStateBlock10,
    besselGridStateBlock11, besselGridStateBlock12, besselGridStateBlock13,
    besselGridStateBlock14, besselGridState009, besselGridState013, besselGridState020, besselGridState023, besselGridState025, besselGridState032, besselGridState034, besselGridState037, besselGridState043, besselGridState044, besselGridState047, besselGridState050, besselGridState051, besselGridState053, besselGridState055, besselGridState056, besselGridState062, besselGridState063, besselGridState066, besselGridState068, besselGridState075, besselGridState080, besselGridState085, besselGridState092, besselGridState096, besselGridState099, besselStateSubset, linearInterval, widenInterval,
    rationalErrorInterval, rationalIntervalSubset, orderedInterval, Finset.sum_range_succ,
    IntervalRat.add, IntervalRat.mul, IntervalRat.scale, IntervalRat.singleton]

theorem compactCertificate260_stateChecks1 :
    compactCertificate260.stateChecks 3 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 9 12 (232561533424187 / 8000000000000)) (orderedInterval (-147970727714 / 1000000000000) (-147970727692 / 1000000000000), orderedInterval (3456300717 / 1000000000000) (3456300739 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 25 12 (624692991263039 / 8000000000000)) (orderedInterval (-29310039922 / 1000000000000) (-29310039921 / 1000000000000), orderedInterval (-85216027071 / 1000000000000) (-85216027070 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 68 12 (1696162991372163 / 8000000000000)) (orderedInterval (-40180425613 / 1000000000000) (-40180363306 / 1000000000000), orderedInterval (37352877491 / 1000000000000) (37352939797 / 1000000000000))) = true
  norm_num [besselStateAtRationalPoint, besselIntervalStepZero,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, besselZeroTransition,
    besselInitial, besselGridStateAt, besselGridStateBlock00, besselGridStateBlock01,
    besselGridStateBlock02, besselGridStateBlock03, besselGridStateBlock04,
    besselGridStateBlock05, besselGridStateBlock06, besselGridStateBlock07,
    besselGridStateBlock08, besselGridStateBlock09, besselGridStateBlock10,
    besselGridStateBlock11, besselGridStateBlock12, besselGridStateBlock13,
    besselGridStateBlock14, besselGridState009, besselGridState013, besselGridState020, besselGridState023, besselGridState025, besselGridState032, besselGridState034, besselGridState037, besselGridState043, besselGridState044, besselGridState047, besselGridState050, besselGridState051, besselGridState053, besselGridState055, besselGridState056, besselGridState062, besselGridState063, besselGridState066, besselGridState068, besselGridState075, besselGridState080, besselGridState085, besselGridState092, besselGridState096, besselGridState099, besselStateSubset, linearInterval, widenInterval,
    rationalErrorInterval, rationalIntervalSubset, orderedInterval, Finset.sum_range_succ,
    IntervalRat.add, IntervalRat.mul, IntervalRat.scale, IntervalRat.singleton]

theorem compactCertificate260_stateChecks2 :
    compactCertificate260.stateChecks 6 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 50 12 (1249385982526619 / 8000000000000)) (orderedInterval (-7756445035 / 1000000000000) (-7756445007 / 1000000000000), orderedInterval (63398539615 / 1000000000000) (63398539643 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 85 12 (2140844176161287 / 8000000000000)) (orderedInterval (-47643968570 / 1000000000000) (-47643968566 / 1000000000000), orderedInterval (-10351146577 / 1000000000000) (-10351146573 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 63 12 (1576936130592533 / 8000000000000)) (orderedInterval (1054522774 / 1000000000000) (1054522778 / 1000000000000), orderedInterval (-56823027064 / 1000000000000) (-56823027060 / 1000000000000))) = true
  norm_num [besselStateAtRationalPoint, besselIntervalStepZero,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, besselZeroTransition,
    besselInitial, besselGridStateAt, besselGridStateBlock00, besselGridStateBlock01,
    besselGridStateBlock02, besselGridStateBlock03, besselGridStateBlock04,
    besselGridStateBlock05, besselGridStateBlock06, besselGridStateBlock07,
    besselGridStateBlock08, besselGridStateBlock09, besselGridStateBlock10,
    besselGridStateBlock11, besselGridStateBlock12, besselGridStateBlock13,
    besselGridStateBlock14, besselGridState009, besselGridState013, besselGridState020, besselGridState023, besselGridState025, besselGridState032, besselGridState034, besselGridState037, besselGridState043, besselGridState044, besselGridState047, besselGridState050, besselGridState051, besselGridState053, besselGridState055, besselGridState056, besselGridState062, besselGridState063, besselGridState066, besselGridState068, besselGridState075, besselGridState080, besselGridState085, besselGridState092, besselGridState096, besselGridState099, besselStateSubset, linearInterval, widenInterval,
    rationalErrorInterval, rationalIntervalSubset, orderedInterval, Finset.sum_range_succ,
    IntervalRat.add, IntervalRat.mul, IntervalRat.scale, IntervalRat.singleton]

theorem compactCertificate260_stateChecks3 :
    compactCertificate260.stateChecks 9 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 96 12 (2419425551654459 / 8000000000000)) (orderedInterval (45824380970 / 1000000000000) (45824381247 / 1000000000000), orderedInterval (-2345361464 / 1000000000000) (-2345361187 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 56 12 (1396855993531811 / 8000000000000)) (orderedInterval (-30915419889 / 1000000000000) (-30915414998 / 1000000000000), orderedInterval (51956234577 / 1000000000000) (51956239468 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 99 12 (2478745473003199 / 8000000000000)) (orderedInterval (17212046949 / 1000000000000) (17212047349 / 1000000000000), orderedInterval (-41961042364 / 1000000000000) (-41961041964 / 1000000000000))) = true
  norm_num [besselStateAtRationalPoint, besselIntervalStepZero,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, besselZeroTransition,
    besselInitial, besselGridStateAt, besselGridStateBlock00, besselGridStateBlock01,
    besselGridStateBlock02, besselGridStateBlock03, besselGridStateBlock04,
    besselGridStateBlock05, besselGridStateBlock06, besselGridStateBlock07,
    besselGridStateBlock08, besselGridStateBlock09, besselGridStateBlock10,
    besselGridStateBlock11, besselGridStateBlock12, besselGridStateBlock13,
    besselGridStateBlock14, besselGridState009, besselGridState013, besselGridState020, besselGridState023, besselGridState025, besselGridState032, besselGridState034, besselGridState037, besselGridState043, besselGridState044, besselGridState047, besselGridState050, besselGridState051, besselGridState053, besselGridState055, besselGridState056, besselGridState062, besselGridState063, besselGridState066, besselGridState068, besselGridState075, besselGridState080, besselGridState085, besselGridState092, besselGridState096, besselGridState099, besselStateSubset, linearInterval, widenInterval,
    rationalErrorInterval, rationalIntervalSubset, orderedInterval, Finset.sum_range_succ,
    IntervalRat.add, IntervalRat.mul, IntervalRat.scale, IntervalRat.singleton]

theorem compactCertificate260_stateChecks4 :
    compactCertificate260.stateChecks 12 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 92 12 (2315965555285531 / 8000000000000)) (orderedInterval (44562615555 / 1000000000000) (44562615556 / 1000000000000), orderedInterval (14525615760 / 1000000000000) (14525615762 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 66 12 (1652782300646923 / 8000000000000)) (orderedInterval (2079253213 / 1000000000000) (2079253215 / 1000000000000), orderedInterval (55466861327 / 1000000000000) (55466861329 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 75 12 (1874078973789117 / 8000000000000)) (orderedInterval (28337724831 / 1000000000000) (28337730102 / 1000000000000), orderedInterval (-43816114049 / 1000000000000) (-43816108778 / 1000000000000))) = true
  norm_num [besselStateAtRationalPoint, besselIntervalStepZero,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, besselZeroTransition,
    besselInitial, besselGridStateAt, besselGridStateBlock00, besselGridStateBlock01,
    besselGridStateBlock02, besselGridStateBlock03, besselGridStateBlock04,
    besselGridStateBlock05, besselGridStateBlock06, besselGridStateBlock07,
    besselGridStateBlock08, besselGridStateBlock09, besselGridStateBlock10,
    besselGridStateBlock11, besselGridStateBlock12, besselGridStateBlock13,
    besselGridStateBlock14, besselGridState009, besselGridState013, besselGridState020, besselGridState023, besselGridState025, besselGridState032, besselGridState034, besselGridState037, besselGridState043, besselGridState044, besselGridState047, besselGridState050, besselGridState051, besselGridState053, besselGridState055, besselGridState056, besselGridState062, besselGridState063, besselGridState066, besselGridState068, besselGridState075, besselGridState080, besselGridState085, besselGridState092, besselGridState096, besselGridState099, besselStateSubset, linearInterval, widenInterval,
    rationalErrorInterval, rationalIntervalSubset, orderedInterval, Finset.sum_range_succ,
    IntervalRat.add, IntervalRat.mul, IntervalRat.scale, IntervalRat.singleton]

theorem compactCertificate260_stateChecks5 :
    compactCertificate260.stateChecks 15 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 62 12 (1562411665790573 / 8000000000000)) (orderedInterval (55125478108 / 1000000000000) (55125478110 / 1000000000000), orderedInterval (14719892732 / 1000000000000) (14719892733 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 55 12 (1380438089918033 / 8000000000000)) (orderedInterval (-31843264575 / 1000000000000) (-31843264574 / 1000000000000), orderedInterval (-51631919130 / 1000000000000) (-51631919129 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 80 12 (400104763617267 / 1600000000000)) (orderedInterval (-23166806640 / 1000000000000) (-23166804982 / 1000000000000), orderedInterval (44869465895 / 1000000000000) (44869467553 / 1000000000000))) = true
  norm_num [besselStateAtRationalPoint, besselIntervalStepZero,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, besselZeroTransition,
    besselInitial, besselGridStateAt, besselGridStateBlock00, besselGridStateBlock01,
    besselGridStateBlock02, besselGridStateBlock03, besselGridStateBlock04,
    besselGridStateBlock05, besselGridStateBlock06, besselGridStateBlock07,
    besselGridStateBlock08, besselGridStateBlock09, besselGridStateBlock10,
    besselGridStateBlock11, besselGridStateBlock12, besselGridStateBlock13,
    besselGridStateBlock14, besselGridState009, besselGridState013, besselGridState020, besselGridState023, besselGridState025, besselGridState032, besselGridState034, besselGridState037, besselGridState043, besselGridState044, besselGridState047, besselGridState050, besselGridState051, besselGridState053, besselGridState055, besselGridState056, besselGridState062, besselGridState063, besselGridState066, besselGridState068, besselGridState075, besselGridState080, besselGridState085, besselGridState092, besselGridState096, besselGridState099, besselStateSubset, linearInterval, widenInterval,
    rationalErrorInterval, rationalIntervalSubset, orderedInterval, Finset.sum_range_succ,
    IntervalRat.add, IntervalRat.mul, IntervalRat.scale, IntervalRat.singleton]

theorem compactCertificate260_stateChecks6 :
    compactCertificate260.stateChecks 18 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 44 12 (1106710832525449 / 8000000000000)) (orderedInterval (52853626763 / 1000000000000) (52853626764 / 1000000000000), orderedInterval (42333961934 / 1000000000000) (42333961935 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 37 12 (938171029218689 / 8000000000000)) (orderedInterval (-71460813118 / 1000000000000) (-71460812116 / 1000000000000), orderedInterval (18246578645 / 1000000000000) (18246579647 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 23 12 (587063869407467 / 8000000000000)) (orderedInterval (-87831626534 / 1000000000000) (-87831624246 / 1000000000000), orderedInterval (31594448931 / 1000000000000) (31594451219 / 1000000000000))) = true
  norm_num [besselStateAtRationalPoint, besselIntervalStepZero,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, besselZeroTransition,
    besselInitial, besselGridStateAt, besselGridStateBlock00, besselGridStateBlock01,
    besselGridStateBlock02, besselGridStateBlock03, besselGridStateBlock04,
    besselGridStateBlock05, besselGridStateBlock06, besselGridStateBlock07,
    besselGridStateBlock08, besselGridStateBlock09, besselGridStateBlock10,
    besselGridStateBlock11, besselGridStateBlock12, besselGridStateBlock13,
    besselGridStateBlock14, besselGridState009, besselGridState013, besselGridState020, besselGridState023, besselGridState025, besselGridState032, besselGridState034, besselGridState037, besselGridState043, besselGridState044, besselGridState047, besselGridState050, besselGridState051, besselGridState053, besselGridState055, besselGridState056, besselGridState062, besselGridState063, besselGridState066, besselGridState068, besselGridState075, besselGridState080, besselGridState085, besselGridState092, besselGridState096, besselGridState099, besselStateSubset, linearInterval, widenInterval,
    rationalErrorInterval, rationalIntervalSubset, orderedInterval, Finset.sum_range_succ,
    IntervalRat.add, IntervalRat.mul, IntervalRat.scale, IntervalRat.singleton]

theorem compactCertificate260_stateChecks7 :
    compactCertificate260.stateChecks 21 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 13 12 (315724901453589 / 8000000000000)) (orderedInterval (70960909561 / 1000000000000) (70960926135 / 1000000000000), orderedInterval (-106236596020 / 1000000000000) (-106236579446 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 34 12 (857254524687767 / 8000000000000)) (orderedInterval (69607481005 / 1000000000000) (69607481006 / 1000000000000), orderedInterval (32777606097 / 1000000000000) (32777606098 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 47 12 (1170507764517559 / 8000000000000)) (orderedInterval (34861567273 / 1000000000000) (34861574204 / 1000000000000), orderedInterval (-56116898336 / 1000000000000) (-56116891405 / 1000000000000))) = true
  norm_num [besselStateAtRationalPoint, besselIntervalStepZero,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, besselZeroTransition,
    besselInitial, besselGridStateAt, besselGridStateBlock00, besselGridStateBlock01,
    besselGridStateBlock02, besselGridStateBlock03, besselGridStateBlock04,
    besselGridStateBlock05, besselGridStateBlock06, besselGridStateBlock07,
    besselGridStateBlock08, besselGridStateBlock09, besselGridStateBlock10,
    besselGridStateBlock11, besselGridStateBlock12, besselGridStateBlock13,
    besselGridStateBlock14, besselGridState009, besselGridState013, besselGridState020, besselGridState023, besselGridState025, besselGridState032, besselGridState034, besselGridState037, besselGridState043, besselGridState044, besselGridState047, besselGridState050, besselGridState051, besselGridState053, besselGridState055, besselGridState056, besselGridState062, besselGridState063, besselGridState066, besselGridState068, besselGridState075, besselGridState080, besselGridState085, besselGridState092, besselGridState096, besselGridState099, besselStateSubset, linearInterval, widenInterval,
    rationalErrorInterval, rationalIntervalSubset, orderedInterval, Finset.sum_range_succ,
    IntervalRat.add, IntervalRat.mul, IntervalRat.scale, IntervalRat.singleton]

theorem compactCertificate260_stateChecks8 :
    compactCertificate260.stateChecks 24 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 20 12 (494936130592533 / 8000000000000)) (orderedInterval (-18306080970 / 1000000000000) (-18306080839 / 1000000000000), orderedInterval (99924355197 / 1000000000000) (99924355328 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 80 12 (2011887892826293 / 8000000000000)) (orderedInterval (40733791974 / 1000000000000) (40733791975 / 1000000000000), orderedInterval (29451860689 / 1000000000000) (29451860690 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 53 12 (1343847873347387 / 8000000000000)) (orderedInterval (-47462191704 / 1000000000000) (-47462086765 / 1000000000000), orderedInterval (39348031238 / 1000000000000) (39348136176 / 1000000000000))) = true
  norm_num [besselStateAtRationalPoint, besselIntervalStepZero,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, besselZeroTransition,
    besselInitial, besselGridStateAt, besselGridStateBlock00, besselGridStateBlock01,
    besselGridStateBlock02, besselGridStateBlock03, besselGridStateBlock04,
    besselGridStateBlock05, besselGridStateBlock06, besselGridStateBlock07,
    besselGridStateBlock08, besselGridStateBlock09, besselGridStateBlock10,
    besselGridStateBlock11, besselGridStateBlock12, besselGridStateBlock13,
    besselGridStateBlock14, besselGridState009, besselGridState013, besselGridState020, besselGridState023, besselGridState025, besselGridState032, besselGridState034, besselGridState037, besselGridState043, besselGridState044, besselGridState047, besselGridState050, besselGridState051, besselGridState053, besselGridState055, besselGridState056, besselGridState062, besselGridState063, besselGridState066, besselGridState068, besselGridState075, besselGridState080, besselGridState085, besselGridState092, besselGridState096, besselGridState099, besselStateSubset, linearInterval, widenInterval,
    rationalErrorInterval, rationalIntervalSubset, orderedInterval, Finset.sum_range_succ,
    IntervalRat.add, IntervalRat.mul, IntervalRat.scale, IntervalRat.singleton]

theorem compactCertificate260_states : ∀ j,
    BesselStateValid (compactCertificate260.point j) (compactCertificate260.state j) :=
  compactCertificate260.statesValid_of_checks3 compactCertificate260_stateChecks0
    compactCertificate260_stateChecks1 compactCertificate260_stateChecks2
    compactCertificate260_stateChecks3 compactCertificate260_stateChecks4
    compactCertificate260_stateChecks5 compactCertificate260_stateChecks6
    compactCertificate260_stateChecks7 compactCertificate260_stateChecks8

theorem compactCertificate260_chunkChecks0_0 :
    compactCertificate260.chunkChecks (0 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 0) <| besselDerivativeNearFromState (541 / 4) 0 (IntervalRat.scale (541 / 4) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-55645708590 / 1000000000000) (-55645708589 / 1000000000000), orderedInterval (-39925701934 / 1000000000000) (-39925701933 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 0) <| besselDerivativeNearFromState (796996302814441 / 8000000000000) 0 (IntervalRat.scale (541 / 4) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-9750778576 / 1000000000000) (-9750778533 / 1000000000000), orderedInterval (79391175201 / 1000000000000) (79391175244 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 0) <| besselDerivativeNearFromState (257732229007753 / 1600000000000) 0 (IntervalRat.scale (541 / 4) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-62687951495 / 1000000000000) (-62687951345 / 1000000000000), orderedInterval (4920396163 / 1000000000000) (4920396313 / 1000000000000)))) (orderedInterval (-25825469699 / 1000000000000) (-25825469679 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 0) <| besselDerivativeNearFromState (232561533424187 / 8000000000000) 0 (IntervalRat.scale (541 / 4) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-147970727714 / 1000000000000) (-147970727692 / 1000000000000), orderedInterval (3456300717 / 1000000000000) (3456300739 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 0) <| besselDerivativeNearFromState (624692991263039 / 8000000000000) 0 (IntervalRat.scale (541 / 4) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-29310039922 / 1000000000000) (-29310039921 / 1000000000000), orderedInterval (-85216027071 / 1000000000000) (-85216027070 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 0) <| besselDerivativeNearFromState (1696162991372163 / 8000000000000) 0 (IntervalRat.scale (541 / 4) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-40180425613 / 1000000000000) (-40180363306 / 1000000000000), orderedInterval (37352877491 / 1000000000000) (37352939797 / 1000000000000)))) (orderedInterval (3391624345 / 1000000000000) (3391628792 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 0) <| besselDerivativeNearFromState (1249385982526619 / 8000000000000) 0 (IntervalRat.scale (541 / 4) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-7756445035 / 1000000000000) (-7756445007 / 1000000000000), orderedInterval (63398539615 / 1000000000000) (63398539643 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 0) <| besselDerivativeNearFromState (2140844176161287 / 8000000000000) 0 (IntervalRat.scale (541 / 4) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-47643968570 / 1000000000000) (-47643968566 / 1000000000000), orderedInterval (-10351146577 / 1000000000000) (-10351146573 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 0) <| besselDerivativeNearFromState (1576936130592533 / 8000000000000) 0 (IntervalRat.scale (541 / 4) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (1054522774 / 1000000000000) (1054522778 / 1000000000000), orderedInterval (-56823027064 / 1000000000000) (-56823027060 / 1000000000000)))) (orderedInterval (1495016345 / 1000000000000) (1495016353 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate260_chunkChecks0_1 :
    compactCertificate260.chunkChecks (0 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 0) <| besselDerivativeNearFromState (2419425551654459 / 8000000000000) 0 (IntervalRat.scale (541 / 4) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (45824380970 / 1000000000000) (45824381247 / 1000000000000), orderedInterval (-2345361464 / 1000000000000) (-2345361187 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 0) <| besselDerivativeNearFromState (1396855993531811 / 8000000000000) 0 (IntervalRat.scale (541 / 4) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-30915419889 / 1000000000000) (-30915414998 / 1000000000000), orderedInterval (51956234577 / 1000000000000) (51956239468 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 0) <| besselDerivativeNearFromState (2478745473003199 / 8000000000000) 0 (IntervalRat.scale (541 / 4) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (17212046949 / 1000000000000) (17212047349 / 1000000000000), orderedInterval (-41961042364 / 1000000000000) (-41961041964 / 1000000000000)))) (orderedInterval (-7986223615 / 1000000000000) (-7986223092 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 0) <| besselDerivativeNearFromState (2315965555285531 / 8000000000000) 0 (IntervalRat.scale (541 / 4) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (44562615555 / 1000000000000) (44562615556 / 1000000000000), orderedInterval (14525615760 / 1000000000000) (14525615762 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 0) <| besselDerivativeNearFromState (1652782300646923 / 8000000000000) 0 (IntervalRat.scale (541 / 4) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (2079253213 / 1000000000000) (2079253215 / 1000000000000), orderedInterval (55466861327 / 1000000000000) (55466861329 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 0) <| besselDerivativeNearFromState (1874078973789117 / 8000000000000) 0 (IntervalRat.scale (541 / 4) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (28337724831 / 1000000000000) (28337730102 / 1000000000000), orderedInterval (-43816114049 / 1000000000000) (-43816108778 / 1000000000000)))) (orderedInterval (-751277833 / 1000000000000) (-751277790 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 0) <| besselDerivativeNearFromState (1562411665790573 / 8000000000000) 0 (IntervalRat.scale (541 / 4) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (55125478108 / 1000000000000) (55125478110 / 1000000000000), orderedInterval (14719892732 / 1000000000000) (14719892733 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 0) <| besselDerivativeNearFromState (1380438089918033 / 8000000000000) 0 (IntervalRat.scale (541 / 4) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-31843264575 / 1000000000000) (-31843264574 / 1000000000000), orderedInterval (-51631919130 / 1000000000000) (-51631919129 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 0) <| besselDerivativeNearFromState (400104763617267 / 1600000000000) 0 (IntervalRat.scale (541 / 4) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-23166806640 / 1000000000000) (-23166804982 / 1000000000000), orderedInterval (44869465895 / 1000000000000) (44869467553 / 1000000000000)))) (orderedInterval (1865693280 / 1000000000000) (1865693337 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate260_chunkChecks0_2 :
    compactCertificate260.chunkChecks (0 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 0) <| besselDerivativeNearFromState (1106710832525449 / 8000000000000) 0 (IntervalRat.scale (541 / 4) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (52853626763 / 1000000000000) (52853626764 / 1000000000000), orderedInterval (42333961934 / 1000000000000) (42333961935 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 0) <| besselDerivativeNearFromState (938171029218689 / 8000000000000) 0 (IntervalRat.scale (541 / 4) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-71460813118 / 1000000000000) (-71460812116 / 1000000000000), orderedInterval (18246578645 / 1000000000000) (18246579647 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 0) <| besselDerivativeNearFromState (587063869407467 / 8000000000000) 0 (IntervalRat.scale (541 / 4) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-87831626534 / 1000000000000) (-87831624246 / 1000000000000), orderedInterval (31594448931 / 1000000000000) (31594451219 / 1000000000000)))) (orderedInterval (-7265599052 / 1000000000000) (-7265598886 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 0) <| besselDerivativeNearFromState (315724901453589 / 8000000000000) 0 (IntervalRat.scale (541 / 4) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (70960909561 / 1000000000000) (70960926135 / 1000000000000), orderedInterval (-106236596020 / 1000000000000) (-106236579446 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 0) <| besselDerivativeNearFromState (857254524687767 / 8000000000000) 0 (IntervalRat.scale (541 / 4) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (69607481005 / 1000000000000) (69607481006 / 1000000000000), orderedInterval (32777606097 / 1000000000000) (32777606098 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 0) <| besselDerivativeNearFromState (1170507764517559 / 8000000000000) 0 (IntervalRat.scale (541 / 4) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (34861567273 / 1000000000000) (34861574204 / 1000000000000), orderedInterval (-56116898336 / 1000000000000) (-56116891405 / 1000000000000)))) (orderedInterval (-5561228781 / 1000000000000) (-5561227927 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 0) <| besselDerivativeNearFromState (494936130592533 / 8000000000000) 0 (IntervalRat.scale (541 / 4) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-18306080970 / 1000000000000) (-18306080839 / 1000000000000), orderedInterval (99924355197 / 1000000000000) (99924355328 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 0) <| besselDerivativeNearFromState (2011887892826293 / 8000000000000) 0 (IntervalRat.scale (541 / 4) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (40733791974 / 1000000000000) (40733791975 / 1000000000000), orderedInterval (29451860689 / 1000000000000) (29451860690 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 0) <| besselDerivativeNearFromState (1343847873347387 / 8000000000000) 0 (IntervalRat.scale (541 / 4) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-47462191704 / 1000000000000) (-47462086765 / 1000000000000), orderedInterval (39348031238 / 1000000000000) (39348136176 / 1000000000000)))) (orderedInterval (5478988374 / 1000000000000) (5479008102 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate260_chunkChecks0 :
    compactCertificate260.chunkChecks (0 : Fin 5) 0 9 = true :=
  compactCertificate260.chunkChecks_nine_of_three (0 : Fin 5) compactCertificate260_chunkChecks0_0
    compactCertificate260_chunkChecks0_1 compactCertificate260_chunkChecks0_2

theorem compactCertificate260_chunkChecks1_0 :
    compactCertificate260.chunkChecks (1 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 1) <| besselDerivativeNearFromState (541 / 4) 1 (IntervalRat.scale (541 / 4) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-55645708590 / 1000000000000) (-55645708589 / 1000000000000), orderedInterval (-39925701934 / 1000000000000) (-39925701933 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 1) <| besselDerivativeNearFromState (796996302814441 / 8000000000000) 1 (IntervalRat.scale (541 / 4) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-9750778576 / 1000000000000) (-9750778533 / 1000000000000), orderedInterval (79391175201 / 1000000000000) (79391175244 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 1) <| besselDerivativeNearFromState (257732229007753 / 1600000000000) 1 (IntervalRat.scale (541 / 4) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-62687951495 / 1000000000000) (-62687951345 / 1000000000000), orderedInterval (4920396163 / 1000000000000) (4920396313 / 1000000000000)))) (orderedInterval (-14936355553 / 1000000000000) (-14936355531 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 1) <| besselDerivativeNearFromState (232561533424187 / 8000000000000) 1 (IntervalRat.scale (541 / 4) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-147970727714 / 1000000000000) (-147970727692 / 1000000000000), orderedInterval (3456300717 / 1000000000000) (3456300739 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 1) <| besselDerivativeNearFromState (624692991263039 / 8000000000000) 1 (IntervalRat.scale (541 / 4) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-29310039922 / 1000000000000) (-29310039921 / 1000000000000), orderedInterval (-85216027071 / 1000000000000) (-85216027070 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 1) <| besselDerivativeNearFromState (1696162991372163 / 8000000000000) 1 (IntervalRat.scale (541 / 4) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-40180425613 / 1000000000000) (-40180363306 / 1000000000000), orderedInterval (37352877491 / 1000000000000) (37352939797 / 1000000000000)))) (orderedInterval (-5967084014 / 1000000000000) (-5967077051 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 1) <| besselDerivativeNearFromState (1249385982526619 / 8000000000000) 1 (IntervalRat.scale (541 / 4) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-7756445035 / 1000000000000) (-7756445007 / 1000000000000), orderedInterval (63398539615 / 1000000000000) (63398539643 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 1) <| besselDerivativeNearFromState (2140844176161287 / 8000000000000) 1 (IntervalRat.scale (541 / 4) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-47643968570 / 1000000000000) (-47643968566 / 1000000000000), orderedInterval (-10351146577 / 1000000000000) (-10351146573 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 1) <| besselDerivativeNearFromState (1576936130592533 / 8000000000000) 1 (IntervalRat.scale (541 / 4) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (1054522774 / 1000000000000) (1054522778 / 1000000000000), orderedInterval (-56823027064 / 1000000000000) (-56823027060 / 1000000000000)))) (orderedInterval (-1369776459 / 1000000000000) (-1369776445 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate260_chunkChecks1_1 :
    compactCertificate260.chunkChecks (1 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 1) <| besselDerivativeNearFromState (2419425551654459 / 8000000000000) 1 (IntervalRat.scale (541 / 4) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (45824380970 / 1000000000000) (45824381247 / 1000000000000), orderedInterval (-2345361464 / 1000000000000) (-2345361187 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 1) <| besselDerivativeNearFromState (1396855993531811 / 8000000000000) 1 (IntervalRat.scale (541 / 4) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-30915419889 / 1000000000000) (-30915414998 / 1000000000000), orderedInterval (51956234577 / 1000000000000) (51956239468 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 1) <| besselDerivativeNearFromState (2478745473003199 / 8000000000000) 1 (IntervalRat.scale (541 / 4) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (17212046949 / 1000000000000) (17212047349 / 1000000000000), orderedInterval (-41961042364 / 1000000000000) (-41961041964 / 1000000000000)))) (orderedInterval (-7763608812 / 1000000000000) (-7763607992 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 1) <| besselDerivativeNearFromState (2315965555285531 / 8000000000000) 1 (IntervalRat.scale (541 / 4) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (44562615555 / 1000000000000) (44562615556 / 1000000000000), orderedInterval (14525615760 / 1000000000000) (14525615762 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 1) <| besselDerivativeNearFromState (1652782300646923 / 8000000000000) 1 (IntervalRat.scale (541 / 4) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (2079253213 / 1000000000000) (2079253215 / 1000000000000), orderedInterval (55466861327 / 1000000000000) (55466861329 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 1) <| besselDerivativeNearFromState (1874078973789117 / 8000000000000) 1 (IntervalRat.scale (541 / 4) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (28337724831 / 1000000000000) (28337730102 / 1000000000000), orderedInterval (-43816114049 / 1000000000000) (-43816108778 / 1000000000000)))) (orderedInterval (7834792073 / 1000000000000) (7834792147 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 1) <| besselDerivativeNearFromState (1562411665790573 / 8000000000000) 1 (IntervalRat.scale (541 / 4) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (55125478108 / 1000000000000) (55125478110 / 1000000000000), orderedInterval (14719892732 / 1000000000000) (14719892733 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 1) <| besselDerivativeNearFromState (1380438089918033 / 8000000000000) 1 (IntervalRat.scale (541 / 4) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-31843264575 / 1000000000000) (-31843264574 / 1000000000000), orderedInterval (-51631919130 / 1000000000000) (-51631919129 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 1) <| besselDerivativeNearFromState (400104763617267 / 1600000000000) 1 (IntervalRat.scale (541 / 4) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-23166806640 / 1000000000000) (-23166804982 / 1000000000000), orderedInterval (44869465895 / 1000000000000) (44869467553 / 1000000000000)))) (orderedInterval (6139246531 / 1000000000000) (6139246629 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate260_chunkChecks1_2 :
    compactCertificate260.chunkChecks (1 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 1) <| besselDerivativeNearFromState (1106710832525449 / 8000000000000) 1 (IntervalRat.scale (541 / 4) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (52853626763 / 1000000000000) (52853626764 / 1000000000000), orderedInterval (42333961934 / 1000000000000) (42333961935 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 1) <| besselDerivativeNearFromState (938171029218689 / 8000000000000) 1 (IntervalRat.scale (541 / 4) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-71460813118 / 1000000000000) (-71460812116 / 1000000000000), orderedInterval (18246578645 / 1000000000000) (18246579647 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 1) <| besselDerivativeNearFromState (587063869407467 / 8000000000000) 1 (IntervalRat.scale (541 / 4) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-87831626534 / 1000000000000) (-87831624246 / 1000000000000), orderedInterval (31594448931 / 1000000000000) (31594451219 / 1000000000000)))) (orderedInterval (-7260869679 / 1000000000000) (-7260869557 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 1) <| besselDerivativeNearFromState (315724901453589 / 8000000000000) 1 (IntervalRat.scale (541 / 4) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (70960909561 / 1000000000000) (70960926135 / 1000000000000), orderedInterval (-106236596020 / 1000000000000) (-106236579446 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 1) <| besselDerivativeNearFromState (857254524687767 / 8000000000000) 1 (IntervalRat.scale (541 / 4) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (69607481005 / 1000000000000) (69607481006 / 1000000000000), orderedInterval (32777606097 / 1000000000000) (32777606098 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 1) <| besselDerivativeNearFromState (1170507764517559 / 8000000000000) 1 (IntervalRat.scale (541 / 4) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (34861567273 / 1000000000000) (34861574204 / 1000000000000), orderedInterval (-56116898336 / 1000000000000) (-56116891405 / 1000000000000)))) (orderedInterval (4635785328 / 1000000000000) (4635786007 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 1) <| besselDerivativeNearFromState (494936130592533 / 8000000000000) 1 (IntervalRat.scale (541 / 4) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-18306080970 / 1000000000000) (-18306080839 / 1000000000000), orderedInterval (99924355197 / 1000000000000) (99924355328 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 1) <| besselDerivativeNearFromState (2011887892826293 / 8000000000000) 1 (IntervalRat.scale (541 / 4) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (40733791974 / 1000000000000) (40733791975 / 1000000000000), orderedInterval (29451860689 / 1000000000000) (29451860690 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 1) <| besselDerivativeNearFromState (1343847873347387 / 8000000000000) 1 (IntervalRat.scale (541 / 4) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-47462191704 / 1000000000000) (-47462086765 / 1000000000000), orderedInterval (39348031238 / 1000000000000) (39348136176 / 1000000000000)))) (orderedInterval (-13351689892 / 1000000000000) (-13351665385 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate260_chunkChecks1 :
    compactCertificate260.chunkChecks (1 : Fin 5) 0 9 = true :=
  compactCertificate260.chunkChecks_nine_of_three (1 : Fin 5) compactCertificate260_chunkChecks1_0
    compactCertificate260_chunkChecks1_1 compactCertificate260_chunkChecks1_2

theorem compactCertificate260_chunkChecks2_0 :
    compactCertificate260.chunkChecks (2 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 2) <| besselDerivativeNearFromState (541 / 4) 2 (IntervalRat.scale (541 / 4) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-55645708590 / 1000000000000) (-55645708589 / 1000000000000), orderedInterval (-39925701934 / 1000000000000) (-39925701933 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 2) <| besselDerivativeNearFromState (796996302814441 / 8000000000000) 2 (IntervalRat.scale (541 / 4) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-9750778576 / 1000000000000) (-9750778533 / 1000000000000), orderedInterval (79391175201 / 1000000000000) (79391175244 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 2) <| besselDerivativeNearFromState (257732229007753 / 1600000000000) 2 (IntervalRat.scale (541 / 4) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-62687951495 / 1000000000000) (-62687951345 / 1000000000000), orderedInterval (4920396163 / 1000000000000) (4920396313 / 1000000000000)))) (orderedInterval (27433761242 / 1000000000000) (27433761268 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 2) <| besselDerivativeNearFromState (232561533424187 / 8000000000000) 2 (IntervalRat.scale (541 / 4) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-147970727714 / 1000000000000) (-147970727692 / 1000000000000), orderedInterval (3456300717 / 1000000000000) (3456300739 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 2) <| besselDerivativeNearFromState (624692991263039 / 8000000000000) 2 (IntervalRat.scale (541 / 4) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-29310039922 / 1000000000000) (-29310039921 / 1000000000000), orderedInterval (-85216027071 / 1000000000000) (-85216027070 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 2) <| besselDerivativeNearFromState (1696162991372163 / 8000000000000) 2 (IntervalRat.scale (541 / 4) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-40180425613 / 1000000000000) (-40180363306 / 1000000000000), orderedInterval (37352877491 / 1000000000000) (37352939797 / 1000000000000)))) (orderedInterval (-6692750157 / 1000000000000) (-6692739195 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 2) <| besselDerivativeNearFromState (1249385982526619 / 8000000000000) 2 (IntervalRat.scale (541 / 4) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-7756445035 / 1000000000000) (-7756445007 / 1000000000000), orderedInterval (63398539615 / 1000000000000) (63398539643 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 2) <| besselDerivativeNearFromState (2140844176161287 / 8000000000000) 2 (IntervalRat.scale (541 / 4) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-47643968570 / 1000000000000) (-47643968566 / 1000000000000), orderedInterval (-10351146577 / 1000000000000) (-10351146573 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 2) <| besselDerivativeNearFromState (1576936130592533 / 8000000000000) 2 (IntervalRat.scale (541 / 4) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (1054522774 / 1000000000000) (1054522778 / 1000000000000), orderedInterval (-56823027064 / 1000000000000) (-56823027060 / 1000000000000)))) (orderedInterval (-5797004486 / 1000000000000) (-5797004461 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate260_chunkChecks2_1 :
    compactCertificate260.chunkChecks (2 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 2) <| besselDerivativeNearFromState (2419425551654459 / 8000000000000) 2 (IntervalRat.scale (541 / 4) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (45824380970 / 1000000000000) (45824381247 / 1000000000000), orderedInterval (-2345361464 / 1000000000000) (-2345361187 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 2) <| besselDerivativeNearFromState (1396855993531811 / 8000000000000) 2 (IntervalRat.scale (541 / 4) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-30915419889 / 1000000000000) (-30915414998 / 1000000000000), orderedInterval (51956234577 / 1000000000000) (51956239468 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 2) <| besselDerivativeNearFromState (2478745473003199 / 8000000000000) 2 (IntervalRat.scale (541 / 4) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (17212046949 / 1000000000000) (17212047349 / 1000000000000), orderedInterval (-41961042364 / 1000000000000) (-41961041964 / 1000000000000)))) (orderedInterval (31745994098 / 1000000000000) (31745995491 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 2) <| besselDerivativeNearFromState (2315965555285531 / 8000000000000) 2 (IntervalRat.scale (541 / 4) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (44562615555 / 1000000000000) (44562615556 / 1000000000000), orderedInterval (14525615760 / 1000000000000) (14525615762 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 2) <| besselDerivativeNearFromState (1652782300646923 / 8000000000000) 2 (IntervalRat.scale (541 / 4) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (2079253213 / 1000000000000) (2079253215 / 1000000000000), orderedInterval (55466861327 / 1000000000000) (55466861329 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 2) <| besselDerivativeNearFromState (1874078973789117 / 8000000000000) 2 (IntervalRat.scale (541 / 4) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (28337724831 / 1000000000000) (28337730102 / 1000000000000), orderedInterval (-43816114049 / 1000000000000) (-43816108778 / 1000000000000)))) (orderedInterval (3599307298 / 1000000000000) (3599307423 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 2) <| besselDerivativeNearFromState (1562411665790573 / 8000000000000) 2 (IntervalRat.scale (541 / 4) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (55125478108 / 1000000000000) (55125478110 / 1000000000000), orderedInterval (14719892732 / 1000000000000) (14719892733 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 2) <| besselDerivativeNearFromState (1380438089918033 / 8000000000000) 2 (IntervalRat.scale (541 / 4) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-31843264575 / 1000000000000) (-31843264574 / 1000000000000), orderedInterval (-51631919130 / 1000000000000) (-51631919129 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 2) <| besselDerivativeNearFromState (400104763617267 / 1600000000000) 2 (IntervalRat.scale (541 / 4) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-23166806640 / 1000000000000) (-23166804982 / 1000000000000), orderedInterval (44869465895 / 1000000000000) (44869467553 / 1000000000000)))) (orderedInterval (-2311189951 / 1000000000000) (-2311189776 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate260_chunkChecks2_2 :
    compactCertificate260.chunkChecks (2 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 2) <| besselDerivativeNearFromState (1106710832525449 / 8000000000000) 2 (IntervalRat.scale (541 / 4) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (52853626763 / 1000000000000) (52853626764 / 1000000000000), orderedInterval (42333961934 / 1000000000000) (42333961935 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 2) <| besselDerivativeNearFromState (938171029218689 / 8000000000000) 2 (IntervalRat.scale (541 / 4) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-71460813118 / 1000000000000) (-71460812116 / 1000000000000), orderedInterval (18246578645 / 1000000000000) (18246579647 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 2) <| besselDerivativeNearFromState (587063869407467 / 8000000000000) 2 (IntervalRat.scale (541 / 4) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-87831626534 / 1000000000000) (-87831624246 / 1000000000000), orderedInterval (31594448931 / 1000000000000) (31594451219 / 1000000000000)))) (orderedInterval (6695913278 / 1000000000000) (6695913375 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 2) <| besselDerivativeNearFromState (315724901453589 / 8000000000000) 2 (IntervalRat.scale (541 / 4) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (70960909561 / 1000000000000) (70960926135 / 1000000000000), orderedInterval (-106236596020 / 1000000000000) (-106236579446 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 2) <| besselDerivativeNearFromState (857254524687767 / 8000000000000) 2 (IntervalRat.scale (541 / 4) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (69607481005 / 1000000000000) (69607481006 / 1000000000000), orderedInterval (32777606097 / 1000000000000) (32777606098 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 2) <| besselDerivativeNearFromState (1170507764517559 / 8000000000000) 2 (IntervalRat.scale (541 / 4) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (34861567273 / 1000000000000) (34861574204 / 1000000000000), orderedInterval (-56116898336 / 1000000000000) (-56116891405 / 1000000000000)))) (orderedInterval (4195296611 / 1000000000000) (4195297279 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 2) <| besselDerivativeNearFromState (494936130592533 / 8000000000000) 2 (IntervalRat.scale (541 / 4) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-18306080970 / 1000000000000) (-18306080839 / 1000000000000), orderedInterval (99924355197 / 1000000000000) (99924355328 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 2) <| besselDerivativeNearFromState (2011887892826293 / 8000000000000) 2 (IntervalRat.scale (541 / 4) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (40733791974 / 1000000000000) (40733791975 / 1000000000000), orderedInterval (29451860689 / 1000000000000) (29451860690 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 2) <| besselDerivativeNearFromState (1343847873347387 / 8000000000000) 2 (IntervalRat.scale (541 / 4) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-47462191704 / 1000000000000) (-47462086765 / 1000000000000), orderedInterval (39348031238 / 1000000000000) (39348136176 / 1000000000000)))) (orderedInterval (-2150911601 / 1000000000000) (-2150880969 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate260_chunkChecks2 :
    compactCertificate260.chunkChecks (2 : Fin 5) 0 9 = true :=
  compactCertificate260.chunkChecks_nine_of_three (2 : Fin 5) compactCertificate260_chunkChecks2_0
    compactCertificate260_chunkChecks2_1 compactCertificate260_chunkChecks2_2

theorem compactCertificate260_chunkChecks3_0 :
    compactCertificate260.chunkChecks (3 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 3) <| besselDerivativeNearFromState (541 / 4) 3 (IntervalRat.scale (541 / 4) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-55645708590 / 1000000000000) (-55645708589 / 1000000000000), orderedInterval (-39925701934 / 1000000000000) (-39925701933 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 3) <| besselDerivativeNearFromState (796996302814441 / 8000000000000) 3 (IntervalRat.scale (541 / 4) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-9750778576 / 1000000000000) (-9750778533 / 1000000000000), orderedInterval (79391175201 / 1000000000000) (79391175244 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 3) <| besselDerivativeNearFromState (257732229007753 / 1600000000000) 3 (IntervalRat.scale (541 / 4) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-62687951495 / 1000000000000) (-62687951345 / 1000000000000), orderedInterval (4920396163 / 1000000000000) (4920396313 / 1000000000000)))) (orderedInterval (14838051682 / 1000000000000) (14838051712 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 3) <| besselDerivativeNearFromState (232561533424187 / 8000000000000) 3 (IntervalRat.scale (541 / 4) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-147970727714 / 1000000000000) (-147970727692 / 1000000000000), orderedInterval (3456300717 / 1000000000000) (3456300739 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 3) <| besselDerivativeNearFromState (624692991263039 / 8000000000000) 3 (IntervalRat.scale (541 / 4) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-29310039922 / 1000000000000) (-29310039921 / 1000000000000), orderedInterval (-85216027071 / 1000000000000) (-85216027070 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 3) <| besselDerivativeNearFromState (1696162991372163 / 8000000000000) 3 (IntervalRat.scale (541 / 4) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-40180425613 / 1000000000000) (-40180363306 / 1000000000000), orderedInterval (37352877491 / 1000000000000) (37352939797 / 1000000000000)))) (orderedInterval (10877744871 / 1000000000000) (10877762053 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 3) <| besselDerivativeNearFromState (1249385982526619 / 8000000000000) 3 (IntervalRat.scale (541 / 4) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-7756445035 / 1000000000000) (-7756445007 / 1000000000000), orderedInterval (63398539615 / 1000000000000) (63398539643 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 3) <| besselDerivativeNearFromState (2140844176161287 / 8000000000000) 3 (IntervalRat.scale (541 / 4) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-47643968570 / 1000000000000) (-47643968566 / 1000000000000), orderedInterval (-10351146577 / 1000000000000) (-10351146573 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 3) <| besselDerivativeNearFromState (1576936130592533 / 8000000000000) 3 (IntervalRat.scale (541 / 4) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (1054522774 / 1000000000000) (1054522778 / 1000000000000), orderedInterval (-56823027064 / 1000000000000) (-56823027060 / 1000000000000)))) (orderedInterval (1821080906 / 1000000000000) (1821080950 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate260_chunkChecks3_1 :
    compactCertificate260.chunkChecks (3 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 3) <| besselDerivativeNearFromState (2419425551654459 / 8000000000000) 3 (IntervalRat.scale (541 / 4) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (45824380970 / 1000000000000) (45824381247 / 1000000000000), orderedInterval (-2345361464 / 1000000000000) (-2345361187 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 3) <| besselDerivativeNearFromState (1396855993531811 / 8000000000000) 3 (IntervalRat.scale (541 / 4) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-30915419889 / 1000000000000) (-30915414998 / 1000000000000), orderedInterval (51956234577 / 1000000000000) (51956239468 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 3) <| besselDerivativeNearFromState (2478745473003199 / 8000000000000) 3 (IntervalRat.scale (541 / 4) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (17212046949 / 1000000000000) (17212047349 / 1000000000000), orderedInterval (-41961042364 / 1000000000000) (-41961041964 / 1000000000000)))) (orderedInterval (58540164376 / 1000000000000) (58540166921 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 3) <| besselDerivativeNearFromState (2315965555285531 / 8000000000000) 3 (IntervalRat.scale (541 / 4) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (44562615555 / 1000000000000) (44562615556 / 1000000000000), orderedInterval (14525615760 / 1000000000000) (14525615762 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 3) <| besselDerivativeNearFromState (1652782300646923 / 8000000000000) 3 (IntervalRat.scale (541 / 4) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (2079253213 / 1000000000000) (2079253215 / 1000000000000), orderedInterval (55466861327 / 1000000000000) (55466861329 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 3) <| besselDerivativeNearFromState (1874078973789117 / 8000000000000) 3 (IntervalRat.scale (541 / 4) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (28337724831 / 1000000000000) (28337730102 / 1000000000000), orderedInterval (-43816114049 / 1000000000000) (-43816108778 / 1000000000000)))) (orderedInterval (-17301507441 / 1000000000000) (-17301507226 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 3) <| besselDerivativeNearFromState (1562411665790573 / 8000000000000) 3 (IntervalRat.scale (541 / 4) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (55125478108 / 1000000000000) (55125478110 / 1000000000000), orderedInterval (14719892732 / 1000000000000) (14719892733 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 3) <| besselDerivativeNearFromState (1380438089918033 / 8000000000000) 3 (IntervalRat.scale (541 / 4) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-31843264575 / 1000000000000) (-31843264574 / 1000000000000), orderedInterval (-51631919130 / 1000000000000) (-51631919129 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 3) <| besselDerivativeNearFromState (400104763617267 / 1600000000000) 3 (IntervalRat.scale (541 / 4) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-23166806640 / 1000000000000) (-23166804982 / 1000000000000), orderedInterval (44869465895 / 1000000000000) (44869467553 / 1000000000000)))) (orderedInterval (-13891568014 / 1000000000000) (-13891567701 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate260_chunkChecks3_2 :
    compactCertificate260.chunkChecks (3 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 3) <| besselDerivativeNearFromState (1106710832525449 / 8000000000000) 3 (IntervalRat.scale (541 / 4) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (52853626763 / 1000000000000) (52853626764 / 1000000000000), orderedInterval (42333961934 / 1000000000000) (42333961935 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 3) <| besselDerivativeNearFromState (938171029218689 / 8000000000000) 3 (IntervalRat.scale (541 / 4) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-71460813118 / 1000000000000) (-71460812116 / 1000000000000), orderedInterval (18246578645 / 1000000000000) (18246579647 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 3) <| besselDerivativeNearFromState (587063869407467 / 8000000000000) 3 (IntervalRat.scale (541 / 4) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-87831626534 / 1000000000000) (-87831624246 / 1000000000000), orderedInterval (31594448931 / 1000000000000) (31594451219 / 1000000000000)))) (orderedInterval (7702352576 / 1000000000000) (7702352655 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 3) <| besselDerivativeNearFromState (315724901453589 / 8000000000000) 3 (IntervalRat.scale (541 / 4) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (70960909561 / 1000000000000) (70960926135 / 1000000000000), orderedInterval (-106236596020 / 1000000000000) (-106236579446 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 3) <| besselDerivativeNearFromState (857254524687767 / 8000000000000) 3 (IntervalRat.scale (541 / 4) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (69607481005 / 1000000000000) (69607481006 / 1000000000000), orderedInterval (32777606097 / 1000000000000) (32777606098 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 3) <| besselDerivativeNearFromState (1170507764517559 / 8000000000000) 3 (IntervalRat.scale (541 / 4) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (34861567273 / 1000000000000) (34861574204 / 1000000000000), orderedInterval (-56116898336 / 1000000000000) (-56116891405 / 1000000000000)))) (orderedInterval (-5154500500 / 1000000000000) (-5154499800 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 3) <| besselDerivativeNearFromState (494936130592533 / 8000000000000) 3 (IntervalRat.scale (541 / 4) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-18306080970 / 1000000000000) (-18306080839 / 1000000000000), orderedInterval (99924355197 / 1000000000000) (99924355328 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 3) <| besselDerivativeNearFromState (2011887892826293 / 8000000000000) 3 (IntervalRat.scale (541 / 4) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (40733791974 / 1000000000000) (40733791975 / 1000000000000), orderedInterval (29451860689 / 1000000000000) (29451860690 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 3) <| besselDerivativeNearFromState (1343847873347387 / 8000000000000) 3 (IntervalRat.scale (541 / 4) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-47462191704 / 1000000000000) (-47462086765 / 1000000000000), orderedInterval (39348031238 / 1000000000000) (39348136176 / 1000000000000)))) (orderedInterval (29514568906 / 1000000000000) (29514606971 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate260_chunkChecks3 :
    compactCertificate260.chunkChecks (3 : Fin 5) 0 9 = true :=
  compactCertificate260.chunkChecks_nine_of_three (3 : Fin 5) compactCertificate260_chunkChecks3_0
    compactCertificate260_chunkChecks3_1 compactCertificate260_chunkChecks3_2

theorem compactCertificate260_chunkChecks4_0 :
    compactCertificate260.chunkChecks (4 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 4) <| besselDerivativeNearFromState (541 / 4) 4 (IntervalRat.scale (541 / 4) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-55645708590 / 1000000000000) (-55645708589 / 1000000000000), orderedInterval (-39925701934 / 1000000000000) (-39925701933 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 4) <| besselDerivativeNearFromState (796996302814441 / 8000000000000) 4 (IntervalRat.scale (541 / 4) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-9750778576 / 1000000000000) (-9750778533 / 1000000000000), orderedInterval (79391175201 / 1000000000000) (79391175244 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 4) <| besselDerivativeNearFromState (257732229007753 / 1600000000000) 4 (IntervalRat.scale (541 / 4) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-62687951495 / 1000000000000) (-62687951345 / 1000000000000), orderedInterval (4920396163 / 1000000000000) (4920396313 / 1000000000000)))) (orderedInterval (-29702318643 / 1000000000000) (-29702318608 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 4) <| besselDerivativeNearFromState (232561533424187 / 8000000000000) 4 (IntervalRat.scale (541 / 4) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-147970727714 / 1000000000000) (-147970727692 / 1000000000000), orderedInterval (3456300717 / 1000000000000) (3456300739 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 4) <| besselDerivativeNearFromState (624692991263039 / 8000000000000) 4 (IntervalRat.scale (541 / 4) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-29310039922 / 1000000000000) (-29310039921 / 1000000000000), orderedInterval (-85216027071 / 1000000000000) (-85216027070 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 4) <| besselDerivativeNearFromState (1696162991372163 / 8000000000000) 4 (IntervalRat.scale (541 / 4) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-40180425613 / 1000000000000) (-40180363306 / 1000000000000), orderedInterval (37352877491 / 1000000000000) (37352939797 / 1000000000000)))) (orderedInterval (16972998816 / 1000000000000) (16973025875 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 4) <| besselDerivativeNearFromState (1249385982526619 / 8000000000000) 4 (IntervalRat.scale (541 / 4) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-7756445035 / 1000000000000) (-7756445007 / 1000000000000), orderedInterval (63398539615 / 1000000000000) (63398539643 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 4) <| besselDerivativeNearFromState (2140844176161287 / 8000000000000) 4 (IntervalRat.scale (541 / 4) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-47643968570 / 1000000000000) (-47643968566 / 1000000000000), orderedInterval (-10351146577 / 1000000000000) (-10351146573 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 4) <| besselDerivativeNearFromState (1576936130592533 / 8000000000000) 4 (IntervalRat.scale (541 / 4) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (1054522774 / 1000000000000) (1054522778 / 1000000000000), orderedInterval (-56823027064 / 1000000000000) (-56823027060 / 1000000000000)))) (orderedInterval (22609889326 / 1000000000000) (22609889408 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate260_chunkChecks4_1 :
    compactCertificate260.chunkChecks (4 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 4) <| besselDerivativeNearFromState (2419425551654459 / 8000000000000) 4 (IntervalRat.scale (541 / 4) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (45824380970 / 1000000000000) (45824381247 / 1000000000000), orderedInterval (-2345361464 / 1000000000000) (-2345361187 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 4) <| besselDerivativeNearFromState (1396855993531811 / 8000000000000) 4 (IntervalRat.scale (541 / 4) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-30915419889 / 1000000000000) (-30915414998 / 1000000000000), orderedInterval (51956234577 / 1000000000000) (51956239468 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 4) <| besselDerivativeNearFromState (2478745473003199 / 8000000000000) 4 (IntervalRat.scale (541 / 4) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (17212046949 / 1000000000000) (17212047349 / 1000000000000), orderedInterval (-41961042364 / 1000000000000) (-41961041964 / 1000000000000)))) (orderedInterval (-143394419230 / 1000000000000) (-143394414237 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 4) <| besselDerivativeNearFromState (2315965555285531 / 8000000000000) 4 (IntervalRat.scale (541 / 4) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (44562615555 / 1000000000000) (44562615556 / 1000000000000), orderedInterval (14525615760 / 1000000000000) (14525615762 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 4) <| besselDerivativeNearFromState (1652782300646923 / 8000000000000) 4 (IntervalRat.scale (541 / 4) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (2079253213 / 1000000000000) (2079253215 / 1000000000000), orderedInterval (55466861327 / 1000000000000) (55466861329 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 4) <| besselDerivativeNearFromState (1874078973789117 / 8000000000000) 4 (IntervalRat.scale (541 / 4) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (28337724831 / 1000000000000) (28337730102 / 1000000000000), orderedInterval (-43816114049 / 1000000000000) (-43816108778 / 1000000000000)))) (orderedInterval (-16850692112 / 1000000000000) (-16850691741 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 4) <| besselDerivativeNearFromState (1562411665790573 / 8000000000000) 4 (IntervalRat.scale (541 / 4) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (55125478108 / 1000000000000) (55125478110 / 1000000000000), orderedInterval (14719892732 / 1000000000000) (14719892733 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 4) <| besselDerivativeNearFromState (1380438089918033 / 8000000000000) 4 (IntervalRat.scale (541 / 4) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-31843264575 / 1000000000000) (-31843264574 / 1000000000000), orderedInterval (-51631919130 / 1000000000000) (-51631919129 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 4) <| besselDerivativeNearFromState (400104763617267 / 1600000000000) 4 (IntervalRat.scale (541 / 4) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-23166806640 / 1000000000000) (-23166804982 / 1000000000000), orderedInterval (44869465895 / 1000000000000) (44869467553 / 1000000000000)))) (orderedInterval (869391235 / 1000000000000) (869391804 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate260_chunkChecks4_2 :
    compactCertificate260.chunkChecks (4 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 4) <| besselDerivativeNearFromState (1106710832525449 / 8000000000000) 4 (IntervalRat.scale (541 / 4) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (52853626763 / 1000000000000) (52853626764 / 1000000000000), orderedInterval (42333961934 / 1000000000000) (42333961935 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 4) <| besselDerivativeNearFromState (938171029218689 / 8000000000000) 4 (IntervalRat.scale (541 / 4) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-71460813118 / 1000000000000) (-71460812116 / 1000000000000), orderedInterval (18246578645 / 1000000000000) (18246579647 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 4) <| besselDerivativeNearFromState (587063869407467 / 8000000000000) 4 (IntervalRat.scale (541 / 4) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-87831626534 / 1000000000000) (-87831624246 / 1000000000000), orderedInterval (31594448931 / 1000000000000) (31594451219 / 1000000000000)))) (orderedInterval (-7324946751 / 1000000000000) (-7324946682 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 4) <| besselDerivativeNearFromState (315724901453589 / 8000000000000) 4 (IntervalRat.scale (541 / 4) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (70960909561 / 1000000000000) (70960926135 / 1000000000000), orderedInterval (-106236596020 / 1000000000000) (-106236579446 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 4) <| besselDerivativeNearFromState (857254524687767 / 8000000000000) 4 (IntervalRat.scale (541 / 4) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (69607481005 / 1000000000000) (69607481006 / 1000000000000), orderedInterval (32777606097 / 1000000000000) (32777606098 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 4) <| besselDerivativeNearFromState (1170507764517559 / 8000000000000) 4 (IntervalRat.scale (541 / 4) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (34861567273 / 1000000000000) (34861574204 / 1000000000000), orderedInterval (-56116898336 / 1000000000000) (-56116891405 / 1000000000000)))) (orderedInterval (-4214477700 / 1000000000000) (-4214476944 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 4) <| besselDerivativeNearFromState (494936130592533 / 8000000000000) 4 (IntervalRat.scale (541 / 4) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-18306080970 / 1000000000000) (-18306080839 / 1000000000000), orderedInterval (99924355197 / 1000000000000) (99924355328 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 4) <| besselDerivativeNearFromState (2011887892826293 / 8000000000000) 4 (IntervalRat.scale (541 / 4) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (40733791974 / 1000000000000) (40733791975 / 1000000000000), orderedInterval (29451860689 / 1000000000000) (29451860690 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 4) <| besselDerivativeNearFromState (1343847873347387 / 8000000000000) 4 (IntervalRat.scale (541 / 4) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-47462191704 / 1000000000000) (-47462086765 / 1000000000000), orderedInterval (39348031238 / 1000000000000) (39348136176 / 1000000000000)))) (orderedInterval (-18887769475 / 1000000000000) (-18887721877 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate260_chunkChecks4 :
    compactCertificate260.chunkChecks (4 : Fin 5) 0 9 = true :=
  compactCertificate260.chunkChecks_nine_of_three (4 : Fin 5) compactCertificate260_chunkChecks4_0
    compactCertificate260_chunkChecks4_1 compactCertificate260_chunkChecks4_2

theorem compactCertificate260_chunks :
    ∀ r : Fin 5, ∀ b, compactCertificate260.chunkCheck r b = true :=
  compactCertificate260.chunkChecks_all (by
    intro r
    fin_cases r
    · exact compactCertificate260_chunkChecks0
    · exact compactCertificate260_chunkChecks1
    · exact compactCertificate260_chunkChecks2
    · exact compactCertificate260_chunkChecks3
    · exact compactCertificate260_chunkChecks4)

theorem compactCertificate260_coefficient0 :
    compactCertificate260.coefficientCheck (0 : Fin 5) = true := by
  norm_num [CompactCertificate.coefficientCheck, intervalFinSumHull,
    compactCertificate260, rationalIntervalSubset, orderedInterval, Fin.sum_univ_succ]

theorem compactCertificate260_coefficient1 :
    compactCertificate260.coefficientCheck (1 : Fin 5) = true := by
  norm_num [CompactCertificate.coefficientCheck, intervalFinSumHull,
    compactCertificate260, rationalIntervalSubset, orderedInterval, Fin.sum_univ_succ]

theorem compactCertificate260_coefficient2 :
    compactCertificate260.coefficientCheck (2 : Fin 5) = true := by
  norm_num [CompactCertificate.coefficientCheck, intervalFinSumHull,
    compactCertificate260, rationalIntervalSubset, orderedInterval, Fin.sum_univ_succ]

theorem compactCertificate260_coefficient3 :
    compactCertificate260.coefficientCheck (3 : Fin 5) = true := by
  norm_num [CompactCertificate.coefficientCheck, intervalFinSumHull,
    compactCertificate260, rationalIntervalSubset, orderedInterval, Fin.sum_univ_succ]

theorem compactCertificate260_coefficient4 :
    compactCertificate260.coefficientCheck (4 : Fin 5) = true := by
  norm_num [CompactCertificate.coefficientCheck, intervalFinSumHull,
    compactCertificate260, rationalIntervalSubset, orderedInterval, Fin.sum_univ_succ]

theorem compactCertificate260_coefficients : ∀ r : Fin 5,
    compactCertificate260.coefficientCheck r = true := by
  intro r
  fin_cases r
  · exact compactCertificate260_coefficient0
  · exact compactCertificate260_coefficient1
  · exact compactCertificate260_coefficient2
  · exact compactCertificate260_coefficient3
  · exact compactCertificate260_coefficient4

theorem compactCertificate260_lower : (1 : ℚ) ≤ compactCertificate260.output.lo := by
  norm_num [CompactCertificate.output, CompactCertificate.interval,
    CompactCertificate.coefficientTargetNat, compactCertificate260, dualConstant,
    intervalTaylorSum, intervalPow, intervalSub, intervalMaxAbs, widenInterval,
    rationalErrorInterval, orderedInterval, IntervalRat.add, IntervalRat.mul, IntervalRat.scale,
    IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4]

theorem compactCertificate260_proves {t : ℝ} (ht : t ∈ compactCertificate260.interval) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t :=
  compactCertificate260.proves compactCertificate260_states compactCertificate260_chunks
    compactCertificate260_coefficients compactCertificate260_lower ht

end Erdos232
