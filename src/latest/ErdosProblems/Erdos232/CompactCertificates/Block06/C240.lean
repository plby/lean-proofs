/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, OpenAI Codex
-/
import ErdosProblems.Erdos232.CompactBase

open LeanCert.Core
namespace Erdos232

def compactCertificate240 : CompactCertificate where
  left := 233 / 2
  right := 117
  center := 467 / 4
  grid := fun i =>
    match i.val with
    | 0 => 37
    | 1 => 27
    | 2 => 44
    | 3 => 8
    | 4 => 21
    | 5 => 58
    | 6 => 43
    | 7 => 74
    | 8 => 54
    | 9 => 83
    | 10 => 48
    | 11 => 85
    | 12 => 80
    | 13 => 57
    | 14 => 64
    | 15 => 54
    | 16 => 47
    | 17 => 69
    | 18 => 38
    | 19 => 32
    | 20 => 20
    | 21 => 11
    | 22 => 29
    | 23 => 40
    | 24 => 17
    | 25 => 69
    | _ => 46
  point := fun i =>
    match i.val with
    | 0 => 467 / 4
    | 1 => 687980172669767 / 8000000000000
    | 2 => 222478652396711 / 1600000000000
    | 3 => 200750898538069 / 8000000000000
    | 4 => 539245151422993 / 8000000000000
    | 5 => 1464155484234381 / 8000000000000
    | 6 => 1078490302846453 / 8000000000000
    | 7 => 1848011516205769 / 8000000000000
    | 8 => 1361236918644571 / 8000000000000
    | 9 => 2088487490984533 / 8000000000000
    | 10 => 1205788815118957 / 8000000000000
    | 11 => 2139693412000913 / 8000000000000
    | 12 => 1999179139220597 / 8000000000000
    | 13 => 1426708566362501 / 8000000000000
    | 14 => 1617735454268979 / 8000000000000
    | 15 => 1348699164370051 / 8000000000000
    | 16 => 1191616613663071 / 8000000000000
    | 17 => 345376940128029 / 1600000000000
    | 18 => 955330792586663 / 8000000000000
    | 19 => 809844492874543 / 8000000000000
    | 20 => 506763081355429 / 8000000000000
    | 21 => 272538870570843 / 8000000000000
    | 22 => 739996049961529 / 8000000000000
    | 23 => 1010401342014233 / 8000000000000
    | 24 => 427236918644571 / 8000000000000
    | 25 => 1736694354805691 / 8000000000000
    | _ => 1160031343536469 / 8000000000000
  state := fun i =>
    match i.val with
    | 0 => (orderedInterval (-71060446314 / 1000000000000) (-71060446313 / 1000000000000), orderedInterval (-19775926709 / 1000000000000) (-19775926708 / 1000000000000))
    | 1 => (orderedInterval (-79653953087 / 1000000000000) (-79653948937 / 1000000000000), orderedInterval (32988898269 / 1000000000000) (32988902419 / 1000000000000))
    | 2 => (orderedInterval (67627144198 / 1000000000000) (67627144268 / 1000000000000), orderedInterval (-2461063704 / 1000000000000) (-2461063633 / 1000000000000))
    | 3 => (orderedInterval (107569958349 / 1000000000000) (107569958350 / 1000000000000), orderedInterval (115325301804 / 1000000000000) (115325301805 / 1000000000000))
    | 4 => (orderedInterval (-77661324036 / 1000000000000) (-77661277784 / 1000000000000), orderedInterval (58999099292 / 1000000000000) (58999145544 / 1000000000000))
    | 5 => (orderedInterval (58965101992 / 1000000000000) (58965102074 / 1000000000000), orderedInterval (-1398390919 / 1000000000000) (-1398390837 / 1000000000000))
    | 6 => (orderedInterval (-33383374540 / 1000000000000) (-33383374539 / 1000000000000), orderedInterval (-59941739230 / 1000000000000) (-59941739229 / 1000000000000))
    | 7 => (orderedInterval (-33479237640 / 1000000000000) (-33479220389 / 1000000000000), orderedInterval (40508269289 / 1000000000000) (40508286540 / 1000000000000))
    | 8 => (orderedInterval (58826608415 / 1000000000000) (58826608416 / 1000000000000), orderedInterval (16585295141 / 1000000000000) (16585295142 / 1000000000000))
    | 9 => (orderedInterval (-43866834069 / 1000000000000) (-43866834068 / 1000000000000), orderedInterval (-22593839898 / 1000000000000) (-22593839897 / 1000000000000))
    | 10 => (orderedInterval (42447717542 / 1000000000000) (42447717543 / 1000000000000), orderedInterval (49072510308 / 1000000000000) (49072510309 / 1000000000000))
    | 11 => (orderedInterval (-45667580865 / 1000000000000) (-45667580864 / 1000000000000), orderedInterval (-17081367243 / 1000000000000) (-17081367242 / 1000000000000))
    | 12 => (orderedInterval (-30349186073 / 1000000000000) (-30349176088 / 1000000000000), orderedInterval (40390028318 / 1000000000000) (40390038303 / 1000000000000))
    | 13 => (orderedInterval (-3134492636 / 1000000000000) (-3134492634 / 1000000000000), orderedInterval (-59656231666 / 1000000000000) (-59656231664 / 1000000000000))
    | 14 => (orderedInterval (52332278249 / 1000000000000) (52332284527 / 1000000000000), orderedInterval (-20366179668 / 1000000000000) (-20366173389 / 1000000000000))
    | 15 => (orderedInterval (-16624691512 / 1000000000000) (-16624691287 / 1000000000000), orderedInterval (59208701044 / 1000000000000) (59208701269 / 1000000000000))
    | 16 => (orderedInterval (-57024735419 / 1000000000000) (-57024715799 / 1000000000000), orderedInterval (32162623026 / 1000000000000) (32162642646 / 1000000000000))
    | 17 => (orderedInterval (6742990007 / 1000000000000) (6742990025 / 1000000000000), orderedInterval (-53902138625 / 1000000000000) (-53902138607 / 1000000000000))
    | 18 => (orderedInterval (53392845964 / 1000000000000) (53392845965 / 1000000000000), orderedInterval (49579003271 / 1000000000000) (49579003272 / 1000000000000))
    | 19 => (orderedInterval (79001357332 / 1000000000000) (79001357341 / 1000000000000), orderedInterval (6503282644 / 1000000000000) (6503282652 / 1000000000000))
    | 20 => (orderedInterval (96512758233 / 1000000000000) (96512758234 / 1000000000000), orderedInterval (26349115285 / 1000000000000) (26349115286 / 1000000000000))
    | 21 => (orderedInterval (-39293405426 / 1000000000000) (-39293405425 / 1000000000000), orderedInterval (-130361557582 / 1000000000000) (-130361557581 / 1000000000000))
    | 22 => (orderedInterval (-68160389708 / 1000000000000) (-68160353103 / 1000000000000), orderedInterval (47660489056 / 1000000000000) (47660525661 / 1000000000000))
    | 23 => (orderedInterval (70199980564 / 1000000000000) (70199980568 / 1000000000000), orderedInterval (10326570538 / 1000000000000) (10326570542 / 1000000000000))
    | 24 => (orderedInterval (-76830082255 / 1000000000000) (-76830082254 / 1000000000000), orderedInterval (-76855428189 / 1000000000000) (-76855428188 / 1000000000000))
    | 25 => (orderedInterval (-48303847782 / 1000000000000) (-48303847781 / 1000000000000), orderedInterval (-24369195512 / 1000000000000) (-24369195511 / 1000000000000))
    | _ => (orderedInterval (63385687518 / 1000000000000) (63385687520 / 1000000000000), orderedInterval (19084170364 / 1000000000000) (19084170365 / 1000000000000))
  chunkTarget := fun r b =>
    match r.val with
    | 0 =>
      match b.val with
      | 0 => orderedInterval (-24939655708 / 1000000000000) (-24939655656 / 1000000000000)
      | 1 => orderedInterval (-8194416264 / 1000000000000) (-8194414554 / 1000000000000)
      | 2 => orderedInterval (2454356164 / 1000000000000) (2454356703 / 1000000000000)
      | 3 => orderedInterval (4447717616 / 1000000000000) (4447717664 / 1000000000000)
      | 4 => orderedInterval (-13341832 / 1000000000000) (-13341605 / 1000000000000)
      | 5 => orderedInterval (3244005714 / 1000000000000) (3244006851 / 1000000000000)
      | 6 => orderedInterval (-9866586892 / 1000000000000) (-9866586861 / 1000000000000)
      | 7 => orderedInterval (-3108145339 / 1000000000000) (-3108144493 / 1000000000000)
      | _ => orderedInterval (-8423974318 / 1000000000000) (-8423974285 / 1000000000000)
    | 1 =>
      match b.val with
      | 0 => orderedInterval (-7784062860 / 1000000000000) (-7784062816 / 1000000000000)
      | 1 => orderedInterval (1130615239 / 1000000000000) (1130616240 / 1000000000000)
      | 2 => orderedInterval (-1887949985 / 1000000000000) (-1887948920 / 1000000000000)
      | 3 => orderedInterval (8108139281 / 1000000000000) (8108139378 / 1000000000000)
      | 4 => orderedInterval (-9999400375 / 1000000000000) (-9999399910 / 1000000000000)
      | 5 => orderedInterval (-3912627468 / 1000000000000) (-3912626014 / 1000000000000)
      | 6 => orderedInterval (-7962088543 / 1000000000000) (-7962088514 / 1000000000000)
      | 7 => orderedInterval (-1010431237 / 1000000000000) (-1010430565 / 1000000000000)
      | _ => orderedInterval (-970653113 / 1000000000000) (-970653067 / 1000000000000)
    | 2 =>
      match b.val with
      | 0 => orderedInterval (23006108496 / 1000000000000) (23006108534 / 1000000000000)
      | 1 => orderedInterval (11290476798 / 1000000000000) (11290477406 / 1000000000000)
      | 2 => orderedInterval (-7046312399 / 1000000000000) (-7046310286 / 1000000000000)
      | 3 => orderedInterval (-10213402500 / 1000000000000) (-10213402292 / 1000000000000)
      | 4 => orderedInterval (-938441325 / 1000000000000) (-938440361 / 1000000000000)
      | 5 => orderedInterval (-5468172193 / 1000000000000) (-5468170321 / 1000000000000)
      | 6 => orderedInterval (11436456929 / 1000000000000) (11436456956 / 1000000000000)
      | 7 => orderedInterval (5272430498 / 1000000000000) (5272431038 / 1000000000000)
      | _ => orderedInterval (4856122487 / 1000000000000) (4856122556 / 1000000000000)
    | 3 =>
      match b.val with
      | 0 => orderedInterval (7761988882 / 1000000000000) (7761988918 / 1000000000000)
      | 1 => orderedInterval (-881730429 / 1000000000000) (-881730043 / 1000000000000)
      | 2 => orderedInterval (8497397541 / 1000000000000) (8497401718 / 1000000000000)
      | 3 => orderedInterval (-23425717600 / 1000000000000) (-23425717144 / 1000000000000)
      | 4 => orderedInterval (26729064090 / 1000000000000) (26729066096 / 1000000000000)
      | 5 => orderedInterval (10533068757 / 1000000000000) (10533071152 / 1000000000000)
      | 6 => orderedInterval (8487332431 / 1000000000000) (8487332458 / 1000000000000)
      | 7 => orderedInterval (1434660368 / 1000000000000) (1434660800 / 1000000000000)
      | _ => orderedInterval (-5889905376 / 1000000000000) (-5889905271 / 1000000000000)
    | _ =>
      match b.val with
      | 0 => orderedInterval (-20530820563 / 1000000000000) (-20530820527 / 1000000000000)
      | 1 => orderedInterval (-25615729901 / 1000000000000) (-25615729621 / 1000000000000)
      | 2 => orderedInterval (22094633345 / 1000000000000) (22094641639 / 1000000000000)
      | 3 => orderedInterval (25191994559 / 1000000000000) (25191995569 / 1000000000000)
      | 4 => orderedInterval (7045324864 / 1000000000000) (7045329078 / 1000000000000)
      | 5 => orderedInterval (9648138444 / 1000000000000) (9648141535 / 1000000000000)
      | 6 => orderedInterval (-11743754263 / 1000000000000) (-11743754237 / 1000000000000)
      | 7 => orderedInterval (-6778039472 / 1000000000000) (-6778039123 / 1000000000000)
      | _ => orderedInterval (18784180463 / 1000000000000) (18784180632 / 1000000000000)
  coefficientTarget := fun i =>
    match i.val with
    | 0 => orderedInterval (-44400040859 / 1000000000000) (-44400036236 / 1000000000000)
    | 1 => orderedInterval (-24288459061 / 1000000000000) (-24288454188 / 1000000000000)
    | 2 => orderedInterval (32195266791 / 1000000000000) (32195273230 / 1000000000000)
    | 3 => orderedInterval (33246158664 / 1000000000000) (33246168684 / 1000000000000)
    | _ => orderedInterval (18095927476 / 1000000000000) (18095944945 / 1000000000000)

theorem compactCertificate240_stateChecks0 :
    compactCertificate240.stateChecks 0 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 37 12 (467 / 4)) (orderedInterval (-71060446314 / 1000000000000) (-71060446313 / 1000000000000), orderedInterval (-19775926709 / 1000000000000) (-19775926708 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 27 12 (687980172669767 / 8000000000000)) (orderedInterval (-79653953087 / 1000000000000) (-79653948937 / 1000000000000), orderedInterval (32988898269 / 1000000000000) (32988902419 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 44 12 (222478652396711 / 1600000000000)) (orderedInterval (67627144198 / 1000000000000) (67627144268 / 1000000000000), orderedInterval (-2461063704 / 1000000000000) (-2461063633 / 1000000000000))) = true
  norm_num [besselStateAtRationalPoint, besselIntervalStepZero,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, besselZeroTransition,
    besselInitial, besselGridStateAt, besselGridStateBlock00, besselGridStateBlock01,
    besselGridStateBlock02, besselGridStateBlock03, besselGridStateBlock04,
    besselGridStateBlock05, besselGridStateBlock06, besselGridStateBlock07,
    besselGridStateBlock08, besselGridStateBlock09, besselGridStateBlock10,
    besselGridStateBlock11, besselGridStateBlock12, besselGridStateBlock13,
    besselGridStateBlock14, besselGridState008, besselGridState011, besselGridState017, besselGridState020, besselGridState021, besselGridState027, besselGridState029, besselGridState032, besselGridState037, besselGridState038, besselGridState040, besselGridState043, besselGridState044, besselGridState046, besselGridState047, besselGridState048, besselGridState054, besselGridState057, besselGridState058, besselGridState064, besselGridState069, besselGridState074, besselGridState080, besselGridState083, besselGridState085, besselStateSubset, linearInterval, widenInterval,
    rationalErrorInterval, rationalIntervalSubset, orderedInterval, Finset.sum_range_succ,
    IntervalRat.add, IntervalRat.mul, IntervalRat.scale, IntervalRat.singleton]

theorem compactCertificate240_stateChecks1 :
    compactCertificate240.stateChecks 3 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 8 12 (200750898538069 / 8000000000000)) (orderedInterval (107569958349 / 1000000000000) (107569958350 / 1000000000000), orderedInterval (115325301804 / 1000000000000) (115325301805 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 21 12 (539245151422993 / 8000000000000)) (orderedInterval (-77661324036 / 1000000000000) (-77661277784 / 1000000000000), orderedInterval (58999099292 / 1000000000000) (58999145544 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 58 12 (1464155484234381 / 8000000000000)) (orderedInterval (58965101992 / 1000000000000) (58965102074 / 1000000000000), orderedInterval (-1398390919 / 1000000000000) (-1398390837 / 1000000000000))) = true
  norm_num [besselStateAtRationalPoint, besselIntervalStepZero,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, besselZeroTransition,
    besselInitial, besselGridStateAt, besselGridStateBlock00, besselGridStateBlock01,
    besselGridStateBlock02, besselGridStateBlock03, besselGridStateBlock04,
    besselGridStateBlock05, besselGridStateBlock06, besselGridStateBlock07,
    besselGridStateBlock08, besselGridStateBlock09, besselGridStateBlock10,
    besselGridStateBlock11, besselGridStateBlock12, besselGridStateBlock13,
    besselGridStateBlock14, besselGridState008, besselGridState011, besselGridState017, besselGridState020, besselGridState021, besselGridState027, besselGridState029, besselGridState032, besselGridState037, besselGridState038, besselGridState040, besselGridState043, besselGridState044, besselGridState046, besselGridState047, besselGridState048, besselGridState054, besselGridState057, besselGridState058, besselGridState064, besselGridState069, besselGridState074, besselGridState080, besselGridState083, besselGridState085, besselStateSubset, linearInterval, widenInterval,
    rationalErrorInterval, rationalIntervalSubset, orderedInterval, Finset.sum_range_succ,
    IntervalRat.add, IntervalRat.mul, IntervalRat.scale, IntervalRat.singleton]

theorem compactCertificate240_stateChecks2 :
    compactCertificate240.stateChecks 6 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 43 12 (1078490302846453 / 8000000000000)) (orderedInterval (-33383374540 / 1000000000000) (-33383374539 / 1000000000000), orderedInterval (-59941739230 / 1000000000000) (-59941739229 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 74 12 (1848011516205769 / 8000000000000)) (orderedInterval (-33479237640 / 1000000000000) (-33479220389 / 1000000000000), orderedInterval (40508269289 / 1000000000000) (40508286540 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 54 12 (1361236918644571 / 8000000000000)) (orderedInterval (58826608415 / 1000000000000) (58826608416 / 1000000000000), orderedInterval (16585295141 / 1000000000000) (16585295142 / 1000000000000))) = true
  norm_num [besselStateAtRationalPoint, besselIntervalStepZero,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, besselZeroTransition,
    besselInitial, besselGridStateAt, besselGridStateBlock00, besselGridStateBlock01,
    besselGridStateBlock02, besselGridStateBlock03, besselGridStateBlock04,
    besselGridStateBlock05, besselGridStateBlock06, besselGridStateBlock07,
    besselGridStateBlock08, besselGridStateBlock09, besselGridStateBlock10,
    besselGridStateBlock11, besselGridStateBlock12, besselGridStateBlock13,
    besselGridStateBlock14, besselGridState008, besselGridState011, besselGridState017, besselGridState020, besselGridState021, besselGridState027, besselGridState029, besselGridState032, besselGridState037, besselGridState038, besselGridState040, besselGridState043, besselGridState044, besselGridState046, besselGridState047, besselGridState048, besselGridState054, besselGridState057, besselGridState058, besselGridState064, besselGridState069, besselGridState074, besselGridState080, besselGridState083, besselGridState085, besselStateSubset, linearInterval, widenInterval,
    rationalErrorInterval, rationalIntervalSubset, orderedInterval, Finset.sum_range_succ,
    IntervalRat.add, IntervalRat.mul, IntervalRat.scale, IntervalRat.singleton]

theorem compactCertificate240_stateChecks3 :
    compactCertificate240.stateChecks 9 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 83 12 (2088487490984533 / 8000000000000)) (orderedInterval (-43866834069 / 1000000000000) (-43866834068 / 1000000000000), orderedInterval (-22593839898 / 1000000000000) (-22593839897 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 48 12 (1205788815118957 / 8000000000000)) (orderedInterval (42447717542 / 1000000000000) (42447717543 / 1000000000000), orderedInterval (49072510308 / 1000000000000) (49072510309 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 85 12 (2139693412000913 / 8000000000000)) (orderedInterval (-45667580865 / 1000000000000) (-45667580864 / 1000000000000), orderedInterval (-17081367243 / 1000000000000) (-17081367242 / 1000000000000))) = true
  norm_num [besselStateAtRationalPoint, besselIntervalStepZero,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, besselZeroTransition,
    besselInitial, besselGridStateAt, besselGridStateBlock00, besselGridStateBlock01,
    besselGridStateBlock02, besselGridStateBlock03, besselGridStateBlock04,
    besselGridStateBlock05, besselGridStateBlock06, besselGridStateBlock07,
    besselGridStateBlock08, besselGridStateBlock09, besselGridStateBlock10,
    besselGridStateBlock11, besselGridStateBlock12, besselGridStateBlock13,
    besselGridStateBlock14, besselGridState008, besselGridState011, besselGridState017, besselGridState020, besselGridState021, besselGridState027, besselGridState029, besselGridState032, besselGridState037, besselGridState038, besselGridState040, besselGridState043, besselGridState044, besselGridState046, besselGridState047, besselGridState048, besselGridState054, besselGridState057, besselGridState058, besselGridState064, besselGridState069, besselGridState074, besselGridState080, besselGridState083, besselGridState085, besselStateSubset, linearInterval, widenInterval,
    rationalErrorInterval, rationalIntervalSubset, orderedInterval, Finset.sum_range_succ,
    IntervalRat.add, IntervalRat.mul, IntervalRat.scale, IntervalRat.singleton]

theorem compactCertificate240_stateChecks4 :
    compactCertificate240.stateChecks 12 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 80 12 (1999179139220597 / 8000000000000)) (orderedInterval (-30349186073 / 1000000000000) (-30349176088 / 1000000000000), orderedInterval (40390028318 / 1000000000000) (40390038303 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 57 12 (1426708566362501 / 8000000000000)) (orderedInterval (-3134492636 / 1000000000000) (-3134492634 / 1000000000000), orderedInterval (-59656231666 / 1000000000000) (-59656231664 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 64 12 (1617735454268979 / 8000000000000)) (orderedInterval (52332278249 / 1000000000000) (52332284527 / 1000000000000), orderedInterval (-20366179668 / 1000000000000) (-20366173389 / 1000000000000))) = true
  norm_num [besselStateAtRationalPoint, besselIntervalStepZero,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, besselZeroTransition,
    besselInitial, besselGridStateAt, besselGridStateBlock00, besselGridStateBlock01,
    besselGridStateBlock02, besselGridStateBlock03, besselGridStateBlock04,
    besselGridStateBlock05, besselGridStateBlock06, besselGridStateBlock07,
    besselGridStateBlock08, besselGridStateBlock09, besselGridStateBlock10,
    besselGridStateBlock11, besselGridStateBlock12, besselGridStateBlock13,
    besselGridStateBlock14, besselGridState008, besselGridState011, besselGridState017, besselGridState020, besselGridState021, besselGridState027, besselGridState029, besselGridState032, besselGridState037, besselGridState038, besselGridState040, besselGridState043, besselGridState044, besselGridState046, besselGridState047, besselGridState048, besselGridState054, besselGridState057, besselGridState058, besselGridState064, besselGridState069, besselGridState074, besselGridState080, besselGridState083, besselGridState085, besselStateSubset, linearInterval, widenInterval,
    rationalErrorInterval, rationalIntervalSubset, orderedInterval, Finset.sum_range_succ,
    IntervalRat.add, IntervalRat.mul, IntervalRat.scale, IntervalRat.singleton]

theorem compactCertificate240_stateChecks5 :
    compactCertificate240.stateChecks 15 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 54 12 (1348699164370051 / 8000000000000)) (orderedInterval (-16624691512 / 1000000000000) (-16624691287 / 1000000000000), orderedInterval (59208701044 / 1000000000000) (59208701269 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 47 12 (1191616613663071 / 8000000000000)) (orderedInterval (-57024735419 / 1000000000000) (-57024715799 / 1000000000000), orderedInterval (32162623026 / 1000000000000) (32162642646 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 69 12 (345376940128029 / 1600000000000)) (orderedInterval (6742990007 / 1000000000000) (6742990025 / 1000000000000), orderedInterval (-53902138625 / 1000000000000) (-53902138607 / 1000000000000))) = true
  norm_num [besselStateAtRationalPoint, besselIntervalStepZero,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, besselZeroTransition,
    besselInitial, besselGridStateAt, besselGridStateBlock00, besselGridStateBlock01,
    besselGridStateBlock02, besselGridStateBlock03, besselGridStateBlock04,
    besselGridStateBlock05, besselGridStateBlock06, besselGridStateBlock07,
    besselGridStateBlock08, besselGridStateBlock09, besselGridStateBlock10,
    besselGridStateBlock11, besselGridStateBlock12, besselGridStateBlock13,
    besselGridStateBlock14, besselGridState008, besselGridState011, besselGridState017, besselGridState020, besselGridState021, besselGridState027, besselGridState029, besselGridState032, besselGridState037, besselGridState038, besselGridState040, besselGridState043, besselGridState044, besselGridState046, besselGridState047, besselGridState048, besselGridState054, besselGridState057, besselGridState058, besselGridState064, besselGridState069, besselGridState074, besselGridState080, besselGridState083, besselGridState085, besselStateSubset, linearInterval, widenInterval,
    rationalErrorInterval, rationalIntervalSubset, orderedInterval, Finset.sum_range_succ,
    IntervalRat.add, IntervalRat.mul, IntervalRat.scale, IntervalRat.singleton]

theorem compactCertificate240_stateChecks6 :
    compactCertificate240.stateChecks 18 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 38 12 (955330792586663 / 8000000000000)) (orderedInterval (53392845964 / 1000000000000) (53392845965 / 1000000000000), orderedInterval (49579003271 / 1000000000000) (49579003272 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 32 12 (809844492874543 / 8000000000000)) (orderedInterval (79001357332 / 1000000000000) (79001357341 / 1000000000000), orderedInterval (6503282644 / 1000000000000) (6503282652 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 20 12 (506763081355429 / 8000000000000)) (orderedInterval (96512758233 / 1000000000000) (96512758234 / 1000000000000), orderedInterval (26349115285 / 1000000000000) (26349115286 / 1000000000000))) = true
  norm_num [besselStateAtRationalPoint, besselIntervalStepZero,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, besselZeroTransition,
    besselInitial, besselGridStateAt, besselGridStateBlock00, besselGridStateBlock01,
    besselGridStateBlock02, besselGridStateBlock03, besselGridStateBlock04,
    besselGridStateBlock05, besselGridStateBlock06, besselGridStateBlock07,
    besselGridStateBlock08, besselGridStateBlock09, besselGridStateBlock10,
    besselGridStateBlock11, besselGridStateBlock12, besselGridStateBlock13,
    besselGridStateBlock14, besselGridState008, besselGridState011, besselGridState017, besselGridState020, besselGridState021, besselGridState027, besselGridState029, besselGridState032, besselGridState037, besselGridState038, besselGridState040, besselGridState043, besselGridState044, besselGridState046, besselGridState047, besselGridState048, besselGridState054, besselGridState057, besselGridState058, besselGridState064, besselGridState069, besselGridState074, besselGridState080, besselGridState083, besselGridState085, besselStateSubset, linearInterval, widenInterval,
    rationalErrorInterval, rationalIntervalSubset, orderedInterval, Finset.sum_range_succ,
    IntervalRat.add, IntervalRat.mul, IntervalRat.scale, IntervalRat.singleton]

theorem compactCertificate240_stateChecks7 :
    compactCertificate240.stateChecks 21 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 11 12 (272538870570843 / 8000000000000)) (orderedInterval (-39293405426 / 1000000000000) (-39293405425 / 1000000000000), orderedInterval (-130361557582 / 1000000000000) (-130361557581 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 29 12 (739996049961529 / 8000000000000)) (orderedInterval (-68160389708 / 1000000000000) (-68160353103 / 1000000000000), orderedInterval (47660489056 / 1000000000000) (47660525661 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 40 12 (1010401342014233 / 8000000000000)) (orderedInterval (70199980564 / 1000000000000) (70199980568 / 1000000000000), orderedInterval (10326570538 / 1000000000000) (10326570542 / 1000000000000))) = true
  norm_num [besselStateAtRationalPoint, besselIntervalStepZero,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, besselZeroTransition,
    besselInitial, besselGridStateAt, besselGridStateBlock00, besselGridStateBlock01,
    besselGridStateBlock02, besselGridStateBlock03, besselGridStateBlock04,
    besselGridStateBlock05, besselGridStateBlock06, besselGridStateBlock07,
    besselGridStateBlock08, besselGridStateBlock09, besselGridStateBlock10,
    besselGridStateBlock11, besselGridStateBlock12, besselGridStateBlock13,
    besselGridStateBlock14, besselGridState008, besselGridState011, besselGridState017, besselGridState020, besselGridState021, besselGridState027, besselGridState029, besselGridState032, besselGridState037, besselGridState038, besselGridState040, besselGridState043, besselGridState044, besselGridState046, besselGridState047, besselGridState048, besselGridState054, besselGridState057, besselGridState058, besselGridState064, besselGridState069, besselGridState074, besselGridState080, besselGridState083, besselGridState085, besselStateSubset, linearInterval, widenInterval,
    rationalErrorInterval, rationalIntervalSubset, orderedInterval, Finset.sum_range_succ,
    IntervalRat.add, IntervalRat.mul, IntervalRat.scale, IntervalRat.singleton]

theorem compactCertificate240_stateChecks8 :
    compactCertificate240.stateChecks 24 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 17 12 (427236918644571 / 8000000000000)) (orderedInterval (-76830082255 / 1000000000000) (-76830082254 / 1000000000000), orderedInterval (-76855428189 / 1000000000000) (-76855428188 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 69 12 (1736694354805691 / 8000000000000)) (orderedInterval (-48303847782 / 1000000000000) (-48303847781 / 1000000000000), orderedInterval (-24369195512 / 1000000000000) (-24369195511 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 46 12 (1160031343536469 / 8000000000000)) (orderedInterval (63385687518 / 1000000000000) (63385687520 / 1000000000000), orderedInterval (19084170364 / 1000000000000) (19084170365 / 1000000000000))) = true
  norm_num [besselStateAtRationalPoint, besselIntervalStepZero,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, besselZeroTransition,
    besselInitial, besselGridStateAt, besselGridStateBlock00, besselGridStateBlock01,
    besselGridStateBlock02, besselGridStateBlock03, besselGridStateBlock04,
    besselGridStateBlock05, besselGridStateBlock06, besselGridStateBlock07,
    besselGridStateBlock08, besselGridStateBlock09, besselGridStateBlock10,
    besselGridStateBlock11, besselGridStateBlock12, besselGridStateBlock13,
    besselGridStateBlock14, besselGridState008, besselGridState011, besselGridState017, besselGridState020, besselGridState021, besselGridState027, besselGridState029, besselGridState032, besselGridState037, besselGridState038, besselGridState040, besselGridState043, besselGridState044, besselGridState046, besselGridState047, besselGridState048, besselGridState054, besselGridState057, besselGridState058, besselGridState064, besselGridState069, besselGridState074, besselGridState080, besselGridState083, besselGridState085, besselStateSubset, linearInterval, widenInterval,
    rationalErrorInterval, rationalIntervalSubset, orderedInterval, Finset.sum_range_succ,
    IntervalRat.add, IntervalRat.mul, IntervalRat.scale, IntervalRat.singleton]

theorem compactCertificate240_states : ∀ j,
    BesselStateValid (compactCertificate240.point j) (compactCertificate240.state j) :=
  compactCertificate240.statesValid_of_checks3 compactCertificate240_stateChecks0
    compactCertificate240_stateChecks1 compactCertificate240_stateChecks2
    compactCertificate240_stateChecks3 compactCertificate240_stateChecks4
    compactCertificate240_stateChecks5 compactCertificate240_stateChecks6
    compactCertificate240_stateChecks7 compactCertificate240_stateChecks8

theorem compactCertificate240_chunkChecks0_0 :
    compactCertificate240.chunkChecks (0 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 0) <| besselDerivativeNearFromState (467 / 4) 0 (IntervalRat.scale (467 / 4) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-71060446314 / 1000000000000) (-71060446313 / 1000000000000), orderedInterval (-19775926709 / 1000000000000) (-19775926708 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 0) <| besselDerivativeNearFromState (687980172669767 / 8000000000000) 0 (IntervalRat.scale (467 / 4) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-79653953087 / 1000000000000) (-79653948937 / 1000000000000), orderedInterval (32988898269 / 1000000000000) (32988902419 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 0) <| besselDerivativeNearFromState (222478652396711 / 1600000000000) 0 (IntervalRat.scale (467 / 4) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (67627144198 / 1000000000000) (67627144268 / 1000000000000), orderedInterval (-2461063704 / 1000000000000) (-2461063633 / 1000000000000)))) (orderedInterval (-24939655708 / 1000000000000) (-24939655656 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 0) <| besselDerivativeNearFromState (200750898538069 / 8000000000000) 0 (IntervalRat.scale (467 / 4) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (107569958349 / 1000000000000) (107569958350 / 1000000000000), orderedInterval (115325301804 / 1000000000000) (115325301805 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 0) <| besselDerivativeNearFromState (539245151422993 / 8000000000000) 0 (IntervalRat.scale (467 / 4) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-77661324036 / 1000000000000) (-77661277784 / 1000000000000), orderedInterval (58999099292 / 1000000000000) (58999145544 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 0) <| besselDerivativeNearFromState (1464155484234381 / 8000000000000) 0 (IntervalRat.scale (467 / 4) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (58965101992 / 1000000000000) (58965102074 / 1000000000000), orderedInterval (-1398390919 / 1000000000000) (-1398390837 / 1000000000000)))) (orderedInterval (-8194416264 / 1000000000000) (-8194414554 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 0) <| besselDerivativeNearFromState (1078490302846453 / 8000000000000) 0 (IntervalRat.scale (467 / 4) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-33383374540 / 1000000000000) (-33383374539 / 1000000000000), orderedInterval (-59941739230 / 1000000000000) (-59941739229 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 0) <| besselDerivativeNearFromState (1848011516205769 / 8000000000000) 0 (IntervalRat.scale (467 / 4) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-33479237640 / 1000000000000) (-33479220389 / 1000000000000), orderedInterval (40508269289 / 1000000000000) (40508286540 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 0) <| besselDerivativeNearFromState (1361236918644571 / 8000000000000) 0 (IntervalRat.scale (467 / 4) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (58826608415 / 1000000000000) (58826608416 / 1000000000000), orderedInterval (16585295141 / 1000000000000) (16585295142 / 1000000000000)))) (orderedInterval (2454356164 / 1000000000000) (2454356703 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate240_chunkChecks0_1 :
    compactCertificate240.chunkChecks (0 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 0) <| besselDerivativeNearFromState (2088487490984533 / 8000000000000) 0 (IntervalRat.scale (467 / 4) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-43866834069 / 1000000000000) (-43866834068 / 1000000000000), orderedInterval (-22593839898 / 1000000000000) (-22593839897 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 0) <| besselDerivativeNearFromState (1205788815118957 / 8000000000000) 0 (IntervalRat.scale (467 / 4) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (42447717542 / 1000000000000) (42447717543 / 1000000000000), orderedInterval (49072510308 / 1000000000000) (49072510309 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 0) <| besselDerivativeNearFromState (2139693412000913 / 8000000000000) 0 (IntervalRat.scale (467 / 4) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-45667580865 / 1000000000000) (-45667580864 / 1000000000000), orderedInterval (-17081367243 / 1000000000000) (-17081367242 / 1000000000000)))) (orderedInterval (4447717616 / 1000000000000) (4447717664 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 0) <| besselDerivativeNearFromState (1999179139220597 / 8000000000000) 0 (IntervalRat.scale (467 / 4) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-30349186073 / 1000000000000) (-30349176088 / 1000000000000), orderedInterval (40390028318 / 1000000000000) (40390038303 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 0) <| besselDerivativeNearFromState (1426708566362501 / 8000000000000) 0 (IntervalRat.scale (467 / 4) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-3134492636 / 1000000000000) (-3134492634 / 1000000000000), orderedInterval (-59656231666 / 1000000000000) (-59656231664 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 0) <| besselDerivativeNearFromState (1617735454268979 / 8000000000000) 0 (IntervalRat.scale (467 / 4) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (52332278249 / 1000000000000) (52332284527 / 1000000000000), orderedInterval (-20366179668 / 1000000000000) (-20366173389 / 1000000000000)))) (orderedInterval (-13341832 / 1000000000000) (-13341605 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 0) <| besselDerivativeNearFromState (1348699164370051 / 8000000000000) 0 (IntervalRat.scale (467 / 4) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-16624691512 / 1000000000000) (-16624691287 / 1000000000000), orderedInterval (59208701044 / 1000000000000) (59208701269 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 0) <| besselDerivativeNearFromState (1191616613663071 / 8000000000000) 0 (IntervalRat.scale (467 / 4) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-57024735419 / 1000000000000) (-57024715799 / 1000000000000), orderedInterval (32162623026 / 1000000000000) (32162642646 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 0) <| besselDerivativeNearFromState (345376940128029 / 1600000000000) 0 (IntervalRat.scale (467 / 4) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (6742990007 / 1000000000000) (6742990025 / 1000000000000), orderedInterval (-53902138625 / 1000000000000) (-53902138607 / 1000000000000)))) (orderedInterval (3244005714 / 1000000000000) (3244006851 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate240_chunkChecks0_2 :
    compactCertificate240.chunkChecks (0 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 0) <| besselDerivativeNearFromState (955330792586663 / 8000000000000) 0 (IntervalRat.scale (467 / 4) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (53392845964 / 1000000000000) (53392845965 / 1000000000000), orderedInterval (49579003271 / 1000000000000) (49579003272 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 0) <| besselDerivativeNearFromState (809844492874543 / 8000000000000) 0 (IntervalRat.scale (467 / 4) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (79001357332 / 1000000000000) (79001357341 / 1000000000000), orderedInterval (6503282644 / 1000000000000) (6503282652 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 0) <| besselDerivativeNearFromState (506763081355429 / 8000000000000) 0 (IntervalRat.scale (467 / 4) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (96512758233 / 1000000000000) (96512758234 / 1000000000000), orderedInterval (26349115285 / 1000000000000) (26349115286 / 1000000000000)))) (orderedInterval (-9866586892 / 1000000000000) (-9866586861 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 0) <| besselDerivativeNearFromState (272538870570843 / 8000000000000) 0 (IntervalRat.scale (467 / 4) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-39293405426 / 1000000000000) (-39293405425 / 1000000000000), orderedInterval (-130361557582 / 1000000000000) (-130361557581 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 0) <| besselDerivativeNearFromState (739996049961529 / 8000000000000) 0 (IntervalRat.scale (467 / 4) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-68160389708 / 1000000000000) (-68160353103 / 1000000000000), orderedInterval (47660489056 / 1000000000000) (47660525661 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 0) <| besselDerivativeNearFromState (1010401342014233 / 8000000000000) 0 (IntervalRat.scale (467 / 4) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (70199980564 / 1000000000000) (70199980568 / 1000000000000), orderedInterval (10326570538 / 1000000000000) (10326570542 / 1000000000000)))) (orderedInterval (-3108145339 / 1000000000000) (-3108144493 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 0) <| besselDerivativeNearFromState (427236918644571 / 8000000000000) 0 (IntervalRat.scale (467 / 4) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-76830082255 / 1000000000000) (-76830082254 / 1000000000000), orderedInterval (-76855428189 / 1000000000000) (-76855428188 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 0) <| besselDerivativeNearFromState (1736694354805691 / 8000000000000) 0 (IntervalRat.scale (467 / 4) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-48303847782 / 1000000000000) (-48303847781 / 1000000000000), orderedInterval (-24369195512 / 1000000000000) (-24369195511 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 0) <| besselDerivativeNearFromState (1160031343536469 / 8000000000000) 0 (IntervalRat.scale (467 / 4) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (63385687518 / 1000000000000) (63385687520 / 1000000000000), orderedInterval (19084170364 / 1000000000000) (19084170365 / 1000000000000)))) (orderedInterval (-8423974318 / 1000000000000) (-8423974285 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate240_chunkChecks0 :
    compactCertificate240.chunkChecks (0 : Fin 5) 0 9 = true :=
  compactCertificate240.chunkChecks_nine_of_three (0 : Fin 5) compactCertificate240_chunkChecks0_0
    compactCertificate240_chunkChecks0_1 compactCertificate240_chunkChecks0_2

theorem compactCertificate240_chunkChecks1_0 :
    compactCertificate240.chunkChecks (1 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 1) <| besselDerivativeNearFromState (467 / 4) 1 (IntervalRat.scale (467 / 4) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-71060446314 / 1000000000000) (-71060446313 / 1000000000000), orderedInterval (-19775926709 / 1000000000000) (-19775926708 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 1) <| besselDerivativeNearFromState (687980172669767 / 8000000000000) 1 (IntervalRat.scale (467 / 4) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-79653953087 / 1000000000000) (-79653948937 / 1000000000000), orderedInterval (32988898269 / 1000000000000) (32988902419 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 1) <| besselDerivativeNearFromState (222478652396711 / 1600000000000) 1 (IntervalRat.scale (467 / 4) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (67627144198 / 1000000000000) (67627144268 / 1000000000000), orderedInterval (-2461063704 / 1000000000000) (-2461063633 / 1000000000000)))) (orderedInterval (-7784062860 / 1000000000000) (-7784062816 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 1) <| besselDerivativeNearFromState (200750898538069 / 8000000000000) 1 (IntervalRat.scale (467 / 4) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (107569958349 / 1000000000000) (107569958350 / 1000000000000), orderedInterval (115325301804 / 1000000000000) (115325301805 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 1) <| besselDerivativeNearFromState (539245151422993 / 8000000000000) 1 (IntervalRat.scale (467 / 4) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-77661324036 / 1000000000000) (-77661277784 / 1000000000000), orderedInterval (58999099292 / 1000000000000) (58999145544 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 1) <| besselDerivativeNearFromState (1464155484234381 / 8000000000000) 1 (IntervalRat.scale (467 / 4) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (58965101992 / 1000000000000) (58965102074 / 1000000000000), orderedInterval (-1398390919 / 1000000000000) (-1398390837 / 1000000000000)))) (orderedInterval (1130615239 / 1000000000000) (1130616240 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 1) <| besselDerivativeNearFromState (1078490302846453 / 8000000000000) 1 (IntervalRat.scale (467 / 4) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-33383374540 / 1000000000000) (-33383374539 / 1000000000000), orderedInterval (-59941739230 / 1000000000000) (-59941739229 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 1) <| besselDerivativeNearFromState (1848011516205769 / 8000000000000) 1 (IntervalRat.scale (467 / 4) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-33479237640 / 1000000000000) (-33479220389 / 1000000000000), orderedInterval (40508269289 / 1000000000000) (40508286540 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 1) <| besselDerivativeNearFromState (1361236918644571 / 8000000000000) 1 (IntervalRat.scale (467 / 4) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (58826608415 / 1000000000000) (58826608416 / 1000000000000), orderedInterval (16585295141 / 1000000000000) (16585295142 / 1000000000000)))) (orderedInterval (-1887949985 / 1000000000000) (-1887948920 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate240_chunkChecks1_1 :
    compactCertificate240.chunkChecks (1 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 1) <| besselDerivativeNearFromState (2088487490984533 / 8000000000000) 1 (IntervalRat.scale (467 / 4) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-43866834069 / 1000000000000) (-43866834068 / 1000000000000), orderedInterval (-22593839898 / 1000000000000) (-22593839897 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 1) <| besselDerivativeNearFromState (1205788815118957 / 8000000000000) 1 (IntervalRat.scale (467 / 4) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (42447717542 / 1000000000000) (42447717543 / 1000000000000), orderedInterval (49072510308 / 1000000000000) (49072510309 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 1) <| besselDerivativeNearFromState (2139693412000913 / 8000000000000) 1 (IntervalRat.scale (467 / 4) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-45667580865 / 1000000000000) (-45667580864 / 1000000000000), orderedInterval (-17081367243 / 1000000000000) (-17081367242 / 1000000000000)))) (orderedInterval (8108139281 / 1000000000000) (8108139378 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 1) <| besselDerivativeNearFromState (1999179139220597 / 8000000000000) 1 (IntervalRat.scale (467 / 4) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-30349186073 / 1000000000000) (-30349176088 / 1000000000000), orderedInterval (40390028318 / 1000000000000) (40390038303 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 1) <| besselDerivativeNearFromState (1426708566362501 / 8000000000000) 1 (IntervalRat.scale (467 / 4) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-3134492636 / 1000000000000) (-3134492634 / 1000000000000), orderedInterval (-59656231666 / 1000000000000) (-59656231664 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 1) <| besselDerivativeNearFromState (1617735454268979 / 8000000000000) 1 (IntervalRat.scale (467 / 4) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (52332278249 / 1000000000000) (52332284527 / 1000000000000), orderedInterval (-20366179668 / 1000000000000) (-20366173389 / 1000000000000)))) (orderedInterval (-9999400375 / 1000000000000) (-9999399910 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 1) <| besselDerivativeNearFromState (1348699164370051 / 8000000000000) 1 (IntervalRat.scale (467 / 4) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-16624691512 / 1000000000000) (-16624691287 / 1000000000000), orderedInterval (59208701044 / 1000000000000) (59208701269 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 1) <| besselDerivativeNearFromState (1191616613663071 / 8000000000000) 1 (IntervalRat.scale (467 / 4) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-57024735419 / 1000000000000) (-57024715799 / 1000000000000), orderedInterval (32162623026 / 1000000000000) (32162642646 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 1) <| besselDerivativeNearFromState (345376940128029 / 1600000000000) 1 (IntervalRat.scale (467 / 4) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (6742990007 / 1000000000000) (6742990025 / 1000000000000), orderedInterval (-53902138625 / 1000000000000) (-53902138607 / 1000000000000)))) (orderedInterval (-3912627468 / 1000000000000) (-3912626014 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate240_chunkChecks1_2 :
    compactCertificate240.chunkChecks (1 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 1) <| besselDerivativeNearFromState (955330792586663 / 8000000000000) 1 (IntervalRat.scale (467 / 4) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (53392845964 / 1000000000000) (53392845965 / 1000000000000), orderedInterval (49579003271 / 1000000000000) (49579003272 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 1) <| besselDerivativeNearFromState (809844492874543 / 8000000000000) 1 (IntervalRat.scale (467 / 4) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (79001357332 / 1000000000000) (79001357341 / 1000000000000), orderedInterval (6503282644 / 1000000000000) (6503282652 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 1) <| besselDerivativeNearFromState (506763081355429 / 8000000000000) 1 (IntervalRat.scale (467 / 4) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (96512758233 / 1000000000000) (96512758234 / 1000000000000), orderedInterval (26349115285 / 1000000000000) (26349115286 / 1000000000000)))) (orderedInterval (-7962088543 / 1000000000000) (-7962088514 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 1) <| besselDerivativeNearFromState (272538870570843 / 8000000000000) 1 (IntervalRat.scale (467 / 4) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-39293405426 / 1000000000000) (-39293405425 / 1000000000000), orderedInterval (-130361557582 / 1000000000000) (-130361557581 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 1) <| besselDerivativeNearFromState (739996049961529 / 8000000000000) 1 (IntervalRat.scale (467 / 4) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-68160389708 / 1000000000000) (-68160353103 / 1000000000000), orderedInterval (47660489056 / 1000000000000) (47660525661 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 1) <| besselDerivativeNearFromState (1010401342014233 / 8000000000000) 1 (IntervalRat.scale (467 / 4) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (70199980564 / 1000000000000) (70199980568 / 1000000000000), orderedInterval (10326570538 / 1000000000000) (10326570542 / 1000000000000)))) (orderedInterval (-1010431237 / 1000000000000) (-1010430565 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 1) <| besselDerivativeNearFromState (427236918644571 / 8000000000000) 1 (IntervalRat.scale (467 / 4) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-76830082255 / 1000000000000) (-76830082254 / 1000000000000), orderedInterval (-76855428189 / 1000000000000) (-76855428188 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 1) <| besselDerivativeNearFromState (1736694354805691 / 8000000000000) 1 (IntervalRat.scale (467 / 4) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-48303847782 / 1000000000000) (-48303847781 / 1000000000000), orderedInterval (-24369195512 / 1000000000000) (-24369195511 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 1) <| besselDerivativeNearFromState (1160031343536469 / 8000000000000) 1 (IntervalRat.scale (467 / 4) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (63385687518 / 1000000000000) (63385687520 / 1000000000000), orderedInterval (19084170364 / 1000000000000) (19084170365 / 1000000000000)))) (orderedInterval (-970653113 / 1000000000000) (-970653067 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate240_chunkChecks1 :
    compactCertificate240.chunkChecks (1 : Fin 5) 0 9 = true :=
  compactCertificate240.chunkChecks_nine_of_three (1 : Fin 5) compactCertificate240_chunkChecks1_0
    compactCertificate240_chunkChecks1_1 compactCertificate240_chunkChecks1_2

theorem compactCertificate240_chunkChecks2_0 :
    compactCertificate240.chunkChecks (2 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 2) <| besselDerivativeNearFromState (467 / 4) 2 (IntervalRat.scale (467 / 4) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-71060446314 / 1000000000000) (-71060446313 / 1000000000000), orderedInterval (-19775926709 / 1000000000000) (-19775926708 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 2) <| besselDerivativeNearFromState (687980172669767 / 8000000000000) 2 (IntervalRat.scale (467 / 4) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-79653953087 / 1000000000000) (-79653948937 / 1000000000000), orderedInterval (32988898269 / 1000000000000) (32988902419 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 2) <| besselDerivativeNearFromState (222478652396711 / 1600000000000) 2 (IntervalRat.scale (467 / 4) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (67627144198 / 1000000000000) (67627144268 / 1000000000000), orderedInterval (-2461063704 / 1000000000000) (-2461063633 / 1000000000000)))) (orderedInterval (23006108496 / 1000000000000) (23006108534 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 2) <| besselDerivativeNearFromState (200750898538069 / 8000000000000) 2 (IntervalRat.scale (467 / 4) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (107569958349 / 1000000000000) (107569958350 / 1000000000000), orderedInterval (115325301804 / 1000000000000) (115325301805 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 2) <| besselDerivativeNearFromState (539245151422993 / 8000000000000) 2 (IntervalRat.scale (467 / 4) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-77661324036 / 1000000000000) (-77661277784 / 1000000000000), orderedInterval (58999099292 / 1000000000000) (58999145544 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 2) <| besselDerivativeNearFromState (1464155484234381 / 8000000000000) 2 (IntervalRat.scale (467 / 4) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (58965101992 / 1000000000000) (58965102074 / 1000000000000), orderedInterval (-1398390919 / 1000000000000) (-1398390837 / 1000000000000)))) (orderedInterval (11290476798 / 1000000000000) (11290477406 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 2) <| besselDerivativeNearFromState (1078490302846453 / 8000000000000) 2 (IntervalRat.scale (467 / 4) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-33383374540 / 1000000000000) (-33383374539 / 1000000000000), orderedInterval (-59941739230 / 1000000000000) (-59941739229 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 2) <| besselDerivativeNearFromState (1848011516205769 / 8000000000000) 2 (IntervalRat.scale (467 / 4) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-33479237640 / 1000000000000) (-33479220389 / 1000000000000), orderedInterval (40508269289 / 1000000000000) (40508286540 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 2) <| besselDerivativeNearFromState (1361236918644571 / 8000000000000) 2 (IntervalRat.scale (467 / 4) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (58826608415 / 1000000000000) (58826608416 / 1000000000000), orderedInterval (16585295141 / 1000000000000) (16585295142 / 1000000000000)))) (orderedInterval (-7046312399 / 1000000000000) (-7046310286 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate240_chunkChecks2_1 :
    compactCertificate240.chunkChecks (2 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 2) <| besselDerivativeNearFromState (2088487490984533 / 8000000000000) 2 (IntervalRat.scale (467 / 4) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-43866834069 / 1000000000000) (-43866834068 / 1000000000000), orderedInterval (-22593839898 / 1000000000000) (-22593839897 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 2) <| besselDerivativeNearFromState (1205788815118957 / 8000000000000) 2 (IntervalRat.scale (467 / 4) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (42447717542 / 1000000000000) (42447717543 / 1000000000000), orderedInterval (49072510308 / 1000000000000) (49072510309 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 2) <| besselDerivativeNearFromState (2139693412000913 / 8000000000000) 2 (IntervalRat.scale (467 / 4) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-45667580865 / 1000000000000) (-45667580864 / 1000000000000), orderedInterval (-17081367243 / 1000000000000) (-17081367242 / 1000000000000)))) (orderedInterval (-10213402500 / 1000000000000) (-10213402292 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 2) <| besselDerivativeNearFromState (1999179139220597 / 8000000000000) 2 (IntervalRat.scale (467 / 4) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-30349186073 / 1000000000000) (-30349176088 / 1000000000000), orderedInterval (40390028318 / 1000000000000) (40390038303 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 2) <| besselDerivativeNearFromState (1426708566362501 / 8000000000000) 2 (IntervalRat.scale (467 / 4) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-3134492636 / 1000000000000) (-3134492634 / 1000000000000), orderedInterval (-59656231666 / 1000000000000) (-59656231664 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 2) <| besselDerivativeNearFromState (1617735454268979 / 8000000000000) 2 (IntervalRat.scale (467 / 4) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (52332278249 / 1000000000000) (52332284527 / 1000000000000), orderedInterval (-20366179668 / 1000000000000) (-20366173389 / 1000000000000)))) (orderedInterval (-938441325 / 1000000000000) (-938440361 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 2) <| besselDerivativeNearFromState (1348699164370051 / 8000000000000) 2 (IntervalRat.scale (467 / 4) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-16624691512 / 1000000000000) (-16624691287 / 1000000000000), orderedInterval (59208701044 / 1000000000000) (59208701269 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 2) <| besselDerivativeNearFromState (1191616613663071 / 8000000000000) 2 (IntervalRat.scale (467 / 4) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-57024735419 / 1000000000000) (-57024715799 / 1000000000000), orderedInterval (32162623026 / 1000000000000) (32162642646 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 2) <| besselDerivativeNearFromState (345376940128029 / 1600000000000) 2 (IntervalRat.scale (467 / 4) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (6742990007 / 1000000000000) (6742990025 / 1000000000000), orderedInterval (-53902138625 / 1000000000000) (-53902138607 / 1000000000000)))) (orderedInterval (-5468172193 / 1000000000000) (-5468170321 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate240_chunkChecks2_2 :
    compactCertificate240.chunkChecks (2 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 2) <| besselDerivativeNearFromState (955330792586663 / 8000000000000) 2 (IntervalRat.scale (467 / 4) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (53392845964 / 1000000000000) (53392845965 / 1000000000000), orderedInterval (49579003271 / 1000000000000) (49579003272 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 2) <| besselDerivativeNearFromState (809844492874543 / 8000000000000) 2 (IntervalRat.scale (467 / 4) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (79001357332 / 1000000000000) (79001357341 / 1000000000000), orderedInterval (6503282644 / 1000000000000) (6503282652 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 2) <| besselDerivativeNearFromState (506763081355429 / 8000000000000) 2 (IntervalRat.scale (467 / 4) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (96512758233 / 1000000000000) (96512758234 / 1000000000000), orderedInterval (26349115285 / 1000000000000) (26349115286 / 1000000000000)))) (orderedInterval (11436456929 / 1000000000000) (11436456956 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 2) <| besselDerivativeNearFromState (272538870570843 / 8000000000000) 2 (IntervalRat.scale (467 / 4) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-39293405426 / 1000000000000) (-39293405425 / 1000000000000), orderedInterval (-130361557582 / 1000000000000) (-130361557581 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 2) <| besselDerivativeNearFromState (739996049961529 / 8000000000000) 2 (IntervalRat.scale (467 / 4) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-68160389708 / 1000000000000) (-68160353103 / 1000000000000), orderedInterval (47660489056 / 1000000000000) (47660525661 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 2) <| besselDerivativeNearFromState (1010401342014233 / 8000000000000) 2 (IntervalRat.scale (467 / 4) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (70199980564 / 1000000000000) (70199980568 / 1000000000000), orderedInterval (10326570538 / 1000000000000) (10326570542 / 1000000000000)))) (orderedInterval (5272430498 / 1000000000000) (5272431038 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 2) <| besselDerivativeNearFromState (427236918644571 / 8000000000000) 2 (IntervalRat.scale (467 / 4) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-76830082255 / 1000000000000) (-76830082254 / 1000000000000), orderedInterval (-76855428189 / 1000000000000) (-76855428188 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 2) <| besselDerivativeNearFromState (1736694354805691 / 8000000000000) 2 (IntervalRat.scale (467 / 4) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-48303847782 / 1000000000000) (-48303847781 / 1000000000000), orderedInterval (-24369195512 / 1000000000000) (-24369195511 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 2) <| besselDerivativeNearFromState (1160031343536469 / 8000000000000) 2 (IntervalRat.scale (467 / 4) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (63385687518 / 1000000000000) (63385687520 / 1000000000000), orderedInterval (19084170364 / 1000000000000) (19084170365 / 1000000000000)))) (orderedInterval (4856122487 / 1000000000000) (4856122556 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate240_chunkChecks2 :
    compactCertificate240.chunkChecks (2 : Fin 5) 0 9 = true :=
  compactCertificate240.chunkChecks_nine_of_three (2 : Fin 5) compactCertificate240_chunkChecks2_0
    compactCertificate240_chunkChecks2_1 compactCertificate240_chunkChecks2_2

theorem compactCertificate240_chunkChecks3_0 :
    compactCertificate240.chunkChecks (3 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 3) <| besselDerivativeNearFromState (467 / 4) 3 (IntervalRat.scale (467 / 4) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-71060446314 / 1000000000000) (-71060446313 / 1000000000000), orderedInterval (-19775926709 / 1000000000000) (-19775926708 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 3) <| besselDerivativeNearFromState (687980172669767 / 8000000000000) 3 (IntervalRat.scale (467 / 4) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-79653953087 / 1000000000000) (-79653948937 / 1000000000000), orderedInterval (32988898269 / 1000000000000) (32988902419 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 3) <| besselDerivativeNearFromState (222478652396711 / 1600000000000) 3 (IntervalRat.scale (467 / 4) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (67627144198 / 1000000000000) (67627144268 / 1000000000000), orderedInterval (-2461063704 / 1000000000000) (-2461063633 / 1000000000000)))) (orderedInterval (7761988882 / 1000000000000) (7761988918 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 3) <| besselDerivativeNearFromState (200750898538069 / 8000000000000) 3 (IntervalRat.scale (467 / 4) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (107569958349 / 1000000000000) (107569958350 / 1000000000000), orderedInterval (115325301804 / 1000000000000) (115325301805 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 3) <| besselDerivativeNearFromState (539245151422993 / 8000000000000) 3 (IntervalRat.scale (467 / 4) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-77661324036 / 1000000000000) (-77661277784 / 1000000000000), orderedInterval (58999099292 / 1000000000000) (58999145544 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 3) <| besselDerivativeNearFromState (1464155484234381 / 8000000000000) 3 (IntervalRat.scale (467 / 4) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (58965101992 / 1000000000000) (58965102074 / 1000000000000), orderedInterval (-1398390919 / 1000000000000) (-1398390837 / 1000000000000)))) (orderedInterval (-881730429 / 1000000000000) (-881730043 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 3) <| besselDerivativeNearFromState (1078490302846453 / 8000000000000) 3 (IntervalRat.scale (467 / 4) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-33383374540 / 1000000000000) (-33383374539 / 1000000000000), orderedInterval (-59941739230 / 1000000000000) (-59941739229 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 3) <| besselDerivativeNearFromState (1848011516205769 / 8000000000000) 3 (IntervalRat.scale (467 / 4) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-33479237640 / 1000000000000) (-33479220389 / 1000000000000), orderedInterval (40508269289 / 1000000000000) (40508286540 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 3) <| besselDerivativeNearFromState (1361236918644571 / 8000000000000) 3 (IntervalRat.scale (467 / 4) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (58826608415 / 1000000000000) (58826608416 / 1000000000000), orderedInterval (16585295141 / 1000000000000) (16585295142 / 1000000000000)))) (orderedInterval (8497397541 / 1000000000000) (8497401718 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate240_chunkChecks3_1 :
    compactCertificate240.chunkChecks (3 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 3) <| besselDerivativeNearFromState (2088487490984533 / 8000000000000) 3 (IntervalRat.scale (467 / 4) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-43866834069 / 1000000000000) (-43866834068 / 1000000000000), orderedInterval (-22593839898 / 1000000000000) (-22593839897 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 3) <| besselDerivativeNearFromState (1205788815118957 / 8000000000000) 3 (IntervalRat.scale (467 / 4) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (42447717542 / 1000000000000) (42447717543 / 1000000000000), orderedInterval (49072510308 / 1000000000000) (49072510309 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 3) <| besselDerivativeNearFromState (2139693412000913 / 8000000000000) 3 (IntervalRat.scale (467 / 4) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-45667580865 / 1000000000000) (-45667580864 / 1000000000000), orderedInterval (-17081367243 / 1000000000000) (-17081367242 / 1000000000000)))) (orderedInterval (-23425717600 / 1000000000000) (-23425717144 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 3) <| besselDerivativeNearFromState (1999179139220597 / 8000000000000) 3 (IntervalRat.scale (467 / 4) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-30349186073 / 1000000000000) (-30349176088 / 1000000000000), orderedInterval (40390028318 / 1000000000000) (40390038303 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 3) <| besselDerivativeNearFromState (1426708566362501 / 8000000000000) 3 (IntervalRat.scale (467 / 4) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-3134492636 / 1000000000000) (-3134492634 / 1000000000000), orderedInterval (-59656231666 / 1000000000000) (-59656231664 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 3) <| besselDerivativeNearFromState (1617735454268979 / 8000000000000) 3 (IntervalRat.scale (467 / 4) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (52332278249 / 1000000000000) (52332284527 / 1000000000000), orderedInterval (-20366179668 / 1000000000000) (-20366173389 / 1000000000000)))) (orderedInterval (26729064090 / 1000000000000) (26729066096 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 3) <| besselDerivativeNearFromState (1348699164370051 / 8000000000000) 3 (IntervalRat.scale (467 / 4) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-16624691512 / 1000000000000) (-16624691287 / 1000000000000), orderedInterval (59208701044 / 1000000000000) (59208701269 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 3) <| besselDerivativeNearFromState (1191616613663071 / 8000000000000) 3 (IntervalRat.scale (467 / 4) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-57024735419 / 1000000000000) (-57024715799 / 1000000000000), orderedInterval (32162623026 / 1000000000000) (32162642646 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 3) <| besselDerivativeNearFromState (345376940128029 / 1600000000000) 3 (IntervalRat.scale (467 / 4) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (6742990007 / 1000000000000) (6742990025 / 1000000000000), orderedInterval (-53902138625 / 1000000000000) (-53902138607 / 1000000000000)))) (orderedInterval (10533068757 / 1000000000000) (10533071152 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate240_chunkChecks3_2 :
    compactCertificate240.chunkChecks (3 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 3) <| besselDerivativeNearFromState (955330792586663 / 8000000000000) 3 (IntervalRat.scale (467 / 4) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (53392845964 / 1000000000000) (53392845965 / 1000000000000), orderedInterval (49579003271 / 1000000000000) (49579003272 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 3) <| besselDerivativeNearFromState (809844492874543 / 8000000000000) 3 (IntervalRat.scale (467 / 4) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (79001357332 / 1000000000000) (79001357341 / 1000000000000), orderedInterval (6503282644 / 1000000000000) (6503282652 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 3) <| besselDerivativeNearFromState (506763081355429 / 8000000000000) 3 (IntervalRat.scale (467 / 4) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (96512758233 / 1000000000000) (96512758234 / 1000000000000), orderedInterval (26349115285 / 1000000000000) (26349115286 / 1000000000000)))) (orderedInterval (8487332431 / 1000000000000) (8487332458 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 3) <| besselDerivativeNearFromState (272538870570843 / 8000000000000) 3 (IntervalRat.scale (467 / 4) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-39293405426 / 1000000000000) (-39293405425 / 1000000000000), orderedInterval (-130361557582 / 1000000000000) (-130361557581 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 3) <| besselDerivativeNearFromState (739996049961529 / 8000000000000) 3 (IntervalRat.scale (467 / 4) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-68160389708 / 1000000000000) (-68160353103 / 1000000000000), orderedInterval (47660489056 / 1000000000000) (47660525661 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 3) <| besselDerivativeNearFromState (1010401342014233 / 8000000000000) 3 (IntervalRat.scale (467 / 4) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (70199980564 / 1000000000000) (70199980568 / 1000000000000), orderedInterval (10326570538 / 1000000000000) (10326570542 / 1000000000000)))) (orderedInterval (1434660368 / 1000000000000) (1434660800 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 3) <| besselDerivativeNearFromState (427236918644571 / 8000000000000) 3 (IntervalRat.scale (467 / 4) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-76830082255 / 1000000000000) (-76830082254 / 1000000000000), orderedInterval (-76855428189 / 1000000000000) (-76855428188 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 3) <| besselDerivativeNearFromState (1736694354805691 / 8000000000000) 3 (IntervalRat.scale (467 / 4) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-48303847782 / 1000000000000) (-48303847781 / 1000000000000), orderedInterval (-24369195512 / 1000000000000) (-24369195511 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 3) <| besselDerivativeNearFromState (1160031343536469 / 8000000000000) 3 (IntervalRat.scale (467 / 4) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (63385687518 / 1000000000000) (63385687520 / 1000000000000), orderedInterval (19084170364 / 1000000000000) (19084170365 / 1000000000000)))) (orderedInterval (-5889905376 / 1000000000000) (-5889905271 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate240_chunkChecks3 :
    compactCertificate240.chunkChecks (3 : Fin 5) 0 9 = true :=
  compactCertificate240.chunkChecks_nine_of_three (3 : Fin 5) compactCertificate240_chunkChecks3_0
    compactCertificate240_chunkChecks3_1 compactCertificate240_chunkChecks3_2

theorem compactCertificate240_chunkChecks4_0 :
    compactCertificate240.chunkChecks (4 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 4) <| besselDerivativeNearFromState (467 / 4) 4 (IntervalRat.scale (467 / 4) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-71060446314 / 1000000000000) (-71060446313 / 1000000000000), orderedInterval (-19775926709 / 1000000000000) (-19775926708 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 4) <| besselDerivativeNearFromState (687980172669767 / 8000000000000) 4 (IntervalRat.scale (467 / 4) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-79653953087 / 1000000000000) (-79653948937 / 1000000000000), orderedInterval (32988898269 / 1000000000000) (32988902419 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 4) <| besselDerivativeNearFromState (222478652396711 / 1600000000000) 4 (IntervalRat.scale (467 / 4) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (67627144198 / 1000000000000) (67627144268 / 1000000000000), orderedInterval (-2461063704 / 1000000000000) (-2461063633 / 1000000000000)))) (orderedInterval (-20530820563 / 1000000000000) (-20530820527 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 4) <| besselDerivativeNearFromState (200750898538069 / 8000000000000) 4 (IntervalRat.scale (467 / 4) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (107569958349 / 1000000000000) (107569958350 / 1000000000000), orderedInterval (115325301804 / 1000000000000) (115325301805 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 4) <| besselDerivativeNearFromState (539245151422993 / 8000000000000) 4 (IntervalRat.scale (467 / 4) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-77661324036 / 1000000000000) (-77661277784 / 1000000000000), orderedInterval (58999099292 / 1000000000000) (58999145544 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 4) <| besselDerivativeNearFromState (1464155484234381 / 8000000000000) 4 (IntervalRat.scale (467 / 4) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (58965101992 / 1000000000000) (58965102074 / 1000000000000), orderedInterval (-1398390919 / 1000000000000) (-1398390837 / 1000000000000)))) (orderedInterval (-25615729901 / 1000000000000) (-25615729621 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 4) <| besselDerivativeNearFromState (1078490302846453 / 8000000000000) 4 (IntervalRat.scale (467 / 4) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-33383374540 / 1000000000000) (-33383374539 / 1000000000000), orderedInterval (-59941739230 / 1000000000000) (-59941739229 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 4) <| besselDerivativeNearFromState (1848011516205769 / 8000000000000) 4 (IntervalRat.scale (467 / 4) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-33479237640 / 1000000000000) (-33479220389 / 1000000000000), orderedInterval (40508269289 / 1000000000000) (40508286540 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 4) <| besselDerivativeNearFromState (1361236918644571 / 8000000000000) 4 (IntervalRat.scale (467 / 4) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (58826608415 / 1000000000000) (58826608416 / 1000000000000), orderedInterval (16585295141 / 1000000000000) (16585295142 / 1000000000000)))) (orderedInterval (22094633345 / 1000000000000) (22094641639 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate240_chunkChecks4_1 :
    compactCertificate240.chunkChecks (4 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 4) <| besselDerivativeNearFromState (2088487490984533 / 8000000000000) 4 (IntervalRat.scale (467 / 4) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-43866834069 / 1000000000000) (-43866834068 / 1000000000000), orderedInterval (-22593839898 / 1000000000000) (-22593839897 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 4) <| besselDerivativeNearFromState (1205788815118957 / 8000000000000) 4 (IntervalRat.scale (467 / 4) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (42447717542 / 1000000000000) (42447717543 / 1000000000000), orderedInterval (49072510308 / 1000000000000) (49072510309 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 4) <| besselDerivativeNearFromState (2139693412000913 / 8000000000000) 4 (IntervalRat.scale (467 / 4) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-45667580865 / 1000000000000) (-45667580864 / 1000000000000), orderedInterval (-17081367243 / 1000000000000) (-17081367242 / 1000000000000)))) (orderedInterval (25191994559 / 1000000000000) (25191995569 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 4) <| besselDerivativeNearFromState (1999179139220597 / 8000000000000) 4 (IntervalRat.scale (467 / 4) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-30349186073 / 1000000000000) (-30349176088 / 1000000000000), orderedInterval (40390028318 / 1000000000000) (40390038303 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 4) <| besselDerivativeNearFromState (1426708566362501 / 8000000000000) 4 (IntervalRat.scale (467 / 4) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-3134492636 / 1000000000000) (-3134492634 / 1000000000000), orderedInterval (-59656231666 / 1000000000000) (-59656231664 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 4) <| besselDerivativeNearFromState (1617735454268979 / 8000000000000) 4 (IntervalRat.scale (467 / 4) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (52332278249 / 1000000000000) (52332284527 / 1000000000000), orderedInterval (-20366179668 / 1000000000000) (-20366173389 / 1000000000000)))) (orderedInterval (7045324864 / 1000000000000) (7045329078 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 4) <| besselDerivativeNearFromState (1348699164370051 / 8000000000000) 4 (IntervalRat.scale (467 / 4) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-16624691512 / 1000000000000) (-16624691287 / 1000000000000), orderedInterval (59208701044 / 1000000000000) (59208701269 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 4) <| besselDerivativeNearFromState (1191616613663071 / 8000000000000) 4 (IntervalRat.scale (467 / 4) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-57024735419 / 1000000000000) (-57024715799 / 1000000000000), orderedInterval (32162623026 / 1000000000000) (32162642646 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 4) <| besselDerivativeNearFromState (345376940128029 / 1600000000000) 4 (IntervalRat.scale (467 / 4) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (6742990007 / 1000000000000) (6742990025 / 1000000000000), orderedInterval (-53902138625 / 1000000000000) (-53902138607 / 1000000000000)))) (orderedInterval (9648138444 / 1000000000000) (9648141535 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate240_chunkChecks4_2 :
    compactCertificate240.chunkChecks (4 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 4) <| besselDerivativeNearFromState (955330792586663 / 8000000000000) 4 (IntervalRat.scale (467 / 4) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (53392845964 / 1000000000000) (53392845965 / 1000000000000), orderedInterval (49579003271 / 1000000000000) (49579003272 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 4) <| besselDerivativeNearFromState (809844492874543 / 8000000000000) 4 (IntervalRat.scale (467 / 4) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (79001357332 / 1000000000000) (79001357341 / 1000000000000), orderedInterval (6503282644 / 1000000000000) (6503282652 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 4) <| besselDerivativeNearFromState (506763081355429 / 8000000000000) 4 (IntervalRat.scale (467 / 4) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (96512758233 / 1000000000000) (96512758234 / 1000000000000), orderedInterval (26349115285 / 1000000000000) (26349115286 / 1000000000000)))) (orderedInterval (-11743754263 / 1000000000000) (-11743754237 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 4) <| besselDerivativeNearFromState (272538870570843 / 8000000000000) 4 (IntervalRat.scale (467 / 4) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-39293405426 / 1000000000000) (-39293405425 / 1000000000000), orderedInterval (-130361557582 / 1000000000000) (-130361557581 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 4) <| besselDerivativeNearFromState (739996049961529 / 8000000000000) 4 (IntervalRat.scale (467 / 4) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-68160389708 / 1000000000000) (-68160353103 / 1000000000000), orderedInterval (47660489056 / 1000000000000) (47660525661 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 4) <| besselDerivativeNearFromState (1010401342014233 / 8000000000000) 4 (IntervalRat.scale (467 / 4) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (70199980564 / 1000000000000) (70199980568 / 1000000000000), orderedInterval (10326570538 / 1000000000000) (10326570542 / 1000000000000)))) (orderedInterval (-6778039472 / 1000000000000) (-6778039123 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 4) <| besselDerivativeNearFromState (427236918644571 / 8000000000000) 4 (IntervalRat.scale (467 / 4) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-76830082255 / 1000000000000) (-76830082254 / 1000000000000), orderedInterval (-76855428189 / 1000000000000) (-76855428188 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 4) <| besselDerivativeNearFromState (1736694354805691 / 8000000000000) 4 (IntervalRat.scale (467 / 4) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-48303847782 / 1000000000000) (-48303847781 / 1000000000000), orderedInterval (-24369195512 / 1000000000000) (-24369195511 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 4) <| besselDerivativeNearFromState (1160031343536469 / 8000000000000) 4 (IntervalRat.scale (467 / 4) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (63385687518 / 1000000000000) (63385687520 / 1000000000000), orderedInterval (19084170364 / 1000000000000) (19084170365 / 1000000000000)))) (orderedInterval (18784180463 / 1000000000000) (18784180632 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate240_chunkChecks4 :
    compactCertificate240.chunkChecks (4 : Fin 5) 0 9 = true :=
  compactCertificate240.chunkChecks_nine_of_three (4 : Fin 5) compactCertificate240_chunkChecks4_0
    compactCertificate240_chunkChecks4_1 compactCertificate240_chunkChecks4_2

theorem compactCertificate240_chunks :
    ∀ r : Fin 5, ∀ b, compactCertificate240.chunkCheck r b = true :=
  compactCertificate240.chunkChecks_all (by
    intro r
    fin_cases r
    · exact compactCertificate240_chunkChecks0
    · exact compactCertificate240_chunkChecks1
    · exact compactCertificate240_chunkChecks2
    · exact compactCertificate240_chunkChecks3
    · exact compactCertificate240_chunkChecks4)

theorem compactCertificate240_coefficient0 :
    compactCertificate240.coefficientCheck (0 : Fin 5) = true := by
  norm_num [CompactCertificate.coefficientCheck, intervalFinSumHull,
    compactCertificate240, rationalIntervalSubset, orderedInterval, Fin.sum_univ_succ]

theorem compactCertificate240_coefficient1 :
    compactCertificate240.coefficientCheck (1 : Fin 5) = true := by
  norm_num [CompactCertificate.coefficientCheck, intervalFinSumHull,
    compactCertificate240, rationalIntervalSubset, orderedInterval, Fin.sum_univ_succ]

theorem compactCertificate240_coefficient2 :
    compactCertificate240.coefficientCheck (2 : Fin 5) = true := by
  norm_num [CompactCertificate.coefficientCheck, intervalFinSumHull,
    compactCertificate240, rationalIntervalSubset, orderedInterval, Fin.sum_univ_succ]

theorem compactCertificate240_coefficient3 :
    compactCertificate240.coefficientCheck (3 : Fin 5) = true := by
  norm_num [CompactCertificate.coefficientCheck, intervalFinSumHull,
    compactCertificate240, rationalIntervalSubset, orderedInterval, Fin.sum_univ_succ]

theorem compactCertificate240_coefficient4 :
    compactCertificate240.coefficientCheck (4 : Fin 5) = true := by
  norm_num [CompactCertificate.coefficientCheck, intervalFinSumHull,
    compactCertificate240, rationalIntervalSubset, orderedInterval, Fin.sum_univ_succ]

theorem compactCertificate240_coefficients : ∀ r : Fin 5,
    compactCertificate240.coefficientCheck r = true := by
  intro r
  fin_cases r
  · exact compactCertificate240_coefficient0
  · exact compactCertificate240_coefficient1
  · exact compactCertificate240_coefficient2
  · exact compactCertificate240_coefficient3
  · exact compactCertificate240_coefficient4

theorem compactCertificate240_lower : (1 : ℚ) ≤ compactCertificate240.output.lo := by
  norm_num [CompactCertificate.output, CompactCertificate.interval,
    CompactCertificate.coefficientTargetNat, compactCertificate240, dualConstant,
    intervalTaylorSum, intervalPow, intervalSub, intervalMaxAbs, widenInterval,
    rationalErrorInterval, orderedInterval, IntervalRat.add, IntervalRat.mul, IntervalRat.scale,
    IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4]

theorem compactCertificate240_proves {t : ℝ} (ht : t ∈ compactCertificate240.interval) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t :=
  compactCertificate240.proves compactCertificate240_states compactCertificate240_chunks
    compactCertificate240_coefficients compactCertificate240_lower ht

end Erdos232
