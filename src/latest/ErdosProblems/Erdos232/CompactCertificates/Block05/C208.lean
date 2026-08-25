/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, OpenAI Codex
-/
import ErdosProblems.Erdos232.CompactBase

open LeanCert.Core
namespace Erdos232

def compactCertificate208 : CompactCertificate where
  left := 2961 / 32
  right := 1481 / 16
  center := 5923 / 64
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
    | 11 => 68
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
    | 0 => 5923 / 64
    | 1 => 8725709984417623 / 128000000000000
    | 2 => 2821715327935159 / 25600000000000
    | 3 => 2546140411222661 / 128000000000000
    | 4 => 6839291288818817 / 128000000000000
    | 5 => 18570006280771389 / 128000000000000
    | 6 => 13678582577643557 / 128000000000000
    | 7 => 23438484390763961 / 128000000000000
    | 8 => 17264681518483499 / 128000000000000
    | 9 => 26488461261459077 / 128000000000000
    | 10 => 15293120239720733 / 128000000000000
    | 11 => 27137910234007297 / 128000000000000
    | 12 => 25355755977737893 / 128000000000000
    | 13 => 18095063894143669 / 128000000000000
    | 14 => 20517873866456451 / 128000000000000
    | 15 => 17105664133969619 / 128000000000000
    | 16 => 15113373025109999 / 128000000000000
    | 17 => 4380444574685901 / 25600000000000
    | 18 => 12116540223749047 / 128000000000000
    | 19 => 10271325334680767 / 128000000000000
    | 20 => 6427318481516501 / 128000000000000
    | 21 => 3456633255655467 / 128000000000000
    | 22 => 9385431700047401 / 128000000000000
    | 23 => 12815004601178377 / 128000000000000
    | 24 => 5418681518483499 / 128000000000000
    | 25 => 22026639536432779 / 128000000000000
    | _ => 14712774406352261 / 128000000000000
  state := fun i =>
    match i.val with
    | 0 => (orderedInterval (-65827759946 / 1000000000000) (-65827704185 / 1000000000000), orderedInterval (50809281177 / 1000000000000) (50809336938 / 1000000000000))
    | 1 => (orderedInterval (-15573711618 / 1000000000000) (-15573711522 / 1000000000000), orderedInterval (95489584191 / 1000000000000) (95489584287 / 1000000000000))
    | 2 => (orderedInterval (-65989350318 / 1000000000000) (-65989350317 / 1000000000000), orderedInterval (-37398216055 / 1000000000000) (-37398216054 / 1000000000000))
    | 3 => (orderedInterval (173286787460 / 1000000000000) (173286788080 / 1000000000000), orderedInterval (-48705194095 / 1000000000000) (-48705193475 / 1000000000000))
    | 4 => (orderedInterval (-78902427315 / 1000000000000) (-78902427314 / 1000000000000), orderedInterval (-74686983685 / 1000000000000) (-74686983684 / 1000000000000))
    | 5 => (orderedInterval (64626496351 / 1000000000000) (64626496353 / 1000000000000), orderedInterval (14320581862 / 1000000000000) (14320581864 / 1000000000000))
    | 6 => (orderedInterval (57163960182 / 1000000000000) (57163960183 / 1000000000000), orderedInterval (51593597355 / 1000000000000) (51593597356 / 1000000000000))
    | 7 => (orderedInterval (58575519351 / 1000000000000) (58575519645 / 1000000000000), orderedInterval (-6908472381 / 1000000000000) (-6908472086 / 1000000000000))
    | 8 => (orderedInterval (-37437690083 / 1000000000000) (-37437690082 / 1000000000000), orderedInterval (-57466070053 / 1000000000000) (-57466070052 / 1000000000000))
    | 9 => (orderedInterval (20613267144 / 1000000000000) (20613267145 / 1000000000000), orderedInterval (51442261449 / 1000000000000) (51442261450 / 1000000000000))
    | 10 => (orderedInterval (56322288349 / 1000000000000) (56322288350 / 1000000000000), orderedInterval (46198730847 / 1000000000000) (46198730848 / 1000000000000))
    | 11 => (orderedInterval (-40383413391 / 1000000000000) (-40383348075 / 1000000000000), orderedInterval (37134287712 / 1000000000000) (37134353028 / 1000000000000))
    | 12 => (orderedInterval (-46318449417 / 1000000000000) (-46318449416 / 1000000000000), orderedInterval (-32568842434 / 1000000000000) (-32568842433 / 1000000000000))
    | 13 => (orderedInterval (-47219852528 / 1000000000000) (-47219852527 / 1000000000000), orderedInterval (-47515025526 / 1000000000000) (-47515025525 / 1000000000000))
    | 14 => (orderedInterval (-47729665315 / 1000000000000) (-47729665314 / 1000000000000), orderedInterval (-41002126346 / 1000000000000) (-41002126345 / 1000000000000))
    | 15 => (orderedInterval (42644662214 / 1000000000000) (42644683760 / 1000000000000), orderedInterval (-54429283325 / 1000000000000) (-54429261779 / 1000000000000))
    | 16 => (orderedInterval (-36673086836 / 1000000000000) (-36673081186 / 1000000000000), orderedInterval (63770117705 / 1000000000000) (63770123355 / 1000000000000))
    | 17 => (orderedInterval (47467563583 / 1000000000000) (47467660217 / 1000000000000), orderedInterval (-38444457875 / 1000000000000) (-38444361241 / 1000000000000))
    | 18 => (orderedInterval (76337619863 / 1000000000000) (76337619864 / 1000000000000), orderedInterval (29560036933 / 1000000000000) (29560036934 / 1000000000000))
    | 19 => (orderedInterval (-54104589807 / 1000000000000) (-54104565410 / 1000000000000), orderedInterval (71091691063 / 1000000000000) (71091715459 / 1000000000000))
    | 20 => (orderedInterval (75157732180 / 1000000000000) (75157732181 / 1000000000000), orderedInterval (83094769413 / 1000000000000) (83094769414 / 1000000000000))
    | 21 => (orderedInterval (72065362206 / 1000000000000) (72065368364 / 1000000000000), orderedInterval (-136917875975 / 1000000000000) (-136917869817 / 1000000000000))
    | 22 => (orderedInterval (-89550371095 / 1000000000000) (-89550369936 / 1000000000000), orderedInterval (26357100668 / 1000000000000) (26357101827 / 1000000000000))
    | 23 => (orderedInterval (28866007963 / 1000000000000) (28866007964 / 1000000000000), orderedInterval (74189925413 / 1000000000000) (74189925414 / 1000000000000))
    | 24 => (orderedInterval (-93441601631 / 1000000000000) (-93441531430 / 1000000000000), orderedInterval (80518338888 / 1000000000000) (80518409089 / 1000000000000))
    | 25 => (orderedInterval (-4872632467 / 1000000000000) (-4872632466 / 1000000000000), orderedInterval (-60613911612 / 1000000000000) (-60613911610 / 1000000000000))
    | _ => (orderedInterval (36399961803 / 1000000000000) (36399966875 / 1000000000000), orderedInterval (-65070684290 / 1000000000000) (-65070679218 / 1000000000000))
  chunkTarget := fun r b =>
    match r.val with
    | 0 =>
      match b.val with
      | 0 => orderedInterval (-30109266698 / 1000000000000) (-30109244588 / 1000000000000)
      | 1 => orderedInterval (-9355178606 / 1000000000000) (-9355178587 / 1000000000000)
      | 2 => orderedInterval (-2711498494 / 1000000000000) (-2711498479 / 1000000000000)
      | 3 => orderedInterval (-5230450768 / 1000000000000) (-5230441445 / 1000000000000)
      | 4 => orderedInterval (-3387514044 / 1000000000000) (-3387514032 / 1000000000000)
      | 5 => orderedInterval (3806482178 / 1000000000000) (3806485234 / 1000000000000)
      | 6 => orderedInterval (-6696712108 / 1000000000000) (-6696710703 / 1000000000000)
      | 7 => orderedInterval (-1511336811 / 1000000000000) (-1511336659 / 1000000000000)
      | _ => orderedInterval (-6996255063 / 1000000000000) (-6996253662 / 1000000000000)
    | 1 =>
      match b.val with
      | 0 => orderedInterval (18180695503 / 1000000000000) (18180717614 / 1000000000000)
      | 1 => orderedInterval (-3056736403 / 1000000000000) (-3056736387 / 1000000000000)
      | 2 => orderedInterval (-1602525682 / 1000000000000) (-1602525654 / 1000000000000)
      | 3 => orderedInterval (-3926858012 / 1000000000000) (-3926836664 / 1000000000000)
      | 4 => orderedInterval (-5245504264 / 1000000000000) (-5245504245 / 1000000000000)
      | 5 => orderedInterval (-7383461385 / 1000000000000) (-7383456025 / 1000000000000)
      | 6 => orderedInterval (-6855526370 / 1000000000000) (-6855525151 / 1000000000000)
      | 7 => orderedInterval (-5886966093 / 1000000000000) (-5886966028 / 1000000000000)
      | _ => orderedInterval (24560141237 / 1000000000000) (24560142650 / 1000000000000)
    | 2 =>
      match b.val with
      | 0 => orderedInterval (31466904861 / 1000000000000) (31466927212 / 1000000000000)
      | 1 => orderedInterval (12370265671 / 1000000000000) (12370265690 / 1000000000000)
      | 2 => orderedInterval (9012165801 / 1000000000000) (9012165853 / 1000000000000)
      | 3 => orderedInterval (41529476249 / 1000000000000) (41529525373 / 1000000000000)
      | 4 => orderedInterval (5919938354 / 1000000000000) (5919938385 / 1000000000000)
      | 5 => orderedInterval (-8517782770 / 1000000000000) (-8517773189 / 1000000000000)
      | 6 => orderedInterval (9821181501 / 1000000000000) (9821182574 / 1000000000000)
      | 7 => orderedInterval (1490617012 / 1000000000000) (1490617050 / 1000000000000)
      | _ => orderedInterval (9016279488 / 1000000000000) (9016281113 / 1000000000000)
    | 3 =>
      match b.val with
      | 0 => orderedInterval (-17125013169 / 1000000000000) (-17124990823 / 1000000000000)
      | 1 => orderedInterval (4307356119 / 1000000000000) (4307356147 / 1000000000000)
      | 2 => orderedInterval (2551346322 / 1000000000000) (2551346423 / 1000000000000)
      | 3 => orderedInterval (30913587331 / 1000000000000) (30913699847 / 1000000000000)
      | 4 => orderedInterval (9105957534 / 1000000000000) (9105957585 / 1000000000000)
      | 5 => orderedInterval (15783595123 / 1000000000000) (15783612313 / 1000000000000)
      | 6 => orderedInterval (7141705185 / 1000000000000) (7141706117 / 1000000000000)
      | 7 => orderedInterval (7416163543 / 1000000000000) (7416163570 / 1000000000000)
      | _ => orderedInterval (-55252167613 / 1000000000000) (-55252165649 / 1000000000000)
    | _ =>
      match b.val with
      | 0 => orderedInterval (-33552256347 / 1000000000000) (-33552233763 / 1000000000000)
      | 1 => orderedInterval (-28160329627 / 1000000000000) (-28160329585 / 1000000000000)
      | 2 => orderedInterval (-31826000464 / 1000000000000) (-31826000269 / 1000000000000)
      | 3 => orderedInterval (-238759631467 / 1000000000000) (-238759372531 / 1000000000000)
      | 4 => orderedInterval (-4781080782 / 1000000000000) (-4781080693 / 1000000000000)
      | 5 => orderedInterval (21562040047 / 1000000000000) (21562071311 / 1000000000000)
      | 6 => orderedInterval (-11569870206 / 1000000000000) (-11569869386 / 1000000000000)
      | 7 => orderedInterval (-2399084432 / 1000000000000) (-2399084409 / 1000000000000)
      | _ => orderedInterval (-10339480742 / 1000000000000) (-10339478286 / 1000000000000)
  coefficientTarget := fun i =>
    match i.val with
    | 0 => orderedInterval (-62191730414 / 1000000000000) (-62191692921 / 1000000000000)
    | 1 => orderedInterval (8783258531 / 1000000000000) (8783310110 / 1000000000000)
    | 2 => orderedInterval (112109046167 / 1000000000000) (112109130061 / 1000000000000)
    | 3 => orderedInterval (4842530375 / 1000000000000) (4842685530 / 1000000000000)
    | _ => orderedInterval (-339825694020 / 1000000000000) (-339825377611 / 1000000000000)

theorem compactCertificate208_stateChecks0 :
    compactCertificate208.stateChecks 0 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 29 12 (5923 / 64)) (orderedInterval (-65827759946 / 1000000000000) (-65827704185 / 1000000000000), orderedInterval (50809281177 / 1000000000000) (50809336938 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 22 12 (8725709984417623 / 128000000000000)) (orderedInterval (-15573711618 / 1000000000000) (-15573711522 / 1000000000000), orderedInterval (95489584191 / 1000000000000) (95489584287 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 35 12 (2821715327935159 / 25600000000000)) (orderedInterval (-65989350318 / 1000000000000) (-65989350317 / 1000000000000), orderedInterval (-37398216055 / 1000000000000) (-37398216054 / 1000000000000))) = true
  norm_num [besselStateAtRationalPoint, besselIntervalStepZero,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, besselZeroTransition,
    besselInitial, besselGridStateAt, besselGridStateBlock00, besselGridStateBlock01,
    besselGridStateBlock02, besselGridStateBlock03, besselGridStateBlock04,
    besselGridStateBlock05, besselGridStateBlock06, besselGridStateBlock07,
    besselGridStateBlock08, besselGridStateBlock09, besselGridStateBlock10,
    besselGridStateBlock11, besselGridStateBlock12, besselGridStateBlock13,
    besselGridStateBlock14, besselGridState006, besselGridState009, besselGridState013, besselGridState016, besselGridState017, besselGridState022, besselGridState023, besselGridState026, besselGridState029, besselGridState030, besselGridState032, besselGridState034, besselGridState035, besselGridState037, besselGridState038, besselGridState043, besselGridState045, besselGridState046, besselGridState051, besselGridState054, besselGridState055, besselGridState058, besselGridState063, besselGridState066, besselGridState068, besselStateSubset, linearInterval, widenInterval,
    rationalErrorInterval, rationalIntervalSubset, orderedInterval, Finset.sum_range_succ,
    IntervalRat.add, IntervalRat.mul, IntervalRat.scale, IntervalRat.singleton]

theorem compactCertificate208_stateChecks1 :
    compactCertificate208.stateChecks 3 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 6 12 (2546140411222661 / 128000000000000)) (orderedInterval (173286787460 / 1000000000000) (173286788080 / 1000000000000), orderedInterval (-48705194095 / 1000000000000) (-48705193475 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 17 12 (6839291288818817 / 128000000000000)) (orderedInterval (-78902427315 / 1000000000000) (-78902427314 / 1000000000000), orderedInterval (-74686983685 / 1000000000000) (-74686983684 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 46 12 (18570006280771389 / 128000000000000)) (orderedInterval (64626496351 / 1000000000000) (64626496353 / 1000000000000), orderedInterval (14320581862 / 1000000000000) (14320581864 / 1000000000000))) = true
  norm_num [besselStateAtRationalPoint, besselIntervalStepZero,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, besselZeroTransition,
    besselInitial, besselGridStateAt, besselGridStateBlock00, besselGridStateBlock01,
    besselGridStateBlock02, besselGridStateBlock03, besselGridStateBlock04,
    besselGridStateBlock05, besselGridStateBlock06, besselGridStateBlock07,
    besselGridStateBlock08, besselGridStateBlock09, besselGridStateBlock10,
    besselGridStateBlock11, besselGridStateBlock12, besselGridStateBlock13,
    besselGridStateBlock14, besselGridState006, besselGridState009, besselGridState013, besselGridState016, besselGridState017, besselGridState022, besselGridState023, besselGridState026, besselGridState029, besselGridState030, besselGridState032, besselGridState034, besselGridState035, besselGridState037, besselGridState038, besselGridState043, besselGridState045, besselGridState046, besselGridState051, besselGridState054, besselGridState055, besselGridState058, besselGridState063, besselGridState066, besselGridState068, besselStateSubset, linearInterval, widenInterval,
    rationalErrorInterval, rationalIntervalSubset, orderedInterval, Finset.sum_range_succ,
    IntervalRat.add, IntervalRat.mul, IntervalRat.scale, IntervalRat.singleton]

theorem compactCertificate208_stateChecks2 :
    compactCertificate208.stateChecks 6 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 34 12 (13678582577643557 / 128000000000000)) (orderedInterval (57163960182 / 1000000000000) (57163960183 / 1000000000000), orderedInterval (51593597355 / 1000000000000) (51593597356 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 58 12 (23438484390763961 / 128000000000000)) (orderedInterval (58575519351 / 1000000000000) (58575519645 / 1000000000000), orderedInterval (-6908472381 / 1000000000000) (-6908472086 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 43 12 (17264681518483499 / 128000000000000)) (orderedInterval (-37437690083 / 1000000000000) (-37437690082 / 1000000000000), orderedInterval (-57466070053 / 1000000000000) (-57466070052 / 1000000000000))) = true
  norm_num [besselStateAtRationalPoint, besselIntervalStepZero,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, besselZeroTransition,
    besselInitial, besselGridStateAt, besselGridStateBlock00, besselGridStateBlock01,
    besselGridStateBlock02, besselGridStateBlock03, besselGridStateBlock04,
    besselGridStateBlock05, besselGridStateBlock06, besselGridStateBlock07,
    besselGridStateBlock08, besselGridStateBlock09, besselGridStateBlock10,
    besselGridStateBlock11, besselGridStateBlock12, besselGridStateBlock13,
    besselGridStateBlock14, besselGridState006, besselGridState009, besselGridState013, besselGridState016, besselGridState017, besselGridState022, besselGridState023, besselGridState026, besselGridState029, besselGridState030, besselGridState032, besselGridState034, besselGridState035, besselGridState037, besselGridState038, besselGridState043, besselGridState045, besselGridState046, besselGridState051, besselGridState054, besselGridState055, besselGridState058, besselGridState063, besselGridState066, besselGridState068, besselStateSubset, linearInterval, widenInterval,
    rationalErrorInterval, rationalIntervalSubset, orderedInterval, Finset.sum_range_succ,
    IntervalRat.add, IntervalRat.mul, IntervalRat.scale, IntervalRat.singleton]

theorem compactCertificate208_stateChecks3 :
    compactCertificate208.stateChecks 9 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 66 12 (26488461261459077 / 128000000000000)) (orderedInterval (20613267144 / 1000000000000) (20613267145 / 1000000000000), orderedInterval (51442261449 / 1000000000000) (51442261450 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 38 12 (15293120239720733 / 128000000000000)) (orderedInterval (56322288349 / 1000000000000) (56322288350 / 1000000000000), orderedInterval (46198730847 / 1000000000000) (46198730848 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 68 12 (27137910234007297 / 128000000000000)) (orderedInterval (-40383413391 / 1000000000000) (-40383348075 / 1000000000000), orderedInterval (37134287712 / 1000000000000) (37134353028 / 1000000000000))) = true
  norm_num [besselStateAtRationalPoint, besselIntervalStepZero,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, besselZeroTransition,
    besselInitial, besselGridStateAt, besselGridStateBlock00, besselGridStateBlock01,
    besselGridStateBlock02, besselGridStateBlock03, besselGridStateBlock04,
    besselGridStateBlock05, besselGridStateBlock06, besselGridStateBlock07,
    besselGridStateBlock08, besselGridStateBlock09, besselGridStateBlock10,
    besselGridStateBlock11, besselGridStateBlock12, besselGridStateBlock13,
    besselGridStateBlock14, besselGridState006, besselGridState009, besselGridState013, besselGridState016, besselGridState017, besselGridState022, besselGridState023, besselGridState026, besselGridState029, besselGridState030, besselGridState032, besselGridState034, besselGridState035, besselGridState037, besselGridState038, besselGridState043, besselGridState045, besselGridState046, besselGridState051, besselGridState054, besselGridState055, besselGridState058, besselGridState063, besselGridState066, besselGridState068, besselStateSubset, linearInterval, widenInterval,
    rationalErrorInterval, rationalIntervalSubset, orderedInterval, Finset.sum_range_succ,
    IntervalRat.add, IntervalRat.mul, IntervalRat.scale, IntervalRat.singleton]

theorem compactCertificate208_stateChecks4 :
    compactCertificate208.stateChecks 12 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 63 12 (25355755977737893 / 128000000000000)) (orderedInterval (-46318449417 / 1000000000000) (-46318449416 / 1000000000000), orderedInterval (-32568842434 / 1000000000000) (-32568842433 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 45 12 (18095063894143669 / 128000000000000)) (orderedInterval (-47219852528 / 1000000000000) (-47219852527 / 1000000000000), orderedInterval (-47515025526 / 1000000000000) (-47515025525 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 51 12 (20517873866456451 / 128000000000000)) (orderedInterval (-47729665315 / 1000000000000) (-47729665314 / 1000000000000), orderedInterval (-41002126346 / 1000000000000) (-41002126345 / 1000000000000))) = true
  norm_num [besselStateAtRationalPoint, besselIntervalStepZero,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, besselZeroTransition,
    besselInitial, besselGridStateAt, besselGridStateBlock00, besselGridStateBlock01,
    besselGridStateBlock02, besselGridStateBlock03, besselGridStateBlock04,
    besselGridStateBlock05, besselGridStateBlock06, besselGridStateBlock07,
    besselGridStateBlock08, besselGridStateBlock09, besselGridStateBlock10,
    besselGridStateBlock11, besselGridStateBlock12, besselGridStateBlock13,
    besselGridStateBlock14, besselGridState006, besselGridState009, besselGridState013, besselGridState016, besselGridState017, besselGridState022, besselGridState023, besselGridState026, besselGridState029, besselGridState030, besselGridState032, besselGridState034, besselGridState035, besselGridState037, besselGridState038, besselGridState043, besselGridState045, besselGridState046, besselGridState051, besselGridState054, besselGridState055, besselGridState058, besselGridState063, besselGridState066, besselGridState068, besselStateSubset, linearInterval, widenInterval,
    rationalErrorInterval, rationalIntervalSubset, orderedInterval, Finset.sum_range_succ,
    IntervalRat.add, IntervalRat.mul, IntervalRat.scale, IntervalRat.singleton]

theorem compactCertificate208_stateChecks5 :
    compactCertificate208.stateChecks 15 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 43 12 (17105664133969619 / 128000000000000)) (orderedInterval (42644662214 / 1000000000000) (42644683760 / 1000000000000), orderedInterval (-54429283325 / 1000000000000) (-54429261779 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 38 12 (15113373025109999 / 128000000000000)) (orderedInterval (-36673086836 / 1000000000000) (-36673081186 / 1000000000000), orderedInterval (63770117705 / 1000000000000) (63770123355 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 54 12 (4380444574685901 / 25600000000000)) (orderedInterval (47467563583 / 1000000000000) (47467660217 / 1000000000000), orderedInterval (-38444457875 / 1000000000000) (-38444361241 / 1000000000000))) = true
  norm_num [besselStateAtRationalPoint, besselIntervalStepZero,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, besselZeroTransition,
    besselInitial, besselGridStateAt, besselGridStateBlock00, besselGridStateBlock01,
    besselGridStateBlock02, besselGridStateBlock03, besselGridStateBlock04,
    besselGridStateBlock05, besselGridStateBlock06, besselGridStateBlock07,
    besselGridStateBlock08, besselGridStateBlock09, besselGridStateBlock10,
    besselGridStateBlock11, besselGridStateBlock12, besselGridStateBlock13,
    besselGridStateBlock14, besselGridState006, besselGridState009, besselGridState013, besselGridState016, besselGridState017, besselGridState022, besselGridState023, besselGridState026, besselGridState029, besselGridState030, besselGridState032, besselGridState034, besselGridState035, besselGridState037, besselGridState038, besselGridState043, besselGridState045, besselGridState046, besselGridState051, besselGridState054, besselGridState055, besselGridState058, besselGridState063, besselGridState066, besselGridState068, besselStateSubset, linearInterval, widenInterval,
    rationalErrorInterval, rationalIntervalSubset, orderedInterval, Finset.sum_range_succ,
    IntervalRat.add, IntervalRat.mul, IntervalRat.scale, IntervalRat.singleton]

theorem compactCertificate208_stateChecks6 :
    compactCertificate208.stateChecks 18 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 30 12 (12116540223749047 / 128000000000000)) (orderedInterval (76337619863 / 1000000000000) (76337619864 / 1000000000000), orderedInterval (29560036933 / 1000000000000) (29560036934 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 26 12 (10271325334680767 / 128000000000000)) (orderedInterval (-54104589807 / 1000000000000) (-54104565410 / 1000000000000), orderedInterval (71091691063 / 1000000000000) (71091715459 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 16 12 (6427318481516501 / 128000000000000)) (orderedInterval (75157732180 / 1000000000000) (75157732181 / 1000000000000), orderedInterval (83094769413 / 1000000000000) (83094769414 / 1000000000000))) = true
  norm_num [besselStateAtRationalPoint, besselIntervalStepZero,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, besselZeroTransition,
    besselInitial, besselGridStateAt, besselGridStateBlock00, besselGridStateBlock01,
    besselGridStateBlock02, besselGridStateBlock03, besselGridStateBlock04,
    besselGridStateBlock05, besselGridStateBlock06, besselGridStateBlock07,
    besselGridStateBlock08, besselGridStateBlock09, besselGridStateBlock10,
    besselGridStateBlock11, besselGridStateBlock12, besselGridStateBlock13,
    besselGridStateBlock14, besselGridState006, besselGridState009, besselGridState013, besselGridState016, besselGridState017, besselGridState022, besselGridState023, besselGridState026, besselGridState029, besselGridState030, besselGridState032, besselGridState034, besselGridState035, besselGridState037, besselGridState038, besselGridState043, besselGridState045, besselGridState046, besselGridState051, besselGridState054, besselGridState055, besselGridState058, besselGridState063, besselGridState066, besselGridState068, besselStateSubset, linearInterval, widenInterval,
    rationalErrorInterval, rationalIntervalSubset, orderedInterval, Finset.sum_range_succ,
    IntervalRat.add, IntervalRat.mul, IntervalRat.scale, IntervalRat.singleton]

theorem compactCertificate208_stateChecks7 :
    compactCertificate208.stateChecks 21 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 9 12 (3456633255655467 / 128000000000000)) (orderedInterval (72065362206 / 1000000000000) (72065368364 / 1000000000000), orderedInterval (-136917875975 / 1000000000000) (-136917869817 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 23 12 (9385431700047401 / 128000000000000)) (orderedInterval (-89550371095 / 1000000000000) (-89550369936 / 1000000000000), orderedInterval (26357100668 / 1000000000000) (26357101827 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 32 12 (12815004601178377 / 128000000000000)) (orderedInterval (28866007963 / 1000000000000) (28866007964 / 1000000000000), orderedInterval (74189925413 / 1000000000000) (74189925414 / 1000000000000))) = true
  norm_num [besselStateAtRationalPoint, besselIntervalStepZero,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, besselZeroTransition,
    besselInitial, besselGridStateAt, besselGridStateBlock00, besselGridStateBlock01,
    besselGridStateBlock02, besselGridStateBlock03, besselGridStateBlock04,
    besselGridStateBlock05, besselGridStateBlock06, besselGridStateBlock07,
    besselGridStateBlock08, besselGridStateBlock09, besselGridStateBlock10,
    besselGridStateBlock11, besselGridStateBlock12, besselGridStateBlock13,
    besselGridStateBlock14, besselGridState006, besselGridState009, besselGridState013, besselGridState016, besselGridState017, besselGridState022, besselGridState023, besselGridState026, besselGridState029, besselGridState030, besselGridState032, besselGridState034, besselGridState035, besselGridState037, besselGridState038, besselGridState043, besselGridState045, besselGridState046, besselGridState051, besselGridState054, besselGridState055, besselGridState058, besselGridState063, besselGridState066, besselGridState068, besselStateSubset, linearInterval, widenInterval,
    rationalErrorInterval, rationalIntervalSubset, orderedInterval, Finset.sum_range_succ,
    IntervalRat.add, IntervalRat.mul, IntervalRat.scale, IntervalRat.singleton]

theorem compactCertificate208_stateChecks8 :
    compactCertificate208.stateChecks 24 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 13 12 (5418681518483499 / 128000000000000)) (orderedInterval (-93441601631 / 1000000000000) (-93441531430 / 1000000000000), orderedInterval (80518338888 / 1000000000000) (80518409089 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 55 12 (22026639536432779 / 128000000000000)) (orderedInterval (-4872632467 / 1000000000000) (-4872632466 / 1000000000000), orderedInterval (-60613911612 / 1000000000000) (-60613911610 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 37 12 (14712774406352261 / 128000000000000)) (orderedInterval (36399961803 / 1000000000000) (36399966875 / 1000000000000), orderedInterval (-65070684290 / 1000000000000) (-65070679218 / 1000000000000))) = true
  norm_num [besselStateAtRationalPoint, besselIntervalStepZero,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, besselZeroTransition,
    besselInitial, besselGridStateAt, besselGridStateBlock00, besselGridStateBlock01,
    besselGridStateBlock02, besselGridStateBlock03, besselGridStateBlock04,
    besselGridStateBlock05, besselGridStateBlock06, besselGridStateBlock07,
    besselGridStateBlock08, besselGridStateBlock09, besselGridStateBlock10,
    besselGridStateBlock11, besselGridStateBlock12, besselGridStateBlock13,
    besselGridStateBlock14, besselGridState006, besselGridState009, besselGridState013, besselGridState016, besselGridState017, besselGridState022, besselGridState023, besselGridState026, besselGridState029, besselGridState030, besselGridState032, besselGridState034, besselGridState035, besselGridState037, besselGridState038, besselGridState043, besselGridState045, besselGridState046, besselGridState051, besselGridState054, besselGridState055, besselGridState058, besselGridState063, besselGridState066, besselGridState068, besselStateSubset, linearInterval, widenInterval,
    rationalErrorInterval, rationalIntervalSubset, orderedInterval, Finset.sum_range_succ,
    IntervalRat.add, IntervalRat.mul, IntervalRat.scale, IntervalRat.singleton]

theorem compactCertificate208_states : ∀ j,
    BesselStateValid (compactCertificate208.point j) (compactCertificate208.state j) :=
  compactCertificate208.statesValid_of_checks3 compactCertificate208_stateChecks0
    compactCertificate208_stateChecks1 compactCertificate208_stateChecks2
    compactCertificate208_stateChecks3 compactCertificate208_stateChecks4
    compactCertificate208_stateChecks5 compactCertificate208_stateChecks6
    compactCertificate208_stateChecks7 compactCertificate208_stateChecks8

theorem compactCertificate208_chunkChecks0_0 :
    compactCertificate208.chunkChecks (0 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 0) <| besselDerivativeNearFromState (5923 / 64) 0 (IntervalRat.scale (5923 / 64) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-65827759946 / 1000000000000) (-65827704185 / 1000000000000), orderedInterval (50809281177 / 1000000000000) (50809336938 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 0) <| besselDerivativeNearFromState (8725709984417623 / 128000000000000) 0 (IntervalRat.scale (5923 / 64) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-15573711618 / 1000000000000) (-15573711522 / 1000000000000), orderedInterval (95489584191 / 1000000000000) (95489584287 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 0) <| besselDerivativeNearFromState (2821715327935159 / 25600000000000) 0 (IntervalRat.scale (5923 / 64) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-65989350318 / 1000000000000) (-65989350317 / 1000000000000), orderedInterval (-37398216055 / 1000000000000) (-37398216054 / 1000000000000)))) (orderedInterval (-30109266698 / 1000000000000) (-30109244588 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 0) <| besselDerivativeNearFromState (2546140411222661 / 128000000000000) 0 (IntervalRat.scale (5923 / 64) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (173286787460 / 1000000000000) (173286788080 / 1000000000000), orderedInterval (-48705194095 / 1000000000000) (-48705193475 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 0) <| besselDerivativeNearFromState (6839291288818817 / 128000000000000) 0 (IntervalRat.scale (5923 / 64) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-78902427315 / 1000000000000) (-78902427314 / 1000000000000), orderedInterval (-74686983685 / 1000000000000) (-74686983684 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 0) <| besselDerivativeNearFromState (18570006280771389 / 128000000000000) 0 (IntervalRat.scale (5923 / 64) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (64626496351 / 1000000000000) (64626496353 / 1000000000000), orderedInterval (14320581862 / 1000000000000) (14320581864 / 1000000000000)))) (orderedInterval (-9355178606 / 1000000000000) (-9355178587 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 0) <| besselDerivativeNearFromState (13678582577643557 / 128000000000000) 0 (IntervalRat.scale (5923 / 64) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (57163960182 / 1000000000000) (57163960183 / 1000000000000), orderedInterval (51593597355 / 1000000000000) (51593597356 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 0) <| besselDerivativeNearFromState (23438484390763961 / 128000000000000) 0 (IntervalRat.scale (5923 / 64) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (58575519351 / 1000000000000) (58575519645 / 1000000000000), orderedInterval (-6908472381 / 1000000000000) (-6908472086 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 0) <| besselDerivativeNearFromState (17264681518483499 / 128000000000000) 0 (IntervalRat.scale (5923 / 64) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-37437690083 / 1000000000000) (-37437690082 / 1000000000000), orderedInterval (-57466070053 / 1000000000000) (-57466070052 / 1000000000000)))) (orderedInterval (-2711498494 / 1000000000000) (-2711498479 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate208_chunkChecks0_1 :
    compactCertificate208.chunkChecks (0 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 0) <| besselDerivativeNearFromState (26488461261459077 / 128000000000000) 0 (IntervalRat.scale (5923 / 64) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (20613267144 / 1000000000000) (20613267145 / 1000000000000), orderedInterval (51442261449 / 1000000000000) (51442261450 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 0) <| besselDerivativeNearFromState (15293120239720733 / 128000000000000) 0 (IntervalRat.scale (5923 / 64) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (56322288349 / 1000000000000) (56322288350 / 1000000000000), orderedInterval (46198730847 / 1000000000000) (46198730848 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 0) <| besselDerivativeNearFromState (27137910234007297 / 128000000000000) 0 (IntervalRat.scale (5923 / 64) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-40383413391 / 1000000000000) (-40383348075 / 1000000000000), orderedInterval (37134287712 / 1000000000000) (37134353028 / 1000000000000)))) (orderedInterval (-5230450768 / 1000000000000) (-5230441445 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 0) <| besselDerivativeNearFromState (25355755977737893 / 128000000000000) 0 (IntervalRat.scale (5923 / 64) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-46318449417 / 1000000000000) (-46318449416 / 1000000000000), orderedInterval (-32568842434 / 1000000000000) (-32568842433 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 0) <| besselDerivativeNearFromState (18095063894143669 / 128000000000000) 0 (IntervalRat.scale (5923 / 64) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-47219852528 / 1000000000000) (-47219852527 / 1000000000000), orderedInterval (-47515025526 / 1000000000000) (-47515025525 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 0) <| besselDerivativeNearFromState (20517873866456451 / 128000000000000) 0 (IntervalRat.scale (5923 / 64) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-47729665315 / 1000000000000) (-47729665314 / 1000000000000), orderedInterval (-41002126346 / 1000000000000) (-41002126345 / 1000000000000)))) (orderedInterval (-3387514044 / 1000000000000) (-3387514032 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 0) <| besselDerivativeNearFromState (17105664133969619 / 128000000000000) 0 (IntervalRat.scale (5923 / 64) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (42644662214 / 1000000000000) (42644683760 / 1000000000000), orderedInterval (-54429283325 / 1000000000000) (-54429261779 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 0) <| besselDerivativeNearFromState (15113373025109999 / 128000000000000) 0 (IntervalRat.scale (5923 / 64) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-36673086836 / 1000000000000) (-36673081186 / 1000000000000), orderedInterval (63770117705 / 1000000000000) (63770123355 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 0) <| besselDerivativeNearFromState (4380444574685901 / 25600000000000) 0 (IntervalRat.scale (5923 / 64) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (47467563583 / 1000000000000) (47467660217 / 1000000000000), orderedInterval (-38444457875 / 1000000000000) (-38444361241 / 1000000000000)))) (orderedInterval (3806482178 / 1000000000000) (3806485234 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate208_chunkChecks0_2 :
    compactCertificate208.chunkChecks (0 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 0) <| besselDerivativeNearFromState (12116540223749047 / 128000000000000) 0 (IntervalRat.scale (5923 / 64) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (76337619863 / 1000000000000) (76337619864 / 1000000000000), orderedInterval (29560036933 / 1000000000000) (29560036934 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 0) <| besselDerivativeNearFromState (10271325334680767 / 128000000000000) 0 (IntervalRat.scale (5923 / 64) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-54104589807 / 1000000000000) (-54104565410 / 1000000000000), orderedInterval (71091691063 / 1000000000000) (71091715459 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 0) <| besselDerivativeNearFromState (6427318481516501 / 128000000000000) 0 (IntervalRat.scale (5923 / 64) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (75157732180 / 1000000000000) (75157732181 / 1000000000000), orderedInterval (83094769413 / 1000000000000) (83094769414 / 1000000000000)))) (orderedInterval (-6696712108 / 1000000000000) (-6696710703 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 0) <| besselDerivativeNearFromState (3456633255655467 / 128000000000000) 0 (IntervalRat.scale (5923 / 64) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (72065362206 / 1000000000000) (72065368364 / 1000000000000), orderedInterval (-136917875975 / 1000000000000) (-136917869817 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 0) <| besselDerivativeNearFromState (9385431700047401 / 128000000000000) 0 (IntervalRat.scale (5923 / 64) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-89550371095 / 1000000000000) (-89550369936 / 1000000000000), orderedInterval (26357100668 / 1000000000000) (26357101827 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 0) <| besselDerivativeNearFromState (12815004601178377 / 128000000000000) 0 (IntervalRat.scale (5923 / 64) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (28866007963 / 1000000000000) (28866007964 / 1000000000000), orderedInterval (74189925413 / 1000000000000) (74189925414 / 1000000000000)))) (orderedInterval (-1511336811 / 1000000000000) (-1511336659 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 0) <| besselDerivativeNearFromState (5418681518483499 / 128000000000000) 0 (IntervalRat.scale (5923 / 64) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-93441601631 / 1000000000000) (-93441531430 / 1000000000000), orderedInterval (80518338888 / 1000000000000) (80518409089 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 0) <| besselDerivativeNearFromState (22026639536432779 / 128000000000000) 0 (IntervalRat.scale (5923 / 64) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-4872632467 / 1000000000000) (-4872632466 / 1000000000000), orderedInterval (-60613911612 / 1000000000000) (-60613911610 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 0) <| besselDerivativeNearFromState (14712774406352261 / 128000000000000) 0 (IntervalRat.scale (5923 / 64) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (36399961803 / 1000000000000) (36399966875 / 1000000000000), orderedInterval (-65070684290 / 1000000000000) (-65070679218 / 1000000000000)))) (orderedInterval (-6996255063 / 1000000000000) (-6996253662 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate208_chunkChecks0 :
    compactCertificate208.chunkChecks (0 : Fin 5) 0 9 = true :=
  compactCertificate208.chunkChecks_nine_of_three (0 : Fin 5) compactCertificate208_chunkChecks0_0
    compactCertificate208_chunkChecks0_1 compactCertificate208_chunkChecks0_2

theorem compactCertificate208_chunkChecks1_0 :
    compactCertificate208.chunkChecks (1 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 1) <| besselDerivativeNearFromState (5923 / 64) 1 (IntervalRat.scale (5923 / 64) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-65827759946 / 1000000000000) (-65827704185 / 1000000000000), orderedInterval (50809281177 / 1000000000000) (50809336938 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 1) <| besselDerivativeNearFromState (8725709984417623 / 128000000000000) 1 (IntervalRat.scale (5923 / 64) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-15573711618 / 1000000000000) (-15573711522 / 1000000000000), orderedInterval (95489584191 / 1000000000000) (95489584287 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 1) <| besselDerivativeNearFromState (2821715327935159 / 25600000000000) 1 (IntervalRat.scale (5923 / 64) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-65989350318 / 1000000000000) (-65989350317 / 1000000000000), orderedInterval (-37398216055 / 1000000000000) (-37398216054 / 1000000000000)))) (orderedInterval (18180695503 / 1000000000000) (18180717614 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 1) <| besselDerivativeNearFromState (2546140411222661 / 128000000000000) 1 (IntervalRat.scale (5923 / 64) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (173286787460 / 1000000000000) (173286788080 / 1000000000000), orderedInterval (-48705194095 / 1000000000000) (-48705193475 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 1) <| besselDerivativeNearFromState (6839291288818817 / 128000000000000) 1 (IntervalRat.scale (5923 / 64) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-78902427315 / 1000000000000) (-78902427314 / 1000000000000), orderedInterval (-74686983685 / 1000000000000) (-74686983684 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 1) <| besselDerivativeNearFromState (18570006280771389 / 128000000000000) 1 (IntervalRat.scale (5923 / 64) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (64626496351 / 1000000000000) (64626496353 / 1000000000000), orderedInterval (14320581862 / 1000000000000) (14320581864 / 1000000000000)))) (orderedInterval (-3056736403 / 1000000000000) (-3056736387 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 1) <| besselDerivativeNearFromState (13678582577643557 / 128000000000000) 1 (IntervalRat.scale (5923 / 64) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (57163960182 / 1000000000000) (57163960183 / 1000000000000), orderedInterval (51593597355 / 1000000000000) (51593597356 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 1) <| besselDerivativeNearFromState (23438484390763961 / 128000000000000) 1 (IntervalRat.scale (5923 / 64) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (58575519351 / 1000000000000) (58575519645 / 1000000000000), orderedInterval (-6908472381 / 1000000000000) (-6908472086 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 1) <| besselDerivativeNearFromState (17264681518483499 / 128000000000000) 1 (IntervalRat.scale (5923 / 64) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-37437690083 / 1000000000000) (-37437690082 / 1000000000000), orderedInterval (-57466070053 / 1000000000000) (-57466070052 / 1000000000000)))) (orderedInterval (-1602525682 / 1000000000000) (-1602525654 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate208_chunkChecks1_1 :
    compactCertificate208.chunkChecks (1 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 1) <| besselDerivativeNearFromState (26488461261459077 / 128000000000000) 1 (IntervalRat.scale (5923 / 64) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (20613267144 / 1000000000000) (20613267145 / 1000000000000), orderedInterval (51442261449 / 1000000000000) (51442261450 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 1) <| besselDerivativeNearFromState (15293120239720733 / 128000000000000) 1 (IntervalRat.scale (5923 / 64) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (56322288349 / 1000000000000) (56322288350 / 1000000000000), orderedInterval (46198730847 / 1000000000000) (46198730848 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 1) <| besselDerivativeNearFromState (27137910234007297 / 128000000000000) 1 (IntervalRat.scale (5923 / 64) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-40383413391 / 1000000000000) (-40383348075 / 1000000000000), orderedInterval (37134287712 / 1000000000000) (37134353028 / 1000000000000)))) (orderedInterval (-3926858012 / 1000000000000) (-3926836664 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 1) <| besselDerivativeNearFromState (25355755977737893 / 128000000000000) 1 (IntervalRat.scale (5923 / 64) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-46318449417 / 1000000000000) (-46318449416 / 1000000000000), orderedInterval (-32568842434 / 1000000000000) (-32568842433 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 1) <| besselDerivativeNearFromState (18095063894143669 / 128000000000000) 1 (IntervalRat.scale (5923 / 64) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-47219852528 / 1000000000000) (-47219852527 / 1000000000000), orderedInterval (-47515025526 / 1000000000000) (-47515025525 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 1) <| besselDerivativeNearFromState (20517873866456451 / 128000000000000) 1 (IntervalRat.scale (5923 / 64) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-47729665315 / 1000000000000) (-47729665314 / 1000000000000), orderedInterval (-41002126346 / 1000000000000) (-41002126345 / 1000000000000)))) (orderedInterval (-5245504264 / 1000000000000) (-5245504245 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 1) <| besselDerivativeNearFromState (17105664133969619 / 128000000000000) 1 (IntervalRat.scale (5923 / 64) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (42644662214 / 1000000000000) (42644683760 / 1000000000000), orderedInterval (-54429283325 / 1000000000000) (-54429261779 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 1) <| besselDerivativeNearFromState (15113373025109999 / 128000000000000) 1 (IntervalRat.scale (5923 / 64) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-36673086836 / 1000000000000) (-36673081186 / 1000000000000), orderedInterval (63770117705 / 1000000000000) (63770123355 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 1) <| besselDerivativeNearFromState (4380444574685901 / 25600000000000) 1 (IntervalRat.scale (5923 / 64) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (47467563583 / 1000000000000) (47467660217 / 1000000000000), orderedInterval (-38444457875 / 1000000000000) (-38444361241 / 1000000000000)))) (orderedInterval (-7383461385 / 1000000000000) (-7383456025 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate208_chunkChecks1_2 :
    compactCertificate208.chunkChecks (1 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 1) <| besselDerivativeNearFromState (12116540223749047 / 128000000000000) 1 (IntervalRat.scale (5923 / 64) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (76337619863 / 1000000000000) (76337619864 / 1000000000000), orderedInterval (29560036933 / 1000000000000) (29560036934 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 1) <| besselDerivativeNearFromState (10271325334680767 / 128000000000000) 1 (IntervalRat.scale (5923 / 64) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-54104589807 / 1000000000000) (-54104565410 / 1000000000000), orderedInterval (71091691063 / 1000000000000) (71091715459 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 1) <| besselDerivativeNearFromState (6427318481516501 / 128000000000000) 1 (IntervalRat.scale (5923 / 64) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (75157732180 / 1000000000000) (75157732181 / 1000000000000), orderedInterval (83094769413 / 1000000000000) (83094769414 / 1000000000000)))) (orderedInterval (-6855526370 / 1000000000000) (-6855525151 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 1) <| besselDerivativeNearFromState (3456633255655467 / 128000000000000) 1 (IntervalRat.scale (5923 / 64) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (72065362206 / 1000000000000) (72065368364 / 1000000000000), orderedInterval (-136917875975 / 1000000000000) (-136917869817 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 1) <| besselDerivativeNearFromState (9385431700047401 / 128000000000000) 1 (IntervalRat.scale (5923 / 64) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-89550371095 / 1000000000000) (-89550369936 / 1000000000000), orderedInterval (26357100668 / 1000000000000) (26357101827 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 1) <| besselDerivativeNearFromState (12815004601178377 / 128000000000000) 1 (IntervalRat.scale (5923 / 64) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (28866007963 / 1000000000000) (28866007964 / 1000000000000), orderedInterval (74189925413 / 1000000000000) (74189925414 / 1000000000000)))) (orderedInterval (-5886966093 / 1000000000000) (-5886966028 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 1) <| besselDerivativeNearFromState (5418681518483499 / 128000000000000) 1 (IntervalRat.scale (5923 / 64) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-93441601631 / 1000000000000) (-93441531430 / 1000000000000), orderedInterval (80518338888 / 1000000000000) (80518409089 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 1) <| besselDerivativeNearFromState (22026639536432779 / 128000000000000) 1 (IntervalRat.scale (5923 / 64) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-4872632467 / 1000000000000) (-4872632466 / 1000000000000), orderedInterval (-60613911612 / 1000000000000) (-60613911610 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 1) <| besselDerivativeNearFromState (14712774406352261 / 128000000000000) 1 (IntervalRat.scale (5923 / 64) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (36399961803 / 1000000000000) (36399966875 / 1000000000000), orderedInterval (-65070684290 / 1000000000000) (-65070679218 / 1000000000000)))) (orderedInterval (24560141237 / 1000000000000) (24560142650 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate208_chunkChecks1 :
    compactCertificate208.chunkChecks (1 : Fin 5) 0 9 = true :=
  compactCertificate208.chunkChecks_nine_of_three (1 : Fin 5) compactCertificate208_chunkChecks1_0
    compactCertificate208_chunkChecks1_1 compactCertificate208_chunkChecks1_2

theorem compactCertificate208_chunkChecks2_0 :
    compactCertificate208.chunkChecks (2 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 2) <| besselDerivativeNearFromState (5923 / 64) 2 (IntervalRat.scale (5923 / 64) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-65827759946 / 1000000000000) (-65827704185 / 1000000000000), orderedInterval (50809281177 / 1000000000000) (50809336938 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 2) <| besselDerivativeNearFromState (8725709984417623 / 128000000000000) 2 (IntervalRat.scale (5923 / 64) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-15573711618 / 1000000000000) (-15573711522 / 1000000000000), orderedInterval (95489584191 / 1000000000000) (95489584287 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 2) <| besselDerivativeNearFromState (2821715327935159 / 25600000000000) 2 (IntervalRat.scale (5923 / 64) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-65989350318 / 1000000000000) (-65989350317 / 1000000000000), orderedInterval (-37398216055 / 1000000000000) (-37398216054 / 1000000000000)))) (orderedInterval (31466904861 / 1000000000000) (31466927212 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 2) <| besselDerivativeNearFromState (2546140411222661 / 128000000000000) 2 (IntervalRat.scale (5923 / 64) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (173286787460 / 1000000000000) (173286788080 / 1000000000000), orderedInterval (-48705194095 / 1000000000000) (-48705193475 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 2) <| besselDerivativeNearFromState (6839291288818817 / 128000000000000) 2 (IntervalRat.scale (5923 / 64) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-78902427315 / 1000000000000) (-78902427314 / 1000000000000), orderedInterval (-74686983685 / 1000000000000) (-74686983684 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 2) <| besselDerivativeNearFromState (18570006280771389 / 128000000000000) 2 (IntervalRat.scale (5923 / 64) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (64626496351 / 1000000000000) (64626496353 / 1000000000000), orderedInterval (14320581862 / 1000000000000) (14320581864 / 1000000000000)))) (orderedInterval (12370265671 / 1000000000000) (12370265690 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 2) <| besselDerivativeNearFromState (13678582577643557 / 128000000000000) 2 (IntervalRat.scale (5923 / 64) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (57163960182 / 1000000000000) (57163960183 / 1000000000000), orderedInterval (51593597355 / 1000000000000) (51593597356 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 2) <| besselDerivativeNearFromState (23438484390763961 / 128000000000000) 2 (IntervalRat.scale (5923 / 64) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (58575519351 / 1000000000000) (58575519645 / 1000000000000), orderedInterval (-6908472381 / 1000000000000) (-6908472086 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 2) <| besselDerivativeNearFromState (17264681518483499 / 128000000000000) 2 (IntervalRat.scale (5923 / 64) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-37437690083 / 1000000000000) (-37437690082 / 1000000000000), orderedInterval (-57466070053 / 1000000000000) (-57466070052 / 1000000000000)))) (orderedInterval (9012165801 / 1000000000000) (9012165853 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate208_chunkChecks2_1 :
    compactCertificate208.chunkChecks (2 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 2) <| besselDerivativeNearFromState (26488461261459077 / 128000000000000) 2 (IntervalRat.scale (5923 / 64) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (20613267144 / 1000000000000) (20613267145 / 1000000000000), orderedInterval (51442261449 / 1000000000000) (51442261450 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 2) <| besselDerivativeNearFromState (15293120239720733 / 128000000000000) 2 (IntervalRat.scale (5923 / 64) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (56322288349 / 1000000000000) (56322288350 / 1000000000000), orderedInterval (46198730847 / 1000000000000) (46198730848 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 2) <| besselDerivativeNearFromState (27137910234007297 / 128000000000000) 2 (IntervalRat.scale (5923 / 64) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-40383413391 / 1000000000000) (-40383348075 / 1000000000000), orderedInterval (37134287712 / 1000000000000) (37134353028 / 1000000000000)))) (orderedInterval (41529476249 / 1000000000000) (41529525373 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 2) <| besselDerivativeNearFromState (25355755977737893 / 128000000000000) 2 (IntervalRat.scale (5923 / 64) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-46318449417 / 1000000000000) (-46318449416 / 1000000000000), orderedInterval (-32568842434 / 1000000000000) (-32568842433 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 2) <| besselDerivativeNearFromState (18095063894143669 / 128000000000000) 2 (IntervalRat.scale (5923 / 64) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-47219852528 / 1000000000000) (-47219852527 / 1000000000000), orderedInterval (-47515025526 / 1000000000000) (-47515025525 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 2) <| besselDerivativeNearFromState (20517873866456451 / 128000000000000) 2 (IntervalRat.scale (5923 / 64) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-47729665315 / 1000000000000) (-47729665314 / 1000000000000), orderedInterval (-41002126346 / 1000000000000) (-41002126345 / 1000000000000)))) (orderedInterval (5919938354 / 1000000000000) (5919938385 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 2) <| besselDerivativeNearFromState (17105664133969619 / 128000000000000) 2 (IntervalRat.scale (5923 / 64) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (42644662214 / 1000000000000) (42644683760 / 1000000000000), orderedInterval (-54429283325 / 1000000000000) (-54429261779 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 2) <| besselDerivativeNearFromState (15113373025109999 / 128000000000000) 2 (IntervalRat.scale (5923 / 64) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-36673086836 / 1000000000000) (-36673081186 / 1000000000000), orderedInterval (63770117705 / 1000000000000) (63770123355 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 2) <| besselDerivativeNearFromState (4380444574685901 / 25600000000000) 2 (IntervalRat.scale (5923 / 64) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (47467563583 / 1000000000000) (47467660217 / 1000000000000), orderedInterval (-38444457875 / 1000000000000) (-38444361241 / 1000000000000)))) (orderedInterval (-8517782770 / 1000000000000) (-8517773189 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate208_chunkChecks2_2 :
    compactCertificate208.chunkChecks (2 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 2) <| besselDerivativeNearFromState (12116540223749047 / 128000000000000) 2 (IntervalRat.scale (5923 / 64) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (76337619863 / 1000000000000) (76337619864 / 1000000000000), orderedInterval (29560036933 / 1000000000000) (29560036934 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 2) <| besselDerivativeNearFromState (10271325334680767 / 128000000000000) 2 (IntervalRat.scale (5923 / 64) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-54104589807 / 1000000000000) (-54104565410 / 1000000000000), orderedInterval (71091691063 / 1000000000000) (71091715459 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 2) <| besselDerivativeNearFromState (6427318481516501 / 128000000000000) 2 (IntervalRat.scale (5923 / 64) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (75157732180 / 1000000000000) (75157732181 / 1000000000000), orderedInterval (83094769413 / 1000000000000) (83094769414 / 1000000000000)))) (orderedInterval (9821181501 / 1000000000000) (9821182574 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 2) <| besselDerivativeNearFromState (3456633255655467 / 128000000000000) 2 (IntervalRat.scale (5923 / 64) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (72065362206 / 1000000000000) (72065368364 / 1000000000000), orderedInterval (-136917875975 / 1000000000000) (-136917869817 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 2) <| besselDerivativeNearFromState (9385431700047401 / 128000000000000) 2 (IntervalRat.scale (5923 / 64) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-89550371095 / 1000000000000) (-89550369936 / 1000000000000), orderedInterval (26357100668 / 1000000000000) (26357101827 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 2) <| besselDerivativeNearFromState (12815004601178377 / 128000000000000) 2 (IntervalRat.scale (5923 / 64) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (28866007963 / 1000000000000) (28866007964 / 1000000000000), orderedInterval (74189925413 / 1000000000000) (74189925414 / 1000000000000)))) (orderedInterval (1490617012 / 1000000000000) (1490617050 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 2) <| besselDerivativeNearFromState (5418681518483499 / 128000000000000) 2 (IntervalRat.scale (5923 / 64) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-93441601631 / 1000000000000) (-93441531430 / 1000000000000), orderedInterval (80518338888 / 1000000000000) (80518409089 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 2) <| besselDerivativeNearFromState (22026639536432779 / 128000000000000) 2 (IntervalRat.scale (5923 / 64) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-4872632467 / 1000000000000) (-4872632466 / 1000000000000), orderedInterval (-60613911612 / 1000000000000) (-60613911610 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 2) <| besselDerivativeNearFromState (14712774406352261 / 128000000000000) 2 (IntervalRat.scale (5923 / 64) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (36399961803 / 1000000000000) (36399966875 / 1000000000000), orderedInterval (-65070684290 / 1000000000000) (-65070679218 / 1000000000000)))) (orderedInterval (9016279488 / 1000000000000) (9016281113 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate208_chunkChecks2 :
    compactCertificate208.chunkChecks (2 : Fin 5) 0 9 = true :=
  compactCertificate208.chunkChecks_nine_of_three (2 : Fin 5) compactCertificate208_chunkChecks2_0
    compactCertificate208_chunkChecks2_1 compactCertificate208_chunkChecks2_2

theorem compactCertificate208_chunkChecks3_0 :
    compactCertificate208.chunkChecks (3 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 3) <| besselDerivativeNearFromState (5923 / 64) 3 (IntervalRat.scale (5923 / 64) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-65827759946 / 1000000000000) (-65827704185 / 1000000000000), orderedInterval (50809281177 / 1000000000000) (50809336938 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 3) <| besselDerivativeNearFromState (8725709984417623 / 128000000000000) 3 (IntervalRat.scale (5923 / 64) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-15573711618 / 1000000000000) (-15573711522 / 1000000000000), orderedInterval (95489584191 / 1000000000000) (95489584287 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 3) <| besselDerivativeNearFromState (2821715327935159 / 25600000000000) 3 (IntervalRat.scale (5923 / 64) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-65989350318 / 1000000000000) (-65989350317 / 1000000000000), orderedInterval (-37398216055 / 1000000000000) (-37398216054 / 1000000000000)))) (orderedInterval (-17125013169 / 1000000000000) (-17124990823 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 3) <| besselDerivativeNearFromState (2546140411222661 / 128000000000000) 3 (IntervalRat.scale (5923 / 64) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (173286787460 / 1000000000000) (173286788080 / 1000000000000), orderedInterval (-48705194095 / 1000000000000) (-48705193475 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 3) <| besselDerivativeNearFromState (6839291288818817 / 128000000000000) 3 (IntervalRat.scale (5923 / 64) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-78902427315 / 1000000000000) (-78902427314 / 1000000000000), orderedInterval (-74686983685 / 1000000000000) (-74686983684 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 3) <| besselDerivativeNearFromState (18570006280771389 / 128000000000000) 3 (IntervalRat.scale (5923 / 64) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (64626496351 / 1000000000000) (64626496353 / 1000000000000), orderedInterval (14320581862 / 1000000000000) (14320581864 / 1000000000000)))) (orderedInterval (4307356119 / 1000000000000) (4307356147 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 3) <| besselDerivativeNearFromState (13678582577643557 / 128000000000000) 3 (IntervalRat.scale (5923 / 64) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (57163960182 / 1000000000000) (57163960183 / 1000000000000), orderedInterval (51593597355 / 1000000000000) (51593597356 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 3) <| besselDerivativeNearFromState (23438484390763961 / 128000000000000) 3 (IntervalRat.scale (5923 / 64) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (58575519351 / 1000000000000) (58575519645 / 1000000000000), orderedInterval (-6908472381 / 1000000000000) (-6908472086 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 3) <| besselDerivativeNearFromState (17264681518483499 / 128000000000000) 3 (IntervalRat.scale (5923 / 64) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-37437690083 / 1000000000000) (-37437690082 / 1000000000000), orderedInterval (-57466070053 / 1000000000000) (-57466070052 / 1000000000000)))) (orderedInterval (2551346322 / 1000000000000) (2551346423 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate208_chunkChecks3_1 :
    compactCertificate208.chunkChecks (3 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 3) <| besselDerivativeNearFromState (26488461261459077 / 128000000000000) 3 (IntervalRat.scale (5923 / 64) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (20613267144 / 1000000000000) (20613267145 / 1000000000000), orderedInterval (51442261449 / 1000000000000) (51442261450 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 3) <| besselDerivativeNearFromState (15293120239720733 / 128000000000000) 3 (IntervalRat.scale (5923 / 64) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (56322288349 / 1000000000000) (56322288350 / 1000000000000), orderedInterval (46198730847 / 1000000000000) (46198730848 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 3) <| besselDerivativeNearFromState (27137910234007297 / 128000000000000) 3 (IntervalRat.scale (5923 / 64) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-40383413391 / 1000000000000) (-40383348075 / 1000000000000), orderedInterval (37134287712 / 1000000000000) (37134353028 / 1000000000000)))) (orderedInterval (30913587331 / 1000000000000) (30913699847 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 3) <| besselDerivativeNearFromState (25355755977737893 / 128000000000000) 3 (IntervalRat.scale (5923 / 64) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-46318449417 / 1000000000000) (-46318449416 / 1000000000000), orderedInterval (-32568842434 / 1000000000000) (-32568842433 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 3) <| besselDerivativeNearFromState (18095063894143669 / 128000000000000) 3 (IntervalRat.scale (5923 / 64) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-47219852528 / 1000000000000) (-47219852527 / 1000000000000), orderedInterval (-47515025526 / 1000000000000) (-47515025525 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 3) <| besselDerivativeNearFromState (20517873866456451 / 128000000000000) 3 (IntervalRat.scale (5923 / 64) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-47729665315 / 1000000000000) (-47729665314 / 1000000000000), orderedInterval (-41002126346 / 1000000000000) (-41002126345 / 1000000000000)))) (orderedInterval (9105957534 / 1000000000000) (9105957585 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 3) <| besselDerivativeNearFromState (17105664133969619 / 128000000000000) 3 (IntervalRat.scale (5923 / 64) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (42644662214 / 1000000000000) (42644683760 / 1000000000000), orderedInterval (-54429283325 / 1000000000000) (-54429261779 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 3) <| besselDerivativeNearFromState (15113373025109999 / 128000000000000) 3 (IntervalRat.scale (5923 / 64) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-36673086836 / 1000000000000) (-36673081186 / 1000000000000), orderedInterval (63770117705 / 1000000000000) (63770123355 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 3) <| besselDerivativeNearFromState (4380444574685901 / 25600000000000) 3 (IntervalRat.scale (5923 / 64) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (47467563583 / 1000000000000) (47467660217 / 1000000000000), orderedInterval (-38444457875 / 1000000000000) (-38444361241 / 1000000000000)))) (orderedInterval (15783595123 / 1000000000000) (15783612313 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate208_chunkChecks3_2 :
    compactCertificate208.chunkChecks (3 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 3) <| besselDerivativeNearFromState (12116540223749047 / 128000000000000) 3 (IntervalRat.scale (5923 / 64) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (76337619863 / 1000000000000) (76337619864 / 1000000000000), orderedInterval (29560036933 / 1000000000000) (29560036934 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 3) <| besselDerivativeNearFromState (10271325334680767 / 128000000000000) 3 (IntervalRat.scale (5923 / 64) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-54104589807 / 1000000000000) (-54104565410 / 1000000000000), orderedInterval (71091691063 / 1000000000000) (71091715459 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 3) <| besselDerivativeNearFromState (6427318481516501 / 128000000000000) 3 (IntervalRat.scale (5923 / 64) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (75157732180 / 1000000000000) (75157732181 / 1000000000000), orderedInterval (83094769413 / 1000000000000) (83094769414 / 1000000000000)))) (orderedInterval (7141705185 / 1000000000000) (7141706117 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 3) <| besselDerivativeNearFromState (3456633255655467 / 128000000000000) 3 (IntervalRat.scale (5923 / 64) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (72065362206 / 1000000000000) (72065368364 / 1000000000000), orderedInterval (-136917875975 / 1000000000000) (-136917869817 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 3) <| besselDerivativeNearFromState (9385431700047401 / 128000000000000) 3 (IntervalRat.scale (5923 / 64) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-89550371095 / 1000000000000) (-89550369936 / 1000000000000), orderedInterval (26357100668 / 1000000000000) (26357101827 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 3) <| besselDerivativeNearFromState (12815004601178377 / 128000000000000) 3 (IntervalRat.scale (5923 / 64) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (28866007963 / 1000000000000) (28866007964 / 1000000000000), orderedInterval (74189925413 / 1000000000000) (74189925414 / 1000000000000)))) (orderedInterval (7416163543 / 1000000000000) (7416163570 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 3) <| besselDerivativeNearFromState (5418681518483499 / 128000000000000) 3 (IntervalRat.scale (5923 / 64) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-93441601631 / 1000000000000) (-93441531430 / 1000000000000), orderedInterval (80518338888 / 1000000000000) (80518409089 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 3) <| besselDerivativeNearFromState (22026639536432779 / 128000000000000) 3 (IntervalRat.scale (5923 / 64) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-4872632467 / 1000000000000) (-4872632466 / 1000000000000), orderedInterval (-60613911612 / 1000000000000) (-60613911610 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 3) <| besselDerivativeNearFromState (14712774406352261 / 128000000000000) 3 (IntervalRat.scale (5923 / 64) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (36399961803 / 1000000000000) (36399966875 / 1000000000000), orderedInterval (-65070684290 / 1000000000000) (-65070679218 / 1000000000000)))) (orderedInterval (-55252167613 / 1000000000000) (-55252165649 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate208_chunkChecks3 :
    compactCertificate208.chunkChecks (3 : Fin 5) 0 9 = true :=
  compactCertificate208.chunkChecks_nine_of_three (3 : Fin 5) compactCertificate208_chunkChecks3_0
    compactCertificate208_chunkChecks3_1 compactCertificate208_chunkChecks3_2

theorem compactCertificate208_chunkChecks4_0 :
    compactCertificate208.chunkChecks (4 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 4) <| besselDerivativeNearFromState (5923 / 64) 4 (IntervalRat.scale (5923 / 64) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-65827759946 / 1000000000000) (-65827704185 / 1000000000000), orderedInterval (50809281177 / 1000000000000) (50809336938 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 4) <| besselDerivativeNearFromState (8725709984417623 / 128000000000000) 4 (IntervalRat.scale (5923 / 64) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-15573711618 / 1000000000000) (-15573711522 / 1000000000000), orderedInterval (95489584191 / 1000000000000) (95489584287 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 4) <| besselDerivativeNearFromState (2821715327935159 / 25600000000000) 4 (IntervalRat.scale (5923 / 64) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-65989350318 / 1000000000000) (-65989350317 / 1000000000000), orderedInterval (-37398216055 / 1000000000000) (-37398216054 / 1000000000000)))) (orderedInterval (-33552256347 / 1000000000000) (-33552233763 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 4) <| besselDerivativeNearFromState (2546140411222661 / 128000000000000) 4 (IntervalRat.scale (5923 / 64) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (173286787460 / 1000000000000) (173286788080 / 1000000000000), orderedInterval (-48705194095 / 1000000000000) (-48705193475 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 4) <| besselDerivativeNearFromState (6839291288818817 / 128000000000000) 4 (IntervalRat.scale (5923 / 64) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-78902427315 / 1000000000000) (-78902427314 / 1000000000000), orderedInterval (-74686983685 / 1000000000000) (-74686983684 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 4) <| besselDerivativeNearFromState (18570006280771389 / 128000000000000) 4 (IntervalRat.scale (5923 / 64) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (64626496351 / 1000000000000) (64626496353 / 1000000000000), orderedInterval (14320581862 / 1000000000000) (14320581864 / 1000000000000)))) (orderedInterval (-28160329627 / 1000000000000) (-28160329585 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 4) <| besselDerivativeNearFromState (13678582577643557 / 128000000000000) 4 (IntervalRat.scale (5923 / 64) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (57163960182 / 1000000000000) (57163960183 / 1000000000000), orderedInterval (51593597355 / 1000000000000) (51593597356 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 4) <| besselDerivativeNearFromState (23438484390763961 / 128000000000000) 4 (IntervalRat.scale (5923 / 64) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (58575519351 / 1000000000000) (58575519645 / 1000000000000), orderedInterval (-6908472381 / 1000000000000) (-6908472086 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 4) <| besselDerivativeNearFromState (17264681518483499 / 128000000000000) 4 (IntervalRat.scale (5923 / 64) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-37437690083 / 1000000000000) (-37437690082 / 1000000000000), orderedInterval (-57466070053 / 1000000000000) (-57466070052 / 1000000000000)))) (orderedInterval (-31826000464 / 1000000000000) (-31826000269 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate208_chunkChecks4_1 :
    compactCertificate208.chunkChecks (4 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 4) <| besselDerivativeNearFromState (26488461261459077 / 128000000000000) 4 (IntervalRat.scale (5923 / 64) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (20613267144 / 1000000000000) (20613267145 / 1000000000000), orderedInterval (51442261449 / 1000000000000) (51442261450 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 4) <| besselDerivativeNearFromState (15293120239720733 / 128000000000000) 4 (IntervalRat.scale (5923 / 64) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (56322288349 / 1000000000000) (56322288350 / 1000000000000), orderedInterval (46198730847 / 1000000000000) (46198730848 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 4) <| besselDerivativeNearFromState (27137910234007297 / 128000000000000) 4 (IntervalRat.scale (5923 / 64) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-40383413391 / 1000000000000) (-40383348075 / 1000000000000), orderedInterval (37134287712 / 1000000000000) (37134353028 / 1000000000000)))) (orderedInterval (-238759631467 / 1000000000000) (-238759372531 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 4) <| besselDerivativeNearFromState (25355755977737893 / 128000000000000) 4 (IntervalRat.scale (5923 / 64) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-46318449417 / 1000000000000) (-46318449416 / 1000000000000), orderedInterval (-32568842434 / 1000000000000) (-32568842433 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 4) <| besselDerivativeNearFromState (18095063894143669 / 128000000000000) 4 (IntervalRat.scale (5923 / 64) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-47219852528 / 1000000000000) (-47219852527 / 1000000000000), orderedInterval (-47515025526 / 1000000000000) (-47515025525 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 4) <| besselDerivativeNearFromState (20517873866456451 / 128000000000000) 4 (IntervalRat.scale (5923 / 64) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-47729665315 / 1000000000000) (-47729665314 / 1000000000000), orderedInterval (-41002126346 / 1000000000000) (-41002126345 / 1000000000000)))) (orderedInterval (-4781080782 / 1000000000000) (-4781080693 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 4) <| besselDerivativeNearFromState (17105664133969619 / 128000000000000) 4 (IntervalRat.scale (5923 / 64) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (42644662214 / 1000000000000) (42644683760 / 1000000000000), orderedInterval (-54429283325 / 1000000000000) (-54429261779 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 4) <| besselDerivativeNearFromState (15113373025109999 / 128000000000000) 4 (IntervalRat.scale (5923 / 64) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-36673086836 / 1000000000000) (-36673081186 / 1000000000000), orderedInterval (63770117705 / 1000000000000) (63770123355 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 4) <| besselDerivativeNearFromState (4380444574685901 / 25600000000000) 4 (IntervalRat.scale (5923 / 64) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (47467563583 / 1000000000000) (47467660217 / 1000000000000), orderedInterval (-38444457875 / 1000000000000) (-38444361241 / 1000000000000)))) (orderedInterval (21562040047 / 1000000000000) (21562071311 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate208_chunkChecks4_2 :
    compactCertificate208.chunkChecks (4 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 4) <| besselDerivativeNearFromState (12116540223749047 / 128000000000000) 4 (IntervalRat.scale (5923 / 64) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (76337619863 / 1000000000000) (76337619864 / 1000000000000), orderedInterval (29560036933 / 1000000000000) (29560036934 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 4) <| besselDerivativeNearFromState (10271325334680767 / 128000000000000) 4 (IntervalRat.scale (5923 / 64) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-54104589807 / 1000000000000) (-54104565410 / 1000000000000), orderedInterval (71091691063 / 1000000000000) (71091715459 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 4) <| besselDerivativeNearFromState (6427318481516501 / 128000000000000) 4 (IntervalRat.scale (5923 / 64) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (75157732180 / 1000000000000) (75157732181 / 1000000000000), orderedInterval (83094769413 / 1000000000000) (83094769414 / 1000000000000)))) (orderedInterval (-11569870206 / 1000000000000) (-11569869386 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 4) <| besselDerivativeNearFromState (3456633255655467 / 128000000000000) 4 (IntervalRat.scale (5923 / 64) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (72065362206 / 1000000000000) (72065368364 / 1000000000000), orderedInterval (-136917875975 / 1000000000000) (-136917869817 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 4) <| besselDerivativeNearFromState (9385431700047401 / 128000000000000) 4 (IntervalRat.scale (5923 / 64) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-89550371095 / 1000000000000) (-89550369936 / 1000000000000), orderedInterval (26357100668 / 1000000000000) (26357101827 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 4) <| besselDerivativeNearFromState (12815004601178377 / 128000000000000) 4 (IntervalRat.scale (5923 / 64) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (28866007963 / 1000000000000) (28866007964 / 1000000000000), orderedInterval (74189925413 / 1000000000000) (74189925414 / 1000000000000)))) (orderedInterval (-2399084432 / 1000000000000) (-2399084409 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 4) <| besselDerivativeNearFromState (5418681518483499 / 128000000000000) 4 (IntervalRat.scale (5923 / 64) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-93441601631 / 1000000000000) (-93441531430 / 1000000000000), orderedInterval (80518338888 / 1000000000000) (80518409089 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 4) <| besselDerivativeNearFromState (22026639536432779 / 128000000000000) 4 (IntervalRat.scale (5923 / 64) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-4872632467 / 1000000000000) (-4872632466 / 1000000000000), orderedInterval (-60613911612 / 1000000000000) (-60613911610 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 4) <| besselDerivativeNearFromState (14712774406352261 / 128000000000000) 4 (IntervalRat.scale (5923 / 64) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (36399961803 / 1000000000000) (36399966875 / 1000000000000), orderedInterval (-65070684290 / 1000000000000) (-65070679218 / 1000000000000)))) (orderedInterval (-10339480742 / 1000000000000) (-10339478286 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate208_chunkChecks4 :
    compactCertificate208.chunkChecks (4 : Fin 5) 0 9 = true :=
  compactCertificate208.chunkChecks_nine_of_three (4 : Fin 5) compactCertificate208_chunkChecks4_0
    compactCertificate208_chunkChecks4_1 compactCertificate208_chunkChecks4_2

theorem compactCertificate208_chunks :
    ∀ r : Fin 5, ∀ b, compactCertificate208.chunkCheck r b = true :=
  compactCertificate208.chunkChecks_all (by
    intro r
    fin_cases r
    · exact compactCertificate208_chunkChecks0
    · exact compactCertificate208_chunkChecks1
    · exact compactCertificate208_chunkChecks2
    · exact compactCertificate208_chunkChecks3
    · exact compactCertificate208_chunkChecks4)

theorem compactCertificate208_coefficient0 :
    compactCertificate208.coefficientCheck (0 : Fin 5) = true := by
  norm_num [CompactCertificate.coefficientCheck, intervalFinSumHull,
    compactCertificate208, rationalIntervalSubset, orderedInterval, Fin.sum_univ_succ]

theorem compactCertificate208_coefficient1 :
    compactCertificate208.coefficientCheck (1 : Fin 5) = true := by
  norm_num [CompactCertificate.coefficientCheck, intervalFinSumHull,
    compactCertificate208, rationalIntervalSubset, orderedInterval, Fin.sum_univ_succ]

theorem compactCertificate208_coefficient2 :
    compactCertificate208.coefficientCheck (2 : Fin 5) = true := by
  norm_num [CompactCertificate.coefficientCheck, intervalFinSumHull,
    compactCertificate208, rationalIntervalSubset, orderedInterval, Fin.sum_univ_succ]

theorem compactCertificate208_coefficient3 :
    compactCertificate208.coefficientCheck (3 : Fin 5) = true := by
  norm_num [CompactCertificate.coefficientCheck, intervalFinSumHull,
    compactCertificate208, rationalIntervalSubset, orderedInterval, Fin.sum_univ_succ]

theorem compactCertificate208_coefficient4 :
    compactCertificate208.coefficientCheck (4 : Fin 5) = true := by
  norm_num [CompactCertificate.coefficientCheck, intervalFinSumHull,
    compactCertificate208, rationalIntervalSubset, orderedInterval, Fin.sum_univ_succ]

theorem compactCertificate208_coefficients : ∀ r : Fin 5,
    compactCertificate208.coefficientCheck r = true := by
  intro r
  fin_cases r
  · exact compactCertificate208_coefficient0
  · exact compactCertificate208_coefficient1
  · exact compactCertificate208_coefficient2
  · exact compactCertificate208_coefficient3
  · exact compactCertificate208_coefficient4

theorem compactCertificate208_lower : (1 : ℚ) ≤ compactCertificate208.output.lo := by
  norm_num [CompactCertificate.output, CompactCertificate.interval,
    CompactCertificate.coefficientTargetNat, compactCertificate208, dualConstant,
    intervalTaylorSum, intervalPow, intervalSub, intervalMaxAbs, widenInterval,
    rationalErrorInterval, orderedInterval, IntervalRat.add, IntervalRat.mul, IntervalRat.scale,
    IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4]

theorem compactCertificate208_proves {t : ℝ} (ht : t ∈ compactCertificate208.interval) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t :=
  compactCertificate208.proves compactCertificate208_states compactCertificate208_chunks
    compactCertificate208_coefficients compactCertificate208_lower ht

end Erdos232
