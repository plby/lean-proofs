/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, OpenAI Codex
-/
import ErdosProblems.Erdos232.CompactBase

open LeanCert.Core
namespace Erdos232

def compactCertificate268 : CompactCertificate where
  left := 142
  right := 143
  center := 285 / 2
  grid := fun i =>
    match i.val with
    | 0 => 45
    | 1 => 33
    | 2 => 54
    | 3 => 10
    | 4 => 26
    | 5 => 71
    | 6 => 52
    | 7 => 90
    | 8 => 66
    | 9 => 101
    | 10 => 59
    | 11 => 104
    | 12 => 97
    | 13 => 69
    | 14 => 79
    | 15 => 66
    | 16 => 58
    | 17 => 84
    | 18 => 46
    | 19 => 39
    | 20 => 25
    | 21 => 13
    | 22 => 36
    | 23 => 49
    | 24 => 21
    | 25 => 84
    | _ => 56
  point := fun i =>
    match i.val with
    | 0 => 285 / 2
    | 1 => 83971884030357 / 800000000000
    | 2 => 27154781984181 / 160000000000
    | 3 => 24502786331199 / 800000000000
    | 4 => 65817930687603 / 800000000000
    | 5 => 178708485227751 / 800000000000
    | 6 => 131635861375263 / 800000000000
    | 7 => 225560292127899 / 800000000000
    | 8 => 166146690284241 / 800000000000
    | 9 => 254911749434943 / 800000000000
    | 10 => 147173367155847 / 800000000000
    | 11 => 261161722663923 / 800000000000
    | 12 => 244011158320287 / 800000000000
    | 13 => 174137876408271 / 800000000000
    | 14 => 197453792062809 / 800000000000
    | 15 => 164616386229321 / 800000000000
    | 16 => 145443569547741 / 800000000000
    | 17 => 42155215390359 / 160000000000
    | 18 => 116603544277173 / 800000000000
    | 19 => 98846115832653 / 800000000000
    | 20 => 61853309715759 / 800000000000
    | 21 => 33264915679953 / 800000000000
    | 22 => 90320717018859 / 800000000000
    | 23 => 123325217333643 / 800000000000
    | 24 => 52146690284241 / 800000000000
    | 25 => 211973400907761 / 800000000000
    | _ => 141588408097599 / 800000000000
  state := fun i =>
    match i.val with
    | 0 => (orderedInterval (-62967031767 / 1000000000000) (-62967028330 / 1000000000000), orderedInterval (22640543950 / 1000000000000) (22640547387 / 1000000000000))
    | 1 => (orderedInterval (-68130267298 / 1000000000000) (-68130252178 / 1000000000000), orderedInterval (38051259789 / 1000000000000) (38051274910 / 1000000000000))
    | 2 => (orderedInterval (46256265606 / 1000000000000) (46256265607 / 1000000000000), orderedInterval (40006143896 / 1000000000000) (40006143897 / 1000000000000))
    | 3 => (orderedInterval (-882890944 / 1000000000000) (-882890932 / 1000000000000), orderedInterval (144192097478 / 1000000000000) (144192097491 / 1000000000000))
    | 4 => (orderedInterval (86282066758 / 1000000000000) (86282066759 / 1000000000000), orderedInterval (16599387061 / 1000000000000) (16599387063 / 1000000000000))
    | 5 => (orderedInterval (-47989639379 / 1000000000000) (-47989639378 / 1000000000000), orderedInterval (-23277610663 / 1000000000000) (-23277610662 / 1000000000000))
    | 6 => (orderedInterval (57390861947 / 1000000000000) (57390868758 / 1000000000000), orderedInterval (-24158779202 / 1000000000000) (-24158772391 / 1000000000000))
    | 7 => (orderedInterval (-381030851 / 1000000000000) (-381030849 / 1000000000000), orderedInterval (47516701465 / 1000000000000) (47516701467 / 1000000000000))
    | 8 => (orderedInterval (49907632548 / 1000000000000) (49907632550 / 1000000000000), orderedInterval (23849849370 / 1000000000000) (23849849371 / 1000000000000))
    | 9 => (orderedInterval (-38035165794 / 1000000000000) (-38035103454 / 1000000000000), orderedInterval (23538520591 / 1000000000000) (23538582930 / 1000000000000))
    | 10 => (orderedInterval (33338838155 / 1000000000000) (33338847251 / 1000000000000), orderedInterval (-48557534452 / 1000000000000) (-48557525356 / 1000000000000))
    | 11 => (orderedInterval (21616998005 / 1000000000000) (21616998006 / 1000000000000), orderedInterval (38474334739 / 1000000000000) (38474334740 / 1000000000000))
    | 12 => (orderedInterval (-39953105367 / 1000000000000) (-39953105366 / 1000000000000), orderedInterval (-22091455077 / 1000000000000) (-22091455076 / 1000000000000))
    | 13 => (orderedInterval (-53713692752 / 1000000000000) (-53713692374 / 1000000000000), orderedInterval (6408418458 / 1000000000000) (6408418836 / 1000000000000))
    | 14 => (orderedInterval (27988919291 / 1000000000000) (27988924709 / 1000000000000), orderedInterval (-42435220072 / 1000000000000) (-42435214654 / 1000000000000))
    | 15 => (orderedInterval (-39505209440 / 1000000000000) (-39505161574 / 1000000000000), orderedInterval (39251739371 / 1000000000000) (39251787237 / 1000000000000))
    | 16 => (orderedInterval (21773115484 / 1000000000000) (21773115485 / 1000000000000), orderedInterval (54963879104 / 1000000000000) (54963879105 / 1000000000000))
    | 17 => (orderedInterval (17373186680 / 1000000000000) (17373186681 / 1000000000000), orderedInterval (45950333475 / 1000000000000) (45950333476 / 1000000000000))
    | 18 => (orderedInterval (59367532569 / 1000000000000) (59367543799 / 1000000000000), orderedInterval (-29242176509 / 1000000000000) (-29242165279 / 1000000000000))
    | 19 => (orderedInterval (-69564111361 / 1000000000000) (-69564110282 / 1000000000000), orderedInterval (17979196021 / 1000000000000) (17979197100 / 1000000000000))
    | 20 => (orderedInterval (38600308676 / 1000000000000) (38600311543 / 1000000000000), orderedInterval (-82371816258 / 1000000000000) (-82371813391 / 1000000000000))
    | 21 => (orderedInterval (-123588033689 / 1000000000000) (-123588033679 / 1000000000000), orderedInterval (-4446779207 / 1000000000000) (-4446779197 / 1000000000000))
    | 22 => (orderedInterval (41643698441 / 1000000000000) (41643698442 / 1000000000000), orderedInterval (62302154474 / 1000000000000) (62302154475 / 1000000000000))
    | 23 => (orderedInterval (-54181376001 / 1000000000000) (-54181376000 / 1000000000000), orderedInterval (-34379536278 / 1000000000000) (-34379536277 / 1000000000000))
    | 24 => (orderedInterval (652449349 / 1000000000000) (652449359 / 1000000000000), orderedInterval (-98830409056 / 1000000000000) (-98830409047 / 1000000000000))
    | 25 => (orderedInterval (47010414933 / 1000000000000) (47010418631 / 1000000000000), orderedInterval (-13968817152 / 1000000000000) (-13968813454 / 1000000000000))
    | _ => (orderedInterval (57798695187 / 1000000000000) (57798697067 / 1000000000000), orderedInterval (-16173119240 / 1000000000000) (-16173117361 / 1000000000000))
  chunkTarget := fun r b =>
    match r.val with
    | 0 =>
      match b.val with
      | 0 => orderedInterval (-22878398631 / 1000000000000) (-22878397118 / 1000000000000)
      | 1 => orderedInterval (6571453873 / 1000000000000) (6571453891 / 1000000000000)
      | 2 => orderedInterval (1217921522 / 1000000000000) (1217921531 / 1000000000000)
      | 3 => orderedInterval (12301495815 / 1000000000000) (12301507623 / 1000000000000)
      | 4 => orderedInterval (-4499683972 / 1000000000000) (-4499683892 / 1000000000000)
      | 5 => orderedInterval (-1257373973 / 1000000000000) (-1257373406 / 1000000000000)
      | 6 => orderedInterval (-4298452481 / 1000000000000) (-4298450495 / 1000000000000)
      | 7 => orderedInterval (5489702085 / 1000000000000) (5489702103 / 1000000000000)
      | _ => orderedInterval (-14667367251 / 1000000000000) (-14667366557 / 1000000000000)
    | 1 =>
      match b.val with
      | 0 => orderedInterval (12031086265 / 1000000000000) (12031087743 / 1000000000000)
      | 1 => orderedInterval (2607763049 / 1000000000000) (2607763069 / 1000000000000)
      | 2 => orderedInterval (-2059778516 / 1000000000000) (-2059778502 / 1000000000000)
      | 3 => orderedInterval (-1467332419 / 1000000000000) (-1467306663 / 1000000000000)
      | 4 => orderedInterval (2151281429 / 1000000000000) (2151281560 / 1000000000000)
      | 5 => orderedInterval (-1183184419 / 1000000000000) (-1183183601 / 1000000000000)
      | 6 => orderedInterval (2445049132 / 1000000000000) (2445051106 / 1000000000000)
      | 7 => orderedInterval (1754445718 / 1000000000000) (1754445734 / 1000000000000)
      | _ => orderedInterval (5610656310 / 1000000000000) (5610657364 / 1000000000000)
    | 2 =>
      match b.val with
      | 0 => orderedInterval (21367667262 / 1000000000000) (21367668725 / 1000000000000)
      | 1 => orderedInterval (-9452520937 / 1000000000000) (-9452520909 / 1000000000000)
      | 2 => orderedInterval (-2593570900 / 1000000000000) (-2593570875 / 1000000000000)
      | 3 => orderedInterval (-54026136700 / 1000000000000) (-54026079759 / 1000000000000)
      | 4 => orderedInterval (8957026774 / 1000000000000) (8957026986 / 1000000000000)
      | 5 => orderedInterval (1467058059 / 1000000000000) (1467059247 / 1000000000000)
      | 6 => orderedInterval (6583722446 / 1000000000000) (6583724444 / 1000000000000)
      | 7 => orderedInterval (-4473091847 / 1000000000000) (-4473091830 / 1000000000000)
      | _ => orderedInterval (29918985832 / 1000000000000) (29918987507 / 1000000000000)
    | 3 =>
      match b.val with
      | 0 => orderedInterval (-13231043825 / 1000000000000) (-13231042381 / 1000000000000)
      | 1 => orderedInterval (-6409430296 / 1000000000000) (-6409430255 / 1000000000000)
      | 2 => orderedInterval (9586189524 / 1000000000000) (9586189570 / 1000000000000)
      | 3 => orderedInterval (-10876215874 / 1000000000000) (-10876089635 / 1000000000000)
      | 4 => orderedInterval (-7249544122 / 1000000000000) (-7249543772 / 1000000000000)
      | 5 => orderedInterval (-2279235842 / 1000000000000) (-2279234123 / 1000000000000)
      | 6 => orderedInterval (-3957713907 / 1000000000000) (-3957711886 / 1000000000000)
      | 7 => orderedInterval (-2603337380 / 1000000000000) (-2603337363 / 1000000000000)
      | _ => orderedInterval (-13276506867 / 1000000000000) (-13276504119 / 1000000000000)
    | _ =>
      match b.val with
      | 0 => orderedInterval (-19496529763 / 1000000000000) (-19496528321 / 1000000000000)
      | 1 => orderedInterval (21041816310 / 1000000000000) (21041816373 / 1000000000000)
      | 2 => orderedInterval (5487412396 / 1000000000000) (5487412482 / 1000000000000)
      | 3 => orderedInterval (260611574885 / 1000000000000) (260611856660 / 1000000000000)
      | 4 => orderedInterval (-13686810352 / 1000000000000) (-13686809771 / 1000000000000)
      | 5 => orderedInterval (-54442893 / 1000000000000) (-54440394 / 1000000000000)
      | 6 => orderedInterval (-7999501263 / 1000000000000) (-7999499197 / 1000000000000)
      | 7 => orderedInterval (5367648328 / 1000000000000) (5367648345 / 1000000000000)
      | _ => orderedInterval (-71361001379 / 1000000000000) (-71360996701 / 1000000000000)
  coefficientTarget := fun i =>
    match i.val with
    | 0 => orderedInterval (-22020703013 / 1000000000000) (-22020686320 / 1000000000000)
    | 1 => orderedInterval (21889986549 / 1000000000000) (21890017810 / 1000000000000)
    | 2 => orderedInterval (-2250860011 / 1000000000000) (-2250796464 / 1000000000000)
    | 3 => orderedInterval (-50296838589 / 1000000000000) (-50296703964 / 1000000000000)
    | _ => orderedInterval (179910166269 / 1000000000000) (179910459476 / 1000000000000)

theorem compactCertificate268_stateChecks0 :
    compactCertificate268.stateChecks 0 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 45 12 (285 / 2)) (orderedInterval (-62967031767 / 1000000000000) (-62967028330 / 1000000000000), orderedInterval (22640543950 / 1000000000000) (22640547387 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 33 12 (83971884030357 / 800000000000)) (orderedInterval (-68130267298 / 1000000000000) (-68130252178 / 1000000000000), orderedInterval (38051259789 / 1000000000000) (38051274910 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 54 12 (27154781984181 / 160000000000)) (orderedInterval (46256265606 / 1000000000000) (46256265607 / 1000000000000), orderedInterval (40006143896 / 1000000000000) (40006143897 / 1000000000000))) = true
  norm_num [besselStateAtRationalPoint, besselIntervalStepZero,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, besselZeroTransition,
    besselInitial, besselGridStateAt, besselGridStateBlock00, besselGridStateBlock01,
    besselGridStateBlock02, besselGridStateBlock03, besselGridStateBlock04,
    besselGridStateBlock05, besselGridStateBlock06, besselGridStateBlock07,
    besselGridStateBlock08, besselGridStateBlock09, besselGridStateBlock10,
    besselGridStateBlock11, besselGridStateBlock12, besselGridStateBlock13,
    besselGridStateBlock14, besselGridState010, besselGridState013, besselGridState021, besselGridState025, besselGridState026, besselGridState033, besselGridState036, besselGridState039, besselGridState045, besselGridState046, besselGridState049, besselGridState052, besselGridState054, besselGridState056, besselGridState058, besselGridState059, besselGridState066, besselGridState069, besselGridState071, besselGridState079, besselGridState084, besselGridState090, besselGridState097, besselGridState101, besselGridState104, besselStateSubset, linearInterval, widenInterval,
    rationalErrorInterval, rationalIntervalSubset, orderedInterval, Finset.sum_range_succ,
    IntervalRat.add, IntervalRat.mul, IntervalRat.scale, IntervalRat.singleton]

theorem compactCertificate268_stateChecks1 :
    compactCertificate268.stateChecks 3 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 10 12 (24502786331199 / 800000000000)) (orderedInterval (-882890944 / 1000000000000) (-882890932 / 1000000000000), orderedInterval (144192097478 / 1000000000000) (144192097491 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 26 12 (65817930687603 / 800000000000)) (orderedInterval (86282066758 / 1000000000000) (86282066759 / 1000000000000), orderedInterval (16599387061 / 1000000000000) (16599387063 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 71 12 (178708485227751 / 800000000000)) (orderedInterval (-47989639379 / 1000000000000) (-47989639378 / 1000000000000), orderedInterval (-23277610663 / 1000000000000) (-23277610662 / 1000000000000))) = true
  norm_num [besselStateAtRationalPoint, besselIntervalStepZero,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, besselZeroTransition,
    besselInitial, besselGridStateAt, besselGridStateBlock00, besselGridStateBlock01,
    besselGridStateBlock02, besselGridStateBlock03, besselGridStateBlock04,
    besselGridStateBlock05, besselGridStateBlock06, besselGridStateBlock07,
    besselGridStateBlock08, besselGridStateBlock09, besselGridStateBlock10,
    besselGridStateBlock11, besselGridStateBlock12, besselGridStateBlock13,
    besselGridStateBlock14, besselGridState010, besselGridState013, besselGridState021, besselGridState025, besselGridState026, besselGridState033, besselGridState036, besselGridState039, besselGridState045, besselGridState046, besselGridState049, besselGridState052, besselGridState054, besselGridState056, besselGridState058, besselGridState059, besselGridState066, besselGridState069, besselGridState071, besselGridState079, besselGridState084, besselGridState090, besselGridState097, besselGridState101, besselGridState104, besselStateSubset, linearInterval, widenInterval,
    rationalErrorInterval, rationalIntervalSubset, orderedInterval, Finset.sum_range_succ,
    IntervalRat.add, IntervalRat.mul, IntervalRat.scale, IntervalRat.singleton]

theorem compactCertificate268_stateChecks2 :
    compactCertificate268.stateChecks 6 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 52 12 (131635861375263 / 800000000000)) (orderedInterval (57390861947 / 1000000000000) (57390868758 / 1000000000000), orderedInterval (-24158779202 / 1000000000000) (-24158772391 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 90 12 (225560292127899 / 800000000000)) (orderedInterval (-381030851 / 1000000000000) (-381030849 / 1000000000000), orderedInterval (47516701465 / 1000000000000) (47516701467 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 66 12 (166146690284241 / 800000000000)) (orderedInterval (49907632548 / 1000000000000) (49907632550 / 1000000000000), orderedInterval (23849849370 / 1000000000000) (23849849371 / 1000000000000))) = true
  norm_num [besselStateAtRationalPoint, besselIntervalStepZero,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, besselZeroTransition,
    besselInitial, besselGridStateAt, besselGridStateBlock00, besselGridStateBlock01,
    besselGridStateBlock02, besselGridStateBlock03, besselGridStateBlock04,
    besselGridStateBlock05, besselGridStateBlock06, besselGridStateBlock07,
    besselGridStateBlock08, besselGridStateBlock09, besselGridStateBlock10,
    besselGridStateBlock11, besselGridStateBlock12, besselGridStateBlock13,
    besselGridStateBlock14, besselGridState010, besselGridState013, besselGridState021, besselGridState025, besselGridState026, besselGridState033, besselGridState036, besselGridState039, besselGridState045, besselGridState046, besselGridState049, besselGridState052, besselGridState054, besselGridState056, besselGridState058, besselGridState059, besselGridState066, besselGridState069, besselGridState071, besselGridState079, besselGridState084, besselGridState090, besselGridState097, besselGridState101, besselGridState104, besselStateSubset, linearInterval, widenInterval,
    rationalErrorInterval, rationalIntervalSubset, orderedInterval, Finset.sum_range_succ,
    IntervalRat.add, IntervalRat.mul, IntervalRat.scale, IntervalRat.singleton]

theorem compactCertificate268_stateChecks3 :
    compactCertificate268.stateChecks 9 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 101 12 (254911749434943 / 800000000000)) (orderedInterval (-38035165794 / 1000000000000) (-38035103454 / 1000000000000), orderedInterval (23538520591 / 1000000000000) (23538582930 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 59 12 (147173367155847 / 800000000000)) (orderedInterval (33338838155 / 1000000000000) (33338847251 / 1000000000000), orderedInterval (-48557534452 / 1000000000000) (-48557525356 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 104 12 (261161722663923 / 800000000000)) (orderedInterval (21616998005 / 1000000000000) (21616998006 / 1000000000000), orderedInterval (38474334739 / 1000000000000) (38474334740 / 1000000000000))) = true
  norm_num [besselStateAtRationalPoint, besselIntervalStepZero,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, besselZeroTransition,
    besselInitial, besselGridStateAt, besselGridStateBlock00, besselGridStateBlock01,
    besselGridStateBlock02, besselGridStateBlock03, besselGridStateBlock04,
    besselGridStateBlock05, besselGridStateBlock06, besselGridStateBlock07,
    besselGridStateBlock08, besselGridStateBlock09, besselGridStateBlock10,
    besselGridStateBlock11, besselGridStateBlock12, besselGridStateBlock13,
    besselGridStateBlock14, besselGridState010, besselGridState013, besselGridState021, besselGridState025, besselGridState026, besselGridState033, besselGridState036, besselGridState039, besselGridState045, besselGridState046, besselGridState049, besselGridState052, besselGridState054, besselGridState056, besselGridState058, besselGridState059, besselGridState066, besselGridState069, besselGridState071, besselGridState079, besselGridState084, besselGridState090, besselGridState097, besselGridState101, besselGridState104, besselStateSubset, linearInterval, widenInterval,
    rationalErrorInterval, rationalIntervalSubset, orderedInterval, Finset.sum_range_succ,
    IntervalRat.add, IntervalRat.mul, IntervalRat.scale, IntervalRat.singleton]

theorem compactCertificate268_stateChecks4 :
    compactCertificate268.stateChecks 12 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 97 12 (244011158320287 / 800000000000)) (orderedInterval (-39953105367 / 1000000000000) (-39953105366 / 1000000000000), orderedInterval (-22091455077 / 1000000000000) (-22091455076 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 69 12 (174137876408271 / 800000000000)) (orderedInterval (-53713692752 / 1000000000000) (-53713692374 / 1000000000000), orderedInterval (6408418458 / 1000000000000) (6408418836 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 79 12 (197453792062809 / 800000000000)) (orderedInterval (27988919291 / 1000000000000) (27988924709 / 1000000000000), orderedInterval (-42435220072 / 1000000000000) (-42435214654 / 1000000000000))) = true
  norm_num [besselStateAtRationalPoint, besselIntervalStepZero,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, besselZeroTransition,
    besselInitial, besselGridStateAt, besselGridStateBlock00, besselGridStateBlock01,
    besselGridStateBlock02, besselGridStateBlock03, besselGridStateBlock04,
    besselGridStateBlock05, besselGridStateBlock06, besselGridStateBlock07,
    besselGridStateBlock08, besselGridStateBlock09, besselGridStateBlock10,
    besselGridStateBlock11, besselGridStateBlock12, besselGridStateBlock13,
    besselGridStateBlock14, besselGridState010, besselGridState013, besselGridState021, besselGridState025, besselGridState026, besselGridState033, besselGridState036, besselGridState039, besselGridState045, besselGridState046, besselGridState049, besselGridState052, besselGridState054, besselGridState056, besselGridState058, besselGridState059, besselGridState066, besselGridState069, besselGridState071, besselGridState079, besselGridState084, besselGridState090, besselGridState097, besselGridState101, besselGridState104, besselStateSubset, linearInterval, widenInterval,
    rationalErrorInterval, rationalIntervalSubset, orderedInterval, Finset.sum_range_succ,
    IntervalRat.add, IntervalRat.mul, IntervalRat.scale, IntervalRat.singleton]

theorem compactCertificate268_stateChecks5 :
    compactCertificate268.stateChecks 15 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 66 12 (164616386229321 / 800000000000)) (orderedInterval (-39505209440 / 1000000000000) (-39505161574 / 1000000000000), orderedInterval (39251739371 / 1000000000000) (39251787237 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 58 12 (145443569547741 / 800000000000)) (orderedInterval (21773115484 / 1000000000000) (21773115485 / 1000000000000), orderedInterval (54963879104 / 1000000000000) (54963879105 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 84 12 (42155215390359 / 160000000000)) (orderedInterval (17373186680 / 1000000000000) (17373186681 / 1000000000000), orderedInterval (45950333475 / 1000000000000) (45950333476 / 1000000000000))) = true
  norm_num [besselStateAtRationalPoint, besselIntervalStepZero,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, besselZeroTransition,
    besselInitial, besselGridStateAt, besselGridStateBlock00, besselGridStateBlock01,
    besselGridStateBlock02, besselGridStateBlock03, besselGridStateBlock04,
    besselGridStateBlock05, besselGridStateBlock06, besselGridStateBlock07,
    besselGridStateBlock08, besselGridStateBlock09, besselGridStateBlock10,
    besselGridStateBlock11, besselGridStateBlock12, besselGridStateBlock13,
    besselGridStateBlock14, besselGridState010, besselGridState013, besselGridState021, besselGridState025, besselGridState026, besselGridState033, besselGridState036, besselGridState039, besselGridState045, besselGridState046, besselGridState049, besselGridState052, besselGridState054, besselGridState056, besselGridState058, besselGridState059, besselGridState066, besselGridState069, besselGridState071, besselGridState079, besselGridState084, besselGridState090, besselGridState097, besselGridState101, besselGridState104, besselStateSubset, linearInterval, widenInterval,
    rationalErrorInterval, rationalIntervalSubset, orderedInterval, Finset.sum_range_succ,
    IntervalRat.add, IntervalRat.mul, IntervalRat.scale, IntervalRat.singleton]

theorem compactCertificate268_stateChecks6 :
    compactCertificate268.stateChecks 18 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 46 12 (116603544277173 / 800000000000)) (orderedInterval (59367532569 / 1000000000000) (59367543799 / 1000000000000), orderedInterval (-29242176509 / 1000000000000) (-29242165279 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 39 12 (98846115832653 / 800000000000)) (orderedInterval (-69564111361 / 1000000000000) (-69564110282 / 1000000000000), orderedInterval (17979196021 / 1000000000000) (17979197100 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 25 12 (61853309715759 / 800000000000)) (orderedInterval (38600308676 / 1000000000000) (38600311543 / 1000000000000), orderedInterval (-82371816258 / 1000000000000) (-82371813391 / 1000000000000))) = true
  norm_num [besselStateAtRationalPoint, besselIntervalStepZero,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, besselZeroTransition,
    besselInitial, besselGridStateAt, besselGridStateBlock00, besselGridStateBlock01,
    besselGridStateBlock02, besselGridStateBlock03, besselGridStateBlock04,
    besselGridStateBlock05, besselGridStateBlock06, besselGridStateBlock07,
    besselGridStateBlock08, besselGridStateBlock09, besselGridStateBlock10,
    besselGridStateBlock11, besselGridStateBlock12, besselGridStateBlock13,
    besselGridStateBlock14, besselGridState010, besselGridState013, besselGridState021, besselGridState025, besselGridState026, besselGridState033, besselGridState036, besselGridState039, besselGridState045, besselGridState046, besselGridState049, besselGridState052, besselGridState054, besselGridState056, besselGridState058, besselGridState059, besselGridState066, besselGridState069, besselGridState071, besselGridState079, besselGridState084, besselGridState090, besselGridState097, besselGridState101, besselGridState104, besselStateSubset, linearInterval, widenInterval,
    rationalErrorInterval, rationalIntervalSubset, orderedInterval, Finset.sum_range_succ,
    IntervalRat.add, IntervalRat.mul, IntervalRat.scale, IntervalRat.singleton]

theorem compactCertificate268_stateChecks7 :
    compactCertificate268.stateChecks 21 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 13 12 (33264915679953 / 800000000000)) (orderedInterval (-123588033689 / 1000000000000) (-123588033679 / 1000000000000), orderedInterval (-4446779207 / 1000000000000) (-4446779197 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 36 12 (90320717018859 / 800000000000)) (orderedInterval (41643698441 / 1000000000000) (41643698442 / 1000000000000), orderedInterval (62302154474 / 1000000000000) (62302154475 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 49 12 (123325217333643 / 800000000000)) (orderedInterval (-54181376001 / 1000000000000) (-54181376000 / 1000000000000), orderedInterval (-34379536278 / 1000000000000) (-34379536277 / 1000000000000))) = true
  norm_num [besselStateAtRationalPoint, besselIntervalStepZero,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, besselZeroTransition,
    besselInitial, besselGridStateAt, besselGridStateBlock00, besselGridStateBlock01,
    besselGridStateBlock02, besselGridStateBlock03, besselGridStateBlock04,
    besselGridStateBlock05, besselGridStateBlock06, besselGridStateBlock07,
    besselGridStateBlock08, besselGridStateBlock09, besselGridStateBlock10,
    besselGridStateBlock11, besselGridStateBlock12, besselGridStateBlock13,
    besselGridStateBlock14, besselGridState010, besselGridState013, besselGridState021, besselGridState025, besselGridState026, besselGridState033, besselGridState036, besselGridState039, besselGridState045, besselGridState046, besselGridState049, besselGridState052, besselGridState054, besselGridState056, besselGridState058, besselGridState059, besselGridState066, besselGridState069, besselGridState071, besselGridState079, besselGridState084, besselGridState090, besselGridState097, besselGridState101, besselGridState104, besselStateSubset, linearInterval, widenInterval,
    rationalErrorInterval, rationalIntervalSubset, orderedInterval, Finset.sum_range_succ,
    IntervalRat.add, IntervalRat.mul, IntervalRat.scale, IntervalRat.singleton]

theorem compactCertificate268_stateChecks8 :
    compactCertificate268.stateChecks 24 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 21 12 (52146690284241 / 800000000000)) (orderedInterval (652449349 / 1000000000000) (652449359 / 1000000000000), orderedInterval (-98830409056 / 1000000000000) (-98830409047 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 84 12 (211973400907761 / 800000000000)) (orderedInterval (47010414933 / 1000000000000) (47010418631 / 1000000000000), orderedInterval (-13968817152 / 1000000000000) (-13968813454 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 56 12 (141588408097599 / 800000000000)) (orderedInterval (57798695187 / 1000000000000) (57798697067 / 1000000000000), orderedInterval (-16173119240 / 1000000000000) (-16173117361 / 1000000000000))) = true
  norm_num [besselStateAtRationalPoint, besselIntervalStepZero,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, besselZeroTransition,
    besselInitial, besselGridStateAt, besselGridStateBlock00, besselGridStateBlock01,
    besselGridStateBlock02, besselGridStateBlock03, besselGridStateBlock04,
    besselGridStateBlock05, besselGridStateBlock06, besselGridStateBlock07,
    besselGridStateBlock08, besselGridStateBlock09, besselGridStateBlock10,
    besselGridStateBlock11, besselGridStateBlock12, besselGridStateBlock13,
    besselGridStateBlock14, besselGridState010, besselGridState013, besselGridState021, besselGridState025, besselGridState026, besselGridState033, besselGridState036, besselGridState039, besselGridState045, besselGridState046, besselGridState049, besselGridState052, besselGridState054, besselGridState056, besselGridState058, besselGridState059, besselGridState066, besselGridState069, besselGridState071, besselGridState079, besselGridState084, besselGridState090, besselGridState097, besselGridState101, besselGridState104, besselStateSubset, linearInterval, widenInterval,
    rationalErrorInterval, rationalIntervalSubset, orderedInterval, Finset.sum_range_succ,
    IntervalRat.add, IntervalRat.mul, IntervalRat.scale, IntervalRat.singleton]

theorem compactCertificate268_states : ∀ j,
    BesselStateValid (compactCertificate268.point j) (compactCertificate268.state j) :=
  compactCertificate268.statesValid_of_checks3 compactCertificate268_stateChecks0
    compactCertificate268_stateChecks1 compactCertificate268_stateChecks2
    compactCertificate268_stateChecks3 compactCertificate268_stateChecks4
    compactCertificate268_stateChecks5 compactCertificate268_stateChecks6
    compactCertificate268_stateChecks7 compactCertificate268_stateChecks8

theorem compactCertificate268_chunkChecks0_0 :
    compactCertificate268.chunkChecks (0 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 0) <| besselDerivativeNearFromState (285 / 2) 0 (IntervalRat.scale (285 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-62967031767 / 1000000000000) (-62967028330 / 1000000000000), orderedInterval (22640543950 / 1000000000000) (22640547387 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 0) <| besselDerivativeNearFromState (83971884030357 / 800000000000) 0 (IntervalRat.scale (285 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-68130267298 / 1000000000000) (-68130252178 / 1000000000000), orderedInterval (38051259789 / 1000000000000) (38051274910 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 0) <| besselDerivativeNearFromState (27154781984181 / 160000000000) 0 (IntervalRat.scale (285 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (46256265606 / 1000000000000) (46256265607 / 1000000000000), orderedInterval (40006143896 / 1000000000000) (40006143897 / 1000000000000)))) (orderedInterval (-22878398631 / 1000000000000) (-22878397118 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 0) <| besselDerivativeNearFromState (24502786331199 / 800000000000) 0 (IntervalRat.scale (285 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-882890944 / 1000000000000) (-882890932 / 1000000000000), orderedInterval (144192097478 / 1000000000000) (144192097491 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 0) <| besselDerivativeNearFromState (65817930687603 / 800000000000) 0 (IntervalRat.scale (285 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (86282066758 / 1000000000000) (86282066759 / 1000000000000), orderedInterval (16599387061 / 1000000000000) (16599387063 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 0) <| besselDerivativeNearFromState (178708485227751 / 800000000000) 0 (IntervalRat.scale (285 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-47989639379 / 1000000000000) (-47989639378 / 1000000000000), orderedInterval (-23277610663 / 1000000000000) (-23277610662 / 1000000000000)))) (orderedInterval (6571453873 / 1000000000000) (6571453891 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 0) <| besselDerivativeNearFromState (131635861375263 / 800000000000) 0 (IntervalRat.scale (285 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (57390861947 / 1000000000000) (57390868758 / 1000000000000), orderedInterval (-24158779202 / 1000000000000) (-24158772391 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 0) <| besselDerivativeNearFromState (225560292127899 / 800000000000) 0 (IntervalRat.scale (285 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-381030851 / 1000000000000) (-381030849 / 1000000000000), orderedInterval (47516701465 / 1000000000000) (47516701467 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 0) <| besselDerivativeNearFromState (166146690284241 / 800000000000) 0 (IntervalRat.scale (285 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (49907632548 / 1000000000000) (49907632550 / 1000000000000), orderedInterval (23849849370 / 1000000000000) (23849849371 / 1000000000000)))) (orderedInterval (1217921522 / 1000000000000) (1217921531 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate268_chunkChecks0_1 :
    compactCertificate268.chunkChecks (0 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 0) <| besselDerivativeNearFromState (254911749434943 / 800000000000) 0 (IntervalRat.scale (285 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-38035165794 / 1000000000000) (-38035103454 / 1000000000000), orderedInterval (23538520591 / 1000000000000) (23538582930 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 0) <| besselDerivativeNearFromState (147173367155847 / 800000000000) 0 (IntervalRat.scale (285 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (33338838155 / 1000000000000) (33338847251 / 1000000000000), orderedInterval (-48557534452 / 1000000000000) (-48557525356 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 0) <| besselDerivativeNearFromState (261161722663923 / 800000000000) 0 (IntervalRat.scale (285 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (21616998005 / 1000000000000) (21616998006 / 1000000000000), orderedInterval (38474334739 / 1000000000000) (38474334740 / 1000000000000)))) (orderedInterval (12301495815 / 1000000000000) (12301507623 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 0) <| besselDerivativeNearFromState (244011158320287 / 800000000000) 0 (IntervalRat.scale (285 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-39953105367 / 1000000000000) (-39953105366 / 1000000000000), orderedInterval (-22091455077 / 1000000000000) (-22091455076 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 0) <| besselDerivativeNearFromState (174137876408271 / 800000000000) 0 (IntervalRat.scale (285 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-53713692752 / 1000000000000) (-53713692374 / 1000000000000), orderedInterval (6408418458 / 1000000000000) (6408418836 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 0) <| besselDerivativeNearFromState (197453792062809 / 800000000000) 0 (IntervalRat.scale (285 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (27988919291 / 1000000000000) (27988924709 / 1000000000000), orderedInterval (-42435220072 / 1000000000000) (-42435214654 / 1000000000000)))) (orderedInterval (-4499683972 / 1000000000000) (-4499683892 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 0) <| besselDerivativeNearFromState (164616386229321 / 800000000000) 0 (IntervalRat.scale (285 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-39505209440 / 1000000000000) (-39505161574 / 1000000000000), orderedInterval (39251739371 / 1000000000000) (39251787237 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 0) <| besselDerivativeNearFromState (145443569547741 / 800000000000) 0 (IntervalRat.scale (285 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (21773115484 / 1000000000000) (21773115485 / 1000000000000), orderedInterval (54963879104 / 1000000000000) (54963879105 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 0) <| besselDerivativeNearFromState (42155215390359 / 160000000000) 0 (IntervalRat.scale (285 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (17373186680 / 1000000000000) (17373186681 / 1000000000000), orderedInterval (45950333475 / 1000000000000) (45950333476 / 1000000000000)))) (orderedInterval (-1257373973 / 1000000000000) (-1257373406 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate268_chunkChecks0_2 :
    compactCertificate268.chunkChecks (0 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 0) <| besselDerivativeNearFromState (116603544277173 / 800000000000) 0 (IntervalRat.scale (285 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (59367532569 / 1000000000000) (59367543799 / 1000000000000), orderedInterval (-29242176509 / 1000000000000) (-29242165279 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 0) <| besselDerivativeNearFromState (98846115832653 / 800000000000) 0 (IntervalRat.scale (285 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-69564111361 / 1000000000000) (-69564110282 / 1000000000000), orderedInterval (17979196021 / 1000000000000) (17979197100 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 0) <| besselDerivativeNearFromState (61853309715759 / 800000000000) 0 (IntervalRat.scale (285 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (38600308676 / 1000000000000) (38600311543 / 1000000000000), orderedInterval (-82371816258 / 1000000000000) (-82371813391 / 1000000000000)))) (orderedInterval (-4298452481 / 1000000000000) (-4298450495 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 0) <| besselDerivativeNearFromState (33264915679953 / 800000000000) 0 (IntervalRat.scale (285 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-123588033689 / 1000000000000) (-123588033679 / 1000000000000), orderedInterval (-4446779207 / 1000000000000) (-4446779197 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 0) <| besselDerivativeNearFromState (90320717018859 / 800000000000) 0 (IntervalRat.scale (285 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (41643698441 / 1000000000000) (41643698442 / 1000000000000), orderedInterval (62302154474 / 1000000000000) (62302154475 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 0) <| besselDerivativeNearFromState (123325217333643 / 800000000000) 0 (IntervalRat.scale (285 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-54181376001 / 1000000000000) (-54181376000 / 1000000000000), orderedInterval (-34379536278 / 1000000000000) (-34379536277 / 1000000000000)))) (orderedInterval (5489702085 / 1000000000000) (5489702103 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 0) <| besselDerivativeNearFromState (52146690284241 / 800000000000) 0 (IntervalRat.scale (285 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (652449349 / 1000000000000) (652449359 / 1000000000000), orderedInterval (-98830409056 / 1000000000000) (-98830409047 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 0) <| besselDerivativeNearFromState (211973400907761 / 800000000000) 0 (IntervalRat.scale (285 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (47010414933 / 1000000000000) (47010418631 / 1000000000000), orderedInterval (-13968817152 / 1000000000000) (-13968813454 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 0) <| besselDerivativeNearFromState (141588408097599 / 800000000000) 0 (IntervalRat.scale (285 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (57798695187 / 1000000000000) (57798697067 / 1000000000000), orderedInterval (-16173119240 / 1000000000000) (-16173117361 / 1000000000000)))) (orderedInterval (-14667367251 / 1000000000000) (-14667366557 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate268_chunkChecks0 :
    compactCertificate268.chunkChecks (0 : Fin 5) 0 9 = true :=
  compactCertificate268.chunkChecks_nine_of_three (0 : Fin 5) compactCertificate268_chunkChecks0_0
    compactCertificate268_chunkChecks0_1 compactCertificate268_chunkChecks0_2

theorem compactCertificate268_chunkChecks1_0 :
    compactCertificate268.chunkChecks (1 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 1) <| besselDerivativeNearFromState (285 / 2) 1 (IntervalRat.scale (285 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-62967031767 / 1000000000000) (-62967028330 / 1000000000000), orderedInterval (22640543950 / 1000000000000) (22640547387 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 1) <| besselDerivativeNearFromState (83971884030357 / 800000000000) 1 (IntervalRat.scale (285 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-68130267298 / 1000000000000) (-68130252178 / 1000000000000), orderedInterval (38051259789 / 1000000000000) (38051274910 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 1) <| besselDerivativeNearFromState (27154781984181 / 160000000000) 1 (IntervalRat.scale (285 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (46256265606 / 1000000000000) (46256265607 / 1000000000000), orderedInterval (40006143896 / 1000000000000) (40006143897 / 1000000000000)))) (orderedInterval (12031086265 / 1000000000000) (12031087743 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 1) <| besselDerivativeNearFromState (24502786331199 / 800000000000) 1 (IntervalRat.scale (285 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-882890944 / 1000000000000) (-882890932 / 1000000000000), orderedInterval (144192097478 / 1000000000000) (144192097491 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 1) <| besselDerivativeNearFromState (65817930687603 / 800000000000) 1 (IntervalRat.scale (285 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (86282066758 / 1000000000000) (86282066759 / 1000000000000), orderedInterval (16599387061 / 1000000000000) (16599387063 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 1) <| besselDerivativeNearFromState (178708485227751 / 800000000000) 1 (IntervalRat.scale (285 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-47989639379 / 1000000000000) (-47989639378 / 1000000000000), orderedInterval (-23277610663 / 1000000000000) (-23277610662 / 1000000000000)))) (orderedInterval (2607763049 / 1000000000000) (2607763069 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 1) <| besselDerivativeNearFromState (131635861375263 / 800000000000) 1 (IntervalRat.scale (285 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (57390861947 / 1000000000000) (57390868758 / 1000000000000), orderedInterval (-24158779202 / 1000000000000) (-24158772391 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 1) <| besselDerivativeNearFromState (225560292127899 / 800000000000) 1 (IntervalRat.scale (285 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-381030851 / 1000000000000) (-381030849 / 1000000000000), orderedInterval (47516701465 / 1000000000000) (47516701467 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 1) <| besselDerivativeNearFromState (166146690284241 / 800000000000) 1 (IntervalRat.scale (285 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (49907632548 / 1000000000000) (49907632550 / 1000000000000), orderedInterval (23849849370 / 1000000000000) (23849849371 / 1000000000000)))) (orderedInterval (-2059778516 / 1000000000000) (-2059778502 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate268_chunkChecks1_1 :
    compactCertificate268.chunkChecks (1 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 1) <| besselDerivativeNearFromState (254911749434943 / 800000000000) 1 (IntervalRat.scale (285 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-38035165794 / 1000000000000) (-38035103454 / 1000000000000), orderedInterval (23538520591 / 1000000000000) (23538582930 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 1) <| besselDerivativeNearFromState (147173367155847 / 800000000000) 1 (IntervalRat.scale (285 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (33338838155 / 1000000000000) (33338847251 / 1000000000000), orderedInterval (-48557534452 / 1000000000000) (-48557525356 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 1) <| besselDerivativeNearFromState (261161722663923 / 800000000000) 1 (IntervalRat.scale (285 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (21616998005 / 1000000000000) (21616998006 / 1000000000000), orderedInterval (38474334739 / 1000000000000) (38474334740 / 1000000000000)))) (orderedInterval (-1467332419 / 1000000000000) (-1467306663 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 1) <| besselDerivativeNearFromState (244011158320287 / 800000000000) 1 (IntervalRat.scale (285 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-39953105367 / 1000000000000) (-39953105366 / 1000000000000), orderedInterval (-22091455077 / 1000000000000) (-22091455076 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 1) <| besselDerivativeNearFromState (174137876408271 / 800000000000) 1 (IntervalRat.scale (285 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-53713692752 / 1000000000000) (-53713692374 / 1000000000000), orderedInterval (6408418458 / 1000000000000) (6408418836 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 1) <| besselDerivativeNearFromState (197453792062809 / 800000000000) 1 (IntervalRat.scale (285 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (27988919291 / 1000000000000) (27988924709 / 1000000000000), orderedInterval (-42435220072 / 1000000000000) (-42435214654 / 1000000000000)))) (orderedInterval (2151281429 / 1000000000000) (2151281560 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 1) <| besselDerivativeNearFromState (164616386229321 / 800000000000) 1 (IntervalRat.scale (285 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-39505209440 / 1000000000000) (-39505161574 / 1000000000000), orderedInterval (39251739371 / 1000000000000) (39251787237 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 1) <| besselDerivativeNearFromState (145443569547741 / 800000000000) 1 (IntervalRat.scale (285 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (21773115484 / 1000000000000) (21773115485 / 1000000000000), orderedInterval (54963879104 / 1000000000000) (54963879105 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 1) <| besselDerivativeNearFromState (42155215390359 / 160000000000) 1 (IntervalRat.scale (285 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (17373186680 / 1000000000000) (17373186681 / 1000000000000), orderedInterval (45950333475 / 1000000000000) (45950333476 / 1000000000000)))) (orderedInterval (-1183184419 / 1000000000000) (-1183183601 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate268_chunkChecks1_2 :
    compactCertificate268.chunkChecks (1 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 1) <| besselDerivativeNearFromState (116603544277173 / 800000000000) 1 (IntervalRat.scale (285 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (59367532569 / 1000000000000) (59367543799 / 1000000000000), orderedInterval (-29242176509 / 1000000000000) (-29242165279 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 1) <| besselDerivativeNearFromState (98846115832653 / 800000000000) 1 (IntervalRat.scale (285 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-69564111361 / 1000000000000) (-69564110282 / 1000000000000), orderedInterval (17979196021 / 1000000000000) (17979197100 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 1) <| besselDerivativeNearFromState (61853309715759 / 800000000000) 1 (IntervalRat.scale (285 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (38600308676 / 1000000000000) (38600311543 / 1000000000000), orderedInterval (-82371816258 / 1000000000000) (-82371813391 / 1000000000000)))) (orderedInterval (2445049132 / 1000000000000) (2445051106 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 1) <| besselDerivativeNearFromState (33264915679953 / 800000000000) 1 (IntervalRat.scale (285 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-123588033689 / 1000000000000) (-123588033679 / 1000000000000), orderedInterval (-4446779207 / 1000000000000) (-4446779197 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 1) <| besselDerivativeNearFromState (90320717018859 / 800000000000) 1 (IntervalRat.scale (285 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (41643698441 / 1000000000000) (41643698442 / 1000000000000), orderedInterval (62302154474 / 1000000000000) (62302154475 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 1) <| besselDerivativeNearFromState (123325217333643 / 800000000000) 1 (IntervalRat.scale (285 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-54181376001 / 1000000000000) (-54181376000 / 1000000000000), orderedInterval (-34379536278 / 1000000000000) (-34379536277 / 1000000000000)))) (orderedInterval (1754445718 / 1000000000000) (1754445734 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 1) <| besselDerivativeNearFromState (52146690284241 / 800000000000) 1 (IntervalRat.scale (285 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (652449349 / 1000000000000) (652449359 / 1000000000000), orderedInterval (-98830409056 / 1000000000000) (-98830409047 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 1) <| besselDerivativeNearFromState (211973400907761 / 800000000000) 1 (IntervalRat.scale (285 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (47010414933 / 1000000000000) (47010418631 / 1000000000000), orderedInterval (-13968817152 / 1000000000000) (-13968813454 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 1) <| besselDerivativeNearFromState (141588408097599 / 800000000000) 1 (IntervalRat.scale (285 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (57798695187 / 1000000000000) (57798697067 / 1000000000000), orderedInterval (-16173119240 / 1000000000000) (-16173117361 / 1000000000000)))) (orderedInterval (5610656310 / 1000000000000) (5610657364 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate268_chunkChecks1 :
    compactCertificate268.chunkChecks (1 : Fin 5) 0 9 = true :=
  compactCertificate268.chunkChecks_nine_of_three (1 : Fin 5) compactCertificate268_chunkChecks1_0
    compactCertificate268_chunkChecks1_1 compactCertificate268_chunkChecks1_2

theorem compactCertificate268_chunkChecks2_0 :
    compactCertificate268.chunkChecks (2 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 2) <| besselDerivativeNearFromState (285 / 2) 2 (IntervalRat.scale (285 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-62967031767 / 1000000000000) (-62967028330 / 1000000000000), orderedInterval (22640543950 / 1000000000000) (22640547387 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 2) <| besselDerivativeNearFromState (83971884030357 / 800000000000) 2 (IntervalRat.scale (285 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-68130267298 / 1000000000000) (-68130252178 / 1000000000000), orderedInterval (38051259789 / 1000000000000) (38051274910 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 2) <| besselDerivativeNearFromState (27154781984181 / 160000000000) 2 (IntervalRat.scale (285 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (46256265606 / 1000000000000) (46256265607 / 1000000000000), orderedInterval (40006143896 / 1000000000000) (40006143897 / 1000000000000)))) (orderedInterval (21367667262 / 1000000000000) (21367668725 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 2) <| besselDerivativeNearFromState (24502786331199 / 800000000000) 2 (IntervalRat.scale (285 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-882890944 / 1000000000000) (-882890932 / 1000000000000), orderedInterval (144192097478 / 1000000000000) (144192097491 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 2) <| besselDerivativeNearFromState (65817930687603 / 800000000000) 2 (IntervalRat.scale (285 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (86282066758 / 1000000000000) (86282066759 / 1000000000000), orderedInterval (16599387061 / 1000000000000) (16599387063 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 2) <| besselDerivativeNearFromState (178708485227751 / 800000000000) 2 (IntervalRat.scale (285 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-47989639379 / 1000000000000) (-47989639378 / 1000000000000), orderedInterval (-23277610663 / 1000000000000) (-23277610662 / 1000000000000)))) (orderedInterval (-9452520937 / 1000000000000) (-9452520909 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 2) <| besselDerivativeNearFromState (131635861375263 / 800000000000) 2 (IntervalRat.scale (285 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (57390861947 / 1000000000000) (57390868758 / 1000000000000), orderedInterval (-24158779202 / 1000000000000) (-24158772391 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 2) <| besselDerivativeNearFromState (225560292127899 / 800000000000) 2 (IntervalRat.scale (285 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-381030851 / 1000000000000) (-381030849 / 1000000000000), orderedInterval (47516701465 / 1000000000000) (47516701467 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 2) <| besselDerivativeNearFromState (166146690284241 / 800000000000) 2 (IntervalRat.scale (285 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (49907632548 / 1000000000000) (49907632550 / 1000000000000), orderedInterval (23849849370 / 1000000000000) (23849849371 / 1000000000000)))) (orderedInterval (-2593570900 / 1000000000000) (-2593570875 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate268_chunkChecks2_1 :
    compactCertificate268.chunkChecks (2 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 2) <| besselDerivativeNearFromState (254911749434943 / 800000000000) 2 (IntervalRat.scale (285 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-38035165794 / 1000000000000) (-38035103454 / 1000000000000), orderedInterval (23538520591 / 1000000000000) (23538582930 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 2) <| besselDerivativeNearFromState (147173367155847 / 800000000000) 2 (IntervalRat.scale (285 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (33338838155 / 1000000000000) (33338847251 / 1000000000000), orderedInterval (-48557534452 / 1000000000000) (-48557525356 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 2) <| besselDerivativeNearFromState (261161722663923 / 800000000000) 2 (IntervalRat.scale (285 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (21616998005 / 1000000000000) (21616998006 / 1000000000000), orderedInterval (38474334739 / 1000000000000) (38474334740 / 1000000000000)))) (orderedInterval (-54026136700 / 1000000000000) (-54026079759 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 2) <| besselDerivativeNearFromState (244011158320287 / 800000000000) 2 (IntervalRat.scale (285 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-39953105367 / 1000000000000) (-39953105366 / 1000000000000), orderedInterval (-22091455077 / 1000000000000) (-22091455076 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 2) <| besselDerivativeNearFromState (174137876408271 / 800000000000) 2 (IntervalRat.scale (285 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-53713692752 / 1000000000000) (-53713692374 / 1000000000000), orderedInterval (6408418458 / 1000000000000) (6408418836 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 2) <| besselDerivativeNearFromState (197453792062809 / 800000000000) 2 (IntervalRat.scale (285 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (27988919291 / 1000000000000) (27988924709 / 1000000000000), orderedInterval (-42435220072 / 1000000000000) (-42435214654 / 1000000000000)))) (orderedInterval (8957026774 / 1000000000000) (8957026986 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 2) <| besselDerivativeNearFromState (164616386229321 / 800000000000) 2 (IntervalRat.scale (285 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-39505209440 / 1000000000000) (-39505161574 / 1000000000000), orderedInterval (39251739371 / 1000000000000) (39251787237 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 2) <| besselDerivativeNearFromState (145443569547741 / 800000000000) 2 (IntervalRat.scale (285 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (21773115484 / 1000000000000) (21773115485 / 1000000000000), orderedInterval (54963879104 / 1000000000000) (54963879105 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 2) <| besselDerivativeNearFromState (42155215390359 / 160000000000) 2 (IntervalRat.scale (285 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (17373186680 / 1000000000000) (17373186681 / 1000000000000), orderedInterval (45950333475 / 1000000000000) (45950333476 / 1000000000000)))) (orderedInterval (1467058059 / 1000000000000) (1467059247 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate268_chunkChecks2_2 :
    compactCertificate268.chunkChecks (2 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 2) <| besselDerivativeNearFromState (116603544277173 / 800000000000) 2 (IntervalRat.scale (285 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (59367532569 / 1000000000000) (59367543799 / 1000000000000), orderedInterval (-29242176509 / 1000000000000) (-29242165279 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 2) <| besselDerivativeNearFromState (98846115832653 / 800000000000) 2 (IntervalRat.scale (285 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-69564111361 / 1000000000000) (-69564110282 / 1000000000000), orderedInterval (17979196021 / 1000000000000) (17979197100 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 2) <| besselDerivativeNearFromState (61853309715759 / 800000000000) 2 (IntervalRat.scale (285 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (38600308676 / 1000000000000) (38600311543 / 1000000000000), orderedInterval (-82371816258 / 1000000000000) (-82371813391 / 1000000000000)))) (orderedInterval (6583722446 / 1000000000000) (6583724444 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 2) <| besselDerivativeNearFromState (33264915679953 / 800000000000) 2 (IntervalRat.scale (285 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-123588033689 / 1000000000000) (-123588033679 / 1000000000000), orderedInterval (-4446779207 / 1000000000000) (-4446779197 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 2) <| besselDerivativeNearFromState (90320717018859 / 800000000000) 2 (IntervalRat.scale (285 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (41643698441 / 1000000000000) (41643698442 / 1000000000000), orderedInterval (62302154474 / 1000000000000) (62302154475 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 2) <| besselDerivativeNearFromState (123325217333643 / 800000000000) 2 (IntervalRat.scale (285 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-54181376001 / 1000000000000) (-54181376000 / 1000000000000), orderedInterval (-34379536278 / 1000000000000) (-34379536277 / 1000000000000)))) (orderedInterval (-4473091847 / 1000000000000) (-4473091830 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 2) <| besselDerivativeNearFromState (52146690284241 / 800000000000) 2 (IntervalRat.scale (285 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (652449349 / 1000000000000) (652449359 / 1000000000000), orderedInterval (-98830409056 / 1000000000000) (-98830409047 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 2) <| besselDerivativeNearFromState (211973400907761 / 800000000000) 2 (IntervalRat.scale (285 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (47010414933 / 1000000000000) (47010418631 / 1000000000000), orderedInterval (-13968817152 / 1000000000000) (-13968813454 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 2) <| besselDerivativeNearFromState (141588408097599 / 800000000000) 2 (IntervalRat.scale (285 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (57798695187 / 1000000000000) (57798697067 / 1000000000000), orderedInterval (-16173119240 / 1000000000000) (-16173117361 / 1000000000000)))) (orderedInterval (29918985832 / 1000000000000) (29918987507 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate268_chunkChecks2 :
    compactCertificate268.chunkChecks (2 : Fin 5) 0 9 = true :=
  compactCertificate268.chunkChecks_nine_of_three (2 : Fin 5) compactCertificate268_chunkChecks2_0
    compactCertificate268_chunkChecks2_1 compactCertificate268_chunkChecks2_2

theorem compactCertificate268_chunkChecks3_0 :
    compactCertificate268.chunkChecks (3 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 3) <| besselDerivativeNearFromState (285 / 2) 3 (IntervalRat.scale (285 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-62967031767 / 1000000000000) (-62967028330 / 1000000000000), orderedInterval (22640543950 / 1000000000000) (22640547387 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 3) <| besselDerivativeNearFromState (83971884030357 / 800000000000) 3 (IntervalRat.scale (285 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-68130267298 / 1000000000000) (-68130252178 / 1000000000000), orderedInterval (38051259789 / 1000000000000) (38051274910 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 3) <| besselDerivativeNearFromState (27154781984181 / 160000000000) 3 (IntervalRat.scale (285 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (46256265606 / 1000000000000) (46256265607 / 1000000000000), orderedInterval (40006143896 / 1000000000000) (40006143897 / 1000000000000)))) (orderedInterval (-13231043825 / 1000000000000) (-13231042381 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 3) <| besselDerivativeNearFromState (24502786331199 / 800000000000) 3 (IntervalRat.scale (285 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-882890944 / 1000000000000) (-882890932 / 1000000000000), orderedInterval (144192097478 / 1000000000000) (144192097491 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 3) <| besselDerivativeNearFromState (65817930687603 / 800000000000) 3 (IntervalRat.scale (285 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (86282066758 / 1000000000000) (86282066759 / 1000000000000), orderedInterval (16599387061 / 1000000000000) (16599387063 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 3) <| besselDerivativeNearFromState (178708485227751 / 800000000000) 3 (IntervalRat.scale (285 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-47989639379 / 1000000000000) (-47989639378 / 1000000000000), orderedInterval (-23277610663 / 1000000000000) (-23277610662 / 1000000000000)))) (orderedInterval (-6409430296 / 1000000000000) (-6409430255 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 3) <| besselDerivativeNearFromState (131635861375263 / 800000000000) 3 (IntervalRat.scale (285 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (57390861947 / 1000000000000) (57390868758 / 1000000000000), orderedInterval (-24158779202 / 1000000000000) (-24158772391 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 3) <| besselDerivativeNearFromState (225560292127899 / 800000000000) 3 (IntervalRat.scale (285 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-381030851 / 1000000000000) (-381030849 / 1000000000000), orderedInterval (47516701465 / 1000000000000) (47516701467 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 3) <| besselDerivativeNearFromState (166146690284241 / 800000000000) 3 (IntervalRat.scale (285 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (49907632548 / 1000000000000) (49907632550 / 1000000000000), orderedInterval (23849849370 / 1000000000000) (23849849371 / 1000000000000)))) (orderedInterval (9586189524 / 1000000000000) (9586189570 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate268_chunkChecks3_1 :
    compactCertificate268.chunkChecks (3 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 3) <| besselDerivativeNearFromState (254911749434943 / 800000000000) 3 (IntervalRat.scale (285 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-38035165794 / 1000000000000) (-38035103454 / 1000000000000), orderedInterval (23538520591 / 1000000000000) (23538582930 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 3) <| besselDerivativeNearFromState (147173367155847 / 800000000000) 3 (IntervalRat.scale (285 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (33338838155 / 1000000000000) (33338847251 / 1000000000000), orderedInterval (-48557534452 / 1000000000000) (-48557525356 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 3) <| besselDerivativeNearFromState (261161722663923 / 800000000000) 3 (IntervalRat.scale (285 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (21616998005 / 1000000000000) (21616998006 / 1000000000000), orderedInterval (38474334739 / 1000000000000) (38474334740 / 1000000000000)))) (orderedInterval (-10876215874 / 1000000000000) (-10876089635 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 3) <| besselDerivativeNearFromState (244011158320287 / 800000000000) 3 (IntervalRat.scale (285 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-39953105367 / 1000000000000) (-39953105366 / 1000000000000), orderedInterval (-22091455077 / 1000000000000) (-22091455076 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 3) <| besselDerivativeNearFromState (174137876408271 / 800000000000) 3 (IntervalRat.scale (285 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-53713692752 / 1000000000000) (-53713692374 / 1000000000000), orderedInterval (6408418458 / 1000000000000) (6408418836 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 3) <| besselDerivativeNearFromState (197453792062809 / 800000000000) 3 (IntervalRat.scale (285 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (27988919291 / 1000000000000) (27988924709 / 1000000000000), orderedInterval (-42435220072 / 1000000000000) (-42435214654 / 1000000000000)))) (orderedInterval (-7249544122 / 1000000000000) (-7249543772 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 3) <| besselDerivativeNearFromState (164616386229321 / 800000000000) 3 (IntervalRat.scale (285 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-39505209440 / 1000000000000) (-39505161574 / 1000000000000), orderedInterval (39251739371 / 1000000000000) (39251787237 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 3) <| besselDerivativeNearFromState (145443569547741 / 800000000000) 3 (IntervalRat.scale (285 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (21773115484 / 1000000000000) (21773115485 / 1000000000000), orderedInterval (54963879104 / 1000000000000) (54963879105 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 3) <| besselDerivativeNearFromState (42155215390359 / 160000000000) 3 (IntervalRat.scale (285 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (17373186680 / 1000000000000) (17373186681 / 1000000000000), orderedInterval (45950333475 / 1000000000000) (45950333476 / 1000000000000)))) (orderedInterval (-2279235842 / 1000000000000) (-2279234123 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate268_chunkChecks3_2 :
    compactCertificate268.chunkChecks (3 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 3) <| besselDerivativeNearFromState (116603544277173 / 800000000000) 3 (IntervalRat.scale (285 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (59367532569 / 1000000000000) (59367543799 / 1000000000000), orderedInterval (-29242176509 / 1000000000000) (-29242165279 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 3) <| besselDerivativeNearFromState (98846115832653 / 800000000000) 3 (IntervalRat.scale (285 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-69564111361 / 1000000000000) (-69564110282 / 1000000000000), orderedInterval (17979196021 / 1000000000000) (17979197100 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 3) <| besselDerivativeNearFromState (61853309715759 / 800000000000) 3 (IntervalRat.scale (285 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (38600308676 / 1000000000000) (38600311543 / 1000000000000), orderedInterval (-82371816258 / 1000000000000) (-82371813391 / 1000000000000)))) (orderedInterval (-3957713907 / 1000000000000) (-3957711886 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 3) <| besselDerivativeNearFromState (33264915679953 / 800000000000) 3 (IntervalRat.scale (285 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-123588033689 / 1000000000000) (-123588033679 / 1000000000000), orderedInterval (-4446779207 / 1000000000000) (-4446779197 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 3) <| besselDerivativeNearFromState (90320717018859 / 800000000000) 3 (IntervalRat.scale (285 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (41643698441 / 1000000000000) (41643698442 / 1000000000000), orderedInterval (62302154474 / 1000000000000) (62302154475 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 3) <| besselDerivativeNearFromState (123325217333643 / 800000000000) 3 (IntervalRat.scale (285 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-54181376001 / 1000000000000) (-54181376000 / 1000000000000), orderedInterval (-34379536278 / 1000000000000) (-34379536277 / 1000000000000)))) (orderedInterval (-2603337380 / 1000000000000) (-2603337363 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 3) <| besselDerivativeNearFromState (52146690284241 / 800000000000) 3 (IntervalRat.scale (285 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (652449349 / 1000000000000) (652449359 / 1000000000000), orderedInterval (-98830409056 / 1000000000000) (-98830409047 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 3) <| besselDerivativeNearFromState (211973400907761 / 800000000000) 3 (IntervalRat.scale (285 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (47010414933 / 1000000000000) (47010418631 / 1000000000000), orderedInterval (-13968817152 / 1000000000000) (-13968813454 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 3) <| besselDerivativeNearFromState (141588408097599 / 800000000000) 3 (IntervalRat.scale (285 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (57798695187 / 1000000000000) (57798697067 / 1000000000000), orderedInterval (-16173119240 / 1000000000000) (-16173117361 / 1000000000000)))) (orderedInterval (-13276506867 / 1000000000000) (-13276504119 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate268_chunkChecks3 :
    compactCertificate268.chunkChecks (3 : Fin 5) 0 9 = true :=
  compactCertificate268.chunkChecks_nine_of_three (3 : Fin 5) compactCertificate268_chunkChecks3_0
    compactCertificate268_chunkChecks3_1 compactCertificate268_chunkChecks3_2

theorem compactCertificate268_chunkChecks4_0 :
    compactCertificate268.chunkChecks (4 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 4) <| besselDerivativeNearFromState (285 / 2) 4 (IntervalRat.scale (285 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-62967031767 / 1000000000000) (-62967028330 / 1000000000000), orderedInterval (22640543950 / 1000000000000) (22640547387 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 4) <| besselDerivativeNearFromState (83971884030357 / 800000000000) 4 (IntervalRat.scale (285 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-68130267298 / 1000000000000) (-68130252178 / 1000000000000), orderedInterval (38051259789 / 1000000000000) (38051274910 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 4) <| besselDerivativeNearFromState (27154781984181 / 160000000000) 4 (IntervalRat.scale (285 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (46256265606 / 1000000000000) (46256265607 / 1000000000000), orderedInterval (40006143896 / 1000000000000) (40006143897 / 1000000000000)))) (orderedInterval (-19496529763 / 1000000000000) (-19496528321 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 4) <| besselDerivativeNearFromState (24502786331199 / 800000000000) 4 (IntervalRat.scale (285 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-882890944 / 1000000000000) (-882890932 / 1000000000000), orderedInterval (144192097478 / 1000000000000) (144192097491 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 4) <| besselDerivativeNearFromState (65817930687603 / 800000000000) 4 (IntervalRat.scale (285 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (86282066758 / 1000000000000) (86282066759 / 1000000000000), orderedInterval (16599387061 / 1000000000000) (16599387063 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 4) <| besselDerivativeNearFromState (178708485227751 / 800000000000) 4 (IntervalRat.scale (285 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-47989639379 / 1000000000000) (-47989639378 / 1000000000000), orderedInterval (-23277610663 / 1000000000000) (-23277610662 / 1000000000000)))) (orderedInterval (21041816310 / 1000000000000) (21041816373 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 4) <| besselDerivativeNearFromState (131635861375263 / 800000000000) 4 (IntervalRat.scale (285 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (57390861947 / 1000000000000) (57390868758 / 1000000000000), orderedInterval (-24158779202 / 1000000000000) (-24158772391 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 4) <| besselDerivativeNearFromState (225560292127899 / 800000000000) 4 (IntervalRat.scale (285 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-381030851 / 1000000000000) (-381030849 / 1000000000000), orderedInterval (47516701465 / 1000000000000) (47516701467 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 4) <| besselDerivativeNearFromState (166146690284241 / 800000000000) 4 (IntervalRat.scale (285 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (49907632548 / 1000000000000) (49907632550 / 1000000000000), orderedInterval (23849849370 / 1000000000000) (23849849371 / 1000000000000)))) (orderedInterval (5487412396 / 1000000000000) (5487412482 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate268_chunkChecks4_1 :
    compactCertificate268.chunkChecks (4 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 4) <| besselDerivativeNearFromState (254911749434943 / 800000000000) 4 (IntervalRat.scale (285 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-38035165794 / 1000000000000) (-38035103454 / 1000000000000), orderedInterval (23538520591 / 1000000000000) (23538582930 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 4) <| besselDerivativeNearFromState (147173367155847 / 800000000000) 4 (IntervalRat.scale (285 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (33338838155 / 1000000000000) (33338847251 / 1000000000000), orderedInterval (-48557534452 / 1000000000000) (-48557525356 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 4) <| besselDerivativeNearFromState (261161722663923 / 800000000000) 4 (IntervalRat.scale (285 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (21616998005 / 1000000000000) (21616998006 / 1000000000000), orderedInterval (38474334739 / 1000000000000) (38474334740 / 1000000000000)))) (orderedInterval (260611574885 / 1000000000000) (260611856660 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 4) <| besselDerivativeNearFromState (244011158320287 / 800000000000) 4 (IntervalRat.scale (285 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-39953105367 / 1000000000000) (-39953105366 / 1000000000000), orderedInterval (-22091455077 / 1000000000000) (-22091455076 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 4) <| besselDerivativeNearFromState (174137876408271 / 800000000000) 4 (IntervalRat.scale (285 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-53713692752 / 1000000000000) (-53713692374 / 1000000000000), orderedInterval (6408418458 / 1000000000000) (6408418836 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 4) <| besselDerivativeNearFromState (197453792062809 / 800000000000) 4 (IntervalRat.scale (285 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (27988919291 / 1000000000000) (27988924709 / 1000000000000), orderedInterval (-42435220072 / 1000000000000) (-42435214654 / 1000000000000)))) (orderedInterval (-13686810352 / 1000000000000) (-13686809771 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 4) <| besselDerivativeNearFromState (164616386229321 / 800000000000) 4 (IntervalRat.scale (285 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-39505209440 / 1000000000000) (-39505161574 / 1000000000000), orderedInterval (39251739371 / 1000000000000) (39251787237 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 4) <| besselDerivativeNearFromState (145443569547741 / 800000000000) 4 (IntervalRat.scale (285 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (21773115484 / 1000000000000) (21773115485 / 1000000000000), orderedInterval (54963879104 / 1000000000000) (54963879105 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 4) <| besselDerivativeNearFromState (42155215390359 / 160000000000) 4 (IntervalRat.scale (285 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (17373186680 / 1000000000000) (17373186681 / 1000000000000), orderedInterval (45950333475 / 1000000000000) (45950333476 / 1000000000000)))) (orderedInterval (-54442893 / 1000000000000) (-54440394 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate268_chunkChecks4_2 :
    compactCertificate268.chunkChecks (4 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 4) <| besselDerivativeNearFromState (116603544277173 / 800000000000) 4 (IntervalRat.scale (285 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (59367532569 / 1000000000000) (59367543799 / 1000000000000), orderedInterval (-29242176509 / 1000000000000) (-29242165279 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 4) <| besselDerivativeNearFromState (98846115832653 / 800000000000) 4 (IntervalRat.scale (285 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-69564111361 / 1000000000000) (-69564110282 / 1000000000000), orderedInterval (17979196021 / 1000000000000) (17979197100 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 4) <| besselDerivativeNearFromState (61853309715759 / 800000000000) 4 (IntervalRat.scale (285 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (38600308676 / 1000000000000) (38600311543 / 1000000000000), orderedInterval (-82371816258 / 1000000000000) (-82371813391 / 1000000000000)))) (orderedInterval (-7999501263 / 1000000000000) (-7999499197 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 4) <| besselDerivativeNearFromState (33264915679953 / 800000000000) 4 (IntervalRat.scale (285 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-123588033689 / 1000000000000) (-123588033679 / 1000000000000), orderedInterval (-4446779207 / 1000000000000) (-4446779197 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 4) <| besselDerivativeNearFromState (90320717018859 / 800000000000) 4 (IntervalRat.scale (285 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (41643698441 / 1000000000000) (41643698442 / 1000000000000), orderedInterval (62302154474 / 1000000000000) (62302154475 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 4) <| besselDerivativeNearFromState (123325217333643 / 800000000000) 4 (IntervalRat.scale (285 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-54181376001 / 1000000000000) (-54181376000 / 1000000000000), orderedInterval (-34379536278 / 1000000000000) (-34379536277 / 1000000000000)))) (orderedInterval (5367648328 / 1000000000000) (5367648345 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 4) <| besselDerivativeNearFromState (52146690284241 / 800000000000) 4 (IntervalRat.scale (285 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (652449349 / 1000000000000) (652449359 / 1000000000000), orderedInterval (-98830409056 / 1000000000000) (-98830409047 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 4) <| besselDerivativeNearFromState (211973400907761 / 800000000000) 4 (IntervalRat.scale (285 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (47010414933 / 1000000000000) (47010418631 / 1000000000000), orderedInterval (-13968817152 / 1000000000000) (-13968813454 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 4) <| besselDerivativeNearFromState (141588408097599 / 800000000000) 4 (IntervalRat.scale (285 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (57798695187 / 1000000000000) (57798697067 / 1000000000000), orderedInterval (-16173119240 / 1000000000000) (-16173117361 / 1000000000000)))) (orderedInterval (-71361001379 / 1000000000000) (-71360996701 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate268_chunkChecks4 :
    compactCertificate268.chunkChecks (4 : Fin 5) 0 9 = true :=
  compactCertificate268.chunkChecks_nine_of_three (4 : Fin 5) compactCertificate268_chunkChecks4_0
    compactCertificate268_chunkChecks4_1 compactCertificate268_chunkChecks4_2

theorem compactCertificate268_chunks :
    ∀ r : Fin 5, ∀ b, compactCertificate268.chunkCheck r b = true :=
  compactCertificate268.chunkChecks_all (by
    intro r
    fin_cases r
    · exact compactCertificate268_chunkChecks0
    · exact compactCertificate268_chunkChecks1
    · exact compactCertificate268_chunkChecks2
    · exact compactCertificate268_chunkChecks3
    · exact compactCertificate268_chunkChecks4)

theorem compactCertificate268_coefficient0 :
    compactCertificate268.coefficientCheck (0 : Fin 5) = true := by
  norm_num [CompactCertificate.coefficientCheck, intervalFinSumHull,
    compactCertificate268, rationalIntervalSubset, orderedInterval, Fin.sum_univ_succ]

theorem compactCertificate268_coefficient1 :
    compactCertificate268.coefficientCheck (1 : Fin 5) = true := by
  norm_num [CompactCertificate.coefficientCheck, intervalFinSumHull,
    compactCertificate268, rationalIntervalSubset, orderedInterval, Fin.sum_univ_succ]

theorem compactCertificate268_coefficient2 :
    compactCertificate268.coefficientCheck (2 : Fin 5) = true := by
  norm_num [CompactCertificate.coefficientCheck, intervalFinSumHull,
    compactCertificate268, rationalIntervalSubset, orderedInterval, Fin.sum_univ_succ]

theorem compactCertificate268_coefficient3 :
    compactCertificate268.coefficientCheck (3 : Fin 5) = true := by
  norm_num [CompactCertificate.coefficientCheck, intervalFinSumHull,
    compactCertificate268, rationalIntervalSubset, orderedInterval, Fin.sum_univ_succ]

theorem compactCertificate268_coefficient4 :
    compactCertificate268.coefficientCheck (4 : Fin 5) = true := by
  norm_num [CompactCertificate.coefficientCheck, intervalFinSumHull,
    compactCertificate268, rationalIntervalSubset, orderedInterval, Fin.sum_univ_succ]

theorem compactCertificate268_coefficients : ∀ r : Fin 5,
    compactCertificate268.coefficientCheck r = true := by
  intro r
  fin_cases r
  · exact compactCertificate268_coefficient0
  · exact compactCertificate268_coefficient1
  · exact compactCertificate268_coefficient2
  · exact compactCertificate268_coefficient3
  · exact compactCertificate268_coefficient4

theorem compactCertificate268_lower : (1 : ℚ) ≤ compactCertificate268.output.lo := by
  norm_num [CompactCertificate.output, CompactCertificate.interval,
    CompactCertificate.coefficientTargetNat, compactCertificate268, dualConstant,
    intervalTaylorSum, intervalPow, intervalSub, intervalMaxAbs, widenInterval,
    rationalErrorInterval, orderedInterval, IntervalRat.add, IntervalRat.mul, IntervalRat.scale,
    IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4]

theorem compactCertificate268_proves {t : ℝ} (ht : t ∈ compactCertificate268.interval) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t :=
  compactCertificate268.proves compactCertificate268_states compactCertificate268_chunks
    compactCertificate268_coefficients compactCertificate268_lower ht

end Erdos232
