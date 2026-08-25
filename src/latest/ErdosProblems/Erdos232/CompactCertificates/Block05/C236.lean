/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, OpenAI Codex
-/
import ErdosProblems.Erdos232.CompactBase

open LeanCert.Core
namespace Erdos232

def compactCertificate236 : CompactCertificate where
  left := 113
  right := 114
  center := 227 / 2
  grid := fun i =>
    match i.val with
    | 0 => 36
    | 1 => 27
    | 2 => 43
    | 3 => 8
    | 4 => 21
    | 5 => 57
    | 6 => 42
    | 7 => 72
    | 8 => 53
    | 9 => 81
    | 10 => 47
    | 11 => 83
    | 12 => 77
    | 13 => 55
    | 14 => 63
    | 15 => 52
    | 16 => 46
    | 17 => 67
    | 18 => 37
    | 19 => 31
    | 20 => 20
    | 21 => 11
    | 22 => 29
    | 23 => 39
    | 24 => 17
    | 25 => 67
    | _ => 45
  point := fun i =>
    match i.val with
    | 0 => 227 / 2
    | 1 => 334414345173527 / 4000000000000
    | 2 => 108142728252791 / 800000000000
    | 3 => 97581271880389 / 4000000000000
    | 4 => 262117022212033 / 4000000000000
    | 5 => 711698704328061 / 4000000000000
    | 6 => 524234044424293 / 4000000000000
    | 7 => 898283970404089 / 4000000000000
    | 8 => 661671906921451 / 4000000000000
    | 9 => 1015174861784773 / 4000000000000
    | 10 => 586111479725917 / 4000000000000
    | 11 => 1040065106047553 / 4000000000000
    | 12 => 971763735766757 / 4000000000000
    | 13 => 693496455169781 / 4000000000000
    | 14 => 786351066636099 / 4000000000000
    | 15 => 655577538141331 / 4000000000000
    | 16 => 579222636619951 / 4000000000000
    | 17 => 167881296379149 / 800000000000
    | 18 => 464368500893303 / 4000000000000
    | 19 => 393650320947583 / 4000000000000
    | 20 => 246328093078549 / 4000000000000
    | 21 => 132476067707883 / 4000000000000
    | 22 => 359698294092649 / 4000000000000
    | 23 => 491137269030473 / 4000000000000
    | 24 => 207671906921451 / 4000000000000
    | 25 => 844174772036171 / 4000000000000
    | _ => 563869625230789 / 4000000000000
  state := fun i =>
    match i.val with
    | 0 => (orderedInterval (69443243969 / 1000000000000) (69443243970 / 1000000000000), orderedInterval (27740148711 / 1000000000000) (27740148712 / 1000000000000))
    | 1 => (orderedInterval (36813521833 / 1000000000000) (36813524489 / 1000000000000), orderedInterval (-79337760205 / 1000000000000) (-79337757550 / 1000000000000))
    | 2 => (orderedInterval (-52646566276 / 1000000000000) (-52646566275 / 1000000000000), orderedInterval (-43825853429 / 1000000000000) (-43825853428 / 1000000000000))
    | 3 => (orderedInterval (6920130062 / 1000000000000) (6920130067 / 1000000000000), orderedInterval (161269317261 / 1000000000000) (161269317267 / 1000000000000))
    | 4 => (orderedInterval (-32804665728 / 1000000000000) (-32804665727 / 1000000000000), orderedInterval (-92696578789 / 1000000000000) (-92696578788 / 1000000000000))
    | 5 => (orderedInterval (21150705033 / 1000000000000) (21150705681 / 1000000000000), orderedInterval (-56011987879 / 1000000000000) (-56011987232 / 1000000000000))
    | 6 => (orderedInterval (-7230849902 / 1000000000000) (-7230849876 / 1000000000000), orderedInterval (69347660248 / 1000000000000) (69347660274 / 1000000000000))
    | 7 => (orderedInterval (-39605721440 / 1000000000000) (-39605653872 / 1000000000000), orderedInterval (35672060622 / 1000000000000) (35672128190 / 1000000000000))
    | 8 => (orderedInterval (18439196152 / 1000000000000) (18439196483 / 1000000000000), orderedInterval (-59288859328 / 1000000000000) (-59288858997 / 1000000000000))
    | 9 => (orderedInterval (-5479029846 / 1000000000000) (-5479029845 / 1000000000000), orderedInterval (-49772729496 / 1000000000000) (-49772729495 / 1000000000000))
    | 10 => (orderedInterval (22133057544 / 1000000000000) (22133058166 / 1000000000000), orderedInterval (-62162948875 / 1000000000000) (-62162948253 / 1000000000000))
    | 11 => (orderedInterval (-2423786505 / 1000000000000) (-2423786504 / 1000000000000), orderedInterval (-49417136764 / 1000000000000) (-49417136763 / 1000000000000))
    | 12 => (orderedInterval (-49568727831 / 1000000000000) (-49568725595 / 1000000000000), orderedInterval (12885125760 / 1000000000000) (12885127996 / 1000000000000))
    | 13 => (orderedInterval (-59393329990 / 1000000000000) (-59393329987 / 1000000000000), orderedInterval (-11843737016 / 1000000000000) (-11843737013 / 1000000000000))
    | 14 => (orderedInterval (29637841273 / 1000000000000) (29637846124 / 1000000000000), orderedInterval (-48654718463 / 1000000000000) (-48654713612 / 1000000000000))
    | 15 => (orderedInterval (60315255922 / 1000000000000) (60315255923 / 1000000000000), orderedInterval (15512603055 / 1000000000000) (15512603056 / 1000000000000))
    | 16 => (orderedInterval (58382021871 / 1000000000000) (58382021872 / 1000000000000), orderedInterval (31229270146 / 1000000000000) (31229270147 / 1000000000000))
    | 17 => (orderedInterval (-8215339623 / 1000000000000) (-8215339622 / 1000000000000), orderedInterval (-54443097964 / 1000000000000) (-54443097963 / 1000000000000))
    | 18 => (orderedInterval (-44075975785 / 1000000000000) (-44075975784 / 1000000000000), orderedInterval (-59317058366 / 1000000000000) (-59317058365 / 1000000000000))
    | 19 => (orderedInterval (-78189299398 / 1000000000000) (-78189298598 / 1000000000000), orderedInterval (19245194325 / 1000000000000) (19245195124 / 1000000000000))
    | 20 => (orderedInterval (-45725263285 / 1000000000000) (-45725259114 / 1000000000000), orderedInterval (91185085872 / 1000000000000) (91185090042 / 1000000000000))
    | 21 => (orderedInterval (84657675308 / 1000000000000) (84657706240 / 1000000000000), orderedInterval (-111076774414 / 1000000000000) (-111076743481 / 1000000000000))
    | 22 => (orderedInterval (32579599987 / 1000000000000) (32579601663 / 1000000000000), orderedInterval (-77757767278 / 1000000000000) (-77757765603 / 1000000000000))
    | 23 => (orderedInterval (-62336651863 / 1000000000000) (-62336651862 / 1000000000000), orderedInterval (-35787559889 / 1000000000000) (-35787559888 / 1000000000000))
    | 24 => (orderedInterval (71851070681 / 1000000000000) (71851115469 / 1000000000000), orderedInterval (-84950689888 / 1000000000000) (-84950645099 / 1000000000000))
    | 25 => (orderedInterval (-53488986952 / 1000000000000) (-53488986950 / 1000000000000), orderedInterval (-12341288892 / 1000000000000) (-12341288890 / 1000000000000))
    | _ => (orderedInterval (-24941931769 / 1000000000000) (-24941931768 / 1000000000000), orderedInterval (-62313444376 / 1000000000000) (-62313444375 / 1000000000000))
  chunkTarget := fun r b =>
    match r.val with
    | 0 =>
      match b.val with
      | 0 => orderedInterval (24778540984 / 1000000000000) (24778541018 / 1000000000000)
      | 1 => orderedInterval (-2776430209 / 1000000000000) (-2776430148 / 1000000000000)
      | 2 => orderedInterval (1667235814 / 1000000000000) (1667237914 / 1000000000000)
      | 3 => orderedInterval (2268879325 / 1000000000000) (2268879417 / 1000000000000)
      | 4 => orderedInterval (-4871519619 / 1000000000000) (-4871519539 / 1000000000000)
      | 5 => orderedInterval (-2854853588 / 1000000000000) (-2854853576 / 1000000000000)
      | 6 => orderedInterval (9984327910 / 1000000000000) (9984328120 / 1000000000000)
      | 7 => orderedInterval (2475067173 / 1000000000000) (2475067797 / 1000000000000)
      | _ => orderedInterval (9467008427 / 1000000000000) (9467008730 / 1000000000000)
    | 1 =>
      match b.val with
      | 0 => orderedInterval (7387724498 / 1000000000000) (7387724526 / 1000000000000)
      | 1 => orderedInterval (3911939737 / 1000000000000) (3911939826 / 1000000000000)
      | 2 => orderedInterval (-4265335133 / 1000000000000) (-4265330986 / 1000000000000)
      | 3 => orderedInterval (-2263574516 / 1000000000000) (-2263574362 / 1000000000000)
      | 4 => orderedInterval (-1782230486 / 1000000000000) (-1782230334 / 1000000000000)
      | 5 => orderedInterval (-4598716709 / 1000000000000) (-4598716692 / 1000000000000)
      | 6 => orderedInterval (10367130585 / 1000000000000) (10367130725 / 1000000000000)
      | 7 => orderedInterval (4963220136 / 1000000000000) (4963220346 / 1000000000000)
      | _ => orderedInterval (16154798653 / 1000000000000) (16154798822 / 1000000000000)
    | 2 =>
      match b.val with
      | 0 => orderedInterval (-23393886727 / 1000000000000) (-23393886702 / 1000000000000)
      | 1 => orderedInterval (4063231532 / 1000000000000) (4063231668 / 1000000000000)
      | 2 => orderedInterval (-5691380673 / 1000000000000) (-5691372440 / 1000000000000)
      | 3 => orderedInterval (-5772681036 / 1000000000000) (-5772680756 / 1000000000000)
      | 4 => orderedInterval (9470738858 / 1000000000000) (9470739156 / 1000000000000)
      | 5 => orderedInterval (4745495287 / 1000000000000) (4745495311 / 1000000000000)
      | 6 => orderedInterval (-10353263531 / 1000000000000) (-10353263430 / 1000000000000)
      | 7 => orderedInterval (-5037626038 / 1000000000000) (-5037625951 / 1000000000000)
      | _ => orderedInterval (-22505825322 / 1000000000000) (-22505825197 / 1000000000000)
    | 3 =>
      match b.val with
      | 0 => orderedInterval (-6148345490 / 1000000000000) (-6148345467 / 1000000000000)
      | 1 => orderedInterval (-14706168854 / 1000000000000) (-14706168643 / 1000000000000)
      | 2 => orderedInterval (13008246123 / 1000000000000) (13008262398 / 1000000000000)
      | 3 => orderedInterval (-4457316005 / 1000000000000) (-4457315463 / 1000000000000)
      | 4 => orderedInterval (4910024905 / 1000000000000) (4910025494 / 1000000000000)
      | 5 => orderedInterval (11940267153 / 1000000000000) (11940267190 / 1000000000000)
      | 6 => orderedInterval (-9821175202 / 1000000000000) (-9821175125 / 1000000000000)
      | 7 => orderedInterval (-4355865345 / 1000000000000) (-4355865298 / 1000000000000)
      | _ => orderedInterval (-28609647717 / 1000000000000) (-28609647588 / 1000000000000)
    | _ =>
      match b.val with
      | 0 => orderedInterval (21516324124 / 1000000000000) (21516324147 / 1000000000000)
      | 1 => orderedInterval (-8953930432 / 1000000000000) (-8953930101 / 1000000000000)
      | 2 => orderedInterval (20503258194 / 1000000000000) (20503290520 / 1000000000000)
      | 3 => orderedInterval (19481991431 / 1000000000000) (19481992542 / 1000000000000)
      | 4 => orderedInterval (-13230254321 / 1000000000000) (-13230253134 / 1000000000000)
      | 5 => orderedInterval (-8491751406 / 1000000000000) (-8491751348 / 1000000000000)
      | 6 => orderedInterval (10258245850 / 1000000000000) (10258245913 / 1000000000000)
      | 7 => orderedInterval (6316845577 / 1000000000000) (6316845611 / 1000000000000)
      | _ => orderedInterval (63705027063 / 1000000000000) (63705027240 / 1000000000000)
  coefficientTarget := fun i =>
    match i.val with
    | 0 => orderedInterval (40138256217 / 1000000000000) (40138259733 / 1000000000000)
    | 1 => orderedInterval (29874956765 / 1000000000000) (29874961871 / 1000000000000)
    | 2 => orderedInterval (-54475197650 / 1000000000000) (-54475188341 / 1000000000000)
    | 3 => orderedInterval (-38239980432 / 1000000000000) (-38239962502 / 1000000000000)
    | _ => orderedInterval (111105756080 / 1000000000000) (111105791390 / 1000000000000)

theorem compactCertificate236_stateChecks0 :
    compactCertificate236.stateChecks 0 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 36 12 (227 / 2)) (orderedInterval (69443243969 / 1000000000000) (69443243970 / 1000000000000), orderedInterval (27740148711 / 1000000000000) (27740148712 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 27 12 (334414345173527 / 4000000000000)) (orderedInterval (36813521833 / 1000000000000) (36813524489 / 1000000000000), orderedInterval (-79337760205 / 1000000000000) (-79337757550 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 43 12 (108142728252791 / 800000000000)) (orderedInterval (-52646566276 / 1000000000000) (-52646566275 / 1000000000000), orderedInterval (-43825853429 / 1000000000000) (-43825853428 / 1000000000000))) = true
  norm_num [besselStateAtRationalPoint, besselIntervalStepZero,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, besselZeroTransition,
    besselInitial, besselGridStateAt, besselGridStateBlock00, besselGridStateBlock01,
    besselGridStateBlock02, besselGridStateBlock03, besselGridStateBlock04,
    besselGridStateBlock05, besselGridStateBlock06, besselGridStateBlock07,
    besselGridStateBlock08, besselGridStateBlock09, besselGridStateBlock10,
    besselGridStateBlock11, besselGridStateBlock12, besselGridStateBlock13,
    besselGridStateBlock14, besselGridState008, besselGridState011, besselGridState017, besselGridState020, besselGridState021, besselGridState027, besselGridState029, besselGridState031, besselGridState036, besselGridState037, besselGridState039, besselGridState042, besselGridState043, besselGridState045, besselGridState046, besselGridState047, besselGridState052, besselGridState053, besselGridState055, besselGridState057, besselGridState063, besselGridState067, besselGridState072, besselGridState077, besselGridState081, besselGridState083, besselStateSubset, linearInterval, widenInterval,
    rationalErrorInterval, rationalIntervalSubset, orderedInterval, Finset.sum_range_succ,
    IntervalRat.add, IntervalRat.mul, IntervalRat.scale, IntervalRat.singleton]

theorem compactCertificate236_stateChecks1 :
    compactCertificate236.stateChecks 3 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 8 12 (97581271880389 / 4000000000000)) (orderedInterval (6920130062 / 1000000000000) (6920130067 / 1000000000000), orderedInterval (161269317261 / 1000000000000) (161269317267 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 21 12 (262117022212033 / 4000000000000)) (orderedInterval (-32804665728 / 1000000000000) (-32804665727 / 1000000000000), orderedInterval (-92696578789 / 1000000000000) (-92696578788 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 57 12 (711698704328061 / 4000000000000)) (orderedInterval (21150705033 / 1000000000000) (21150705681 / 1000000000000), orderedInterval (-56011987879 / 1000000000000) (-56011987232 / 1000000000000))) = true
  norm_num [besselStateAtRationalPoint, besselIntervalStepZero,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, besselZeroTransition,
    besselInitial, besselGridStateAt, besselGridStateBlock00, besselGridStateBlock01,
    besselGridStateBlock02, besselGridStateBlock03, besselGridStateBlock04,
    besselGridStateBlock05, besselGridStateBlock06, besselGridStateBlock07,
    besselGridStateBlock08, besselGridStateBlock09, besselGridStateBlock10,
    besselGridStateBlock11, besselGridStateBlock12, besselGridStateBlock13,
    besselGridStateBlock14, besselGridState008, besselGridState011, besselGridState017, besselGridState020, besselGridState021, besselGridState027, besselGridState029, besselGridState031, besselGridState036, besselGridState037, besselGridState039, besselGridState042, besselGridState043, besselGridState045, besselGridState046, besselGridState047, besselGridState052, besselGridState053, besselGridState055, besselGridState057, besselGridState063, besselGridState067, besselGridState072, besselGridState077, besselGridState081, besselGridState083, besselStateSubset, linearInterval, widenInterval,
    rationalErrorInterval, rationalIntervalSubset, orderedInterval, Finset.sum_range_succ,
    IntervalRat.add, IntervalRat.mul, IntervalRat.scale, IntervalRat.singleton]

theorem compactCertificate236_stateChecks2 :
    compactCertificate236.stateChecks 6 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 42 12 (524234044424293 / 4000000000000)) (orderedInterval (-7230849902 / 1000000000000) (-7230849876 / 1000000000000), orderedInterval (69347660248 / 1000000000000) (69347660274 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 72 12 (898283970404089 / 4000000000000)) (orderedInterval (-39605721440 / 1000000000000) (-39605653872 / 1000000000000), orderedInterval (35672060622 / 1000000000000) (35672128190 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 53 12 (661671906921451 / 4000000000000)) (orderedInterval (18439196152 / 1000000000000) (18439196483 / 1000000000000), orderedInterval (-59288859328 / 1000000000000) (-59288858997 / 1000000000000))) = true
  norm_num [besselStateAtRationalPoint, besselIntervalStepZero,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, besselZeroTransition,
    besselInitial, besselGridStateAt, besselGridStateBlock00, besselGridStateBlock01,
    besselGridStateBlock02, besselGridStateBlock03, besselGridStateBlock04,
    besselGridStateBlock05, besselGridStateBlock06, besselGridStateBlock07,
    besselGridStateBlock08, besselGridStateBlock09, besselGridStateBlock10,
    besselGridStateBlock11, besselGridStateBlock12, besselGridStateBlock13,
    besselGridStateBlock14, besselGridState008, besselGridState011, besselGridState017, besselGridState020, besselGridState021, besselGridState027, besselGridState029, besselGridState031, besselGridState036, besselGridState037, besselGridState039, besselGridState042, besselGridState043, besselGridState045, besselGridState046, besselGridState047, besselGridState052, besselGridState053, besselGridState055, besselGridState057, besselGridState063, besselGridState067, besselGridState072, besselGridState077, besselGridState081, besselGridState083, besselStateSubset, linearInterval, widenInterval,
    rationalErrorInterval, rationalIntervalSubset, orderedInterval, Finset.sum_range_succ,
    IntervalRat.add, IntervalRat.mul, IntervalRat.scale, IntervalRat.singleton]

theorem compactCertificate236_stateChecks3 :
    compactCertificate236.stateChecks 9 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 81 12 (1015174861784773 / 4000000000000)) (orderedInterval (-5479029846 / 1000000000000) (-5479029845 / 1000000000000), orderedInterval (-49772729496 / 1000000000000) (-49772729495 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 47 12 (586111479725917 / 4000000000000)) (orderedInterval (22133057544 / 1000000000000) (22133058166 / 1000000000000), orderedInterval (-62162948875 / 1000000000000) (-62162948253 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 83 12 (1040065106047553 / 4000000000000)) (orderedInterval (-2423786505 / 1000000000000) (-2423786504 / 1000000000000), orderedInterval (-49417136764 / 1000000000000) (-49417136763 / 1000000000000))) = true
  norm_num [besselStateAtRationalPoint, besselIntervalStepZero,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, besselZeroTransition,
    besselInitial, besselGridStateAt, besselGridStateBlock00, besselGridStateBlock01,
    besselGridStateBlock02, besselGridStateBlock03, besselGridStateBlock04,
    besselGridStateBlock05, besselGridStateBlock06, besselGridStateBlock07,
    besselGridStateBlock08, besselGridStateBlock09, besselGridStateBlock10,
    besselGridStateBlock11, besselGridStateBlock12, besselGridStateBlock13,
    besselGridStateBlock14, besselGridState008, besselGridState011, besselGridState017, besselGridState020, besselGridState021, besselGridState027, besselGridState029, besselGridState031, besselGridState036, besselGridState037, besselGridState039, besselGridState042, besselGridState043, besselGridState045, besselGridState046, besselGridState047, besselGridState052, besselGridState053, besselGridState055, besselGridState057, besselGridState063, besselGridState067, besselGridState072, besselGridState077, besselGridState081, besselGridState083, besselStateSubset, linearInterval, widenInterval,
    rationalErrorInterval, rationalIntervalSubset, orderedInterval, Finset.sum_range_succ,
    IntervalRat.add, IntervalRat.mul, IntervalRat.scale, IntervalRat.singleton]

theorem compactCertificate236_stateChecks4 :
    compactCertificate236.stateChecks 12 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 77 12 (971763735766757 / 4000000000000)) (orderedInterval (-49568727831 / 1000000000000) (-49568725595 / 1000000000000), orderedInterval (12885125760 / 1000000000000) (12885127996 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 55 12 (693496455169781 / 4000000000000)) (orderedInterval (-59393329990 / 1000000000000) (-59393329987 / 1000000000000), orderedInterval (-11843737016 / 1000000000000) (-11843737013 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 63 12 (786351066636099 / 4000000000000)) (orderedInterval (29637841273 / 1000000000000) (29637846124 / 1000000000000), orderedInterval (-48654718463 / 1000000000000) (-48654713612 / 1000000000000))) = true
  norm_num [besselStateAtRationalPoint, besselIntervalStepZero,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, besselZeroTransition,
    besselInitial, besselGridStateAt, besselGridStateBlock00, besselGridStateBlock01,
    besselGridStateBlock02, besselGridStateBlock03, besselGridStateBlock04,
    besselGridStateBlock05, besselGridStateBlock06, besselGridStateBlock07,
    besselGridStateBlock08, besselGridStateBlock09, besselGridStateBlock10,
    besselGridStateBlock11, besselGridStateBlock12, besselGridStateBlock13,
    besselGridStateBlock14, besselGridState008, besselGridState011, besselGridState017, besselGridState020, besselGridState021, besselGridState027, besselGridState029, besselGridState031, besselGridState036, besselGridState037, besselGridState039, besselGridState042, besselGridState043, besselGridState045, besselGridState046, besselGridState047, besselGridState052, besselGridState053, besselGridState055, besselGridState057, besselGridState063, besselGridState067, besselGridState072, besselGridState077, besselGridState081, besselGridState083, besselStateSubset, linearInterval, widenInterval,
    rationalErrorInterval, rationalIntervalSubset, orderedInterval, Finset.sum_range_succ,
    IntervalRat.add, IntervalRat.mul, IntervalRat.scale, IntervalRat.singleton]

theorem compactCertificate236_stateChecks5 :
    compactCertificate236.stateChecks 15 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 52 12 (655577538141331 / 4000000000000)) (orderedInterval (60315255922 / 1000000000000) (60315255923 / 1000000000000), orderedInterval (15512603055 / 1000000000000) (15512603056 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 46 12 (579222636619951 / 4000000000000)) (orderedInterval (58382021871 / 1000000000000) (58382021872 / 1000000000000), orderedInterval (31229270146 / 1000000000000) (31229270147 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 67 12 (167881296379149 / 800000000000)) (orderedInterval (-8215339623 / 1000000000000) (-8215339622 / 1000000000000), orderedInterval (-54443097964 / 1000000000000) (-54443097963 / 1000000000000))) = true
  norm_num [besselStateAtRationalPoint, besselIntervalStepZero,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, besselZeroTransition,
    besselInitial, besselGridStateAt, besselGridStateBlock00, besselGridStateBlock01,
    besselGridStateBlock02, besselGridStateBlock03, besselGridStateBlock04,
    besselGridStateBlock05, besselGridStateBlock06, besselGridStateBlock07,
    besselGridStateBlock08, besselGridStateBlock09, besselGridStateBlock10,
    besselGridStateBlock11, besselGridStateBlock12, besselGridStateBlock13,
    besselGridStateBlock14, besselGridState008, besselGridState011, besselGridState017, besselGridState020, besselGridState021, besselGridState027, besselGridState029, besselGridState031, besselGridState036, besselGridState037, besselGridState039, besselGridState042, besselGridState043, besselGridState045, besselGridState046, besselGridState047, besselGridState052, besselGridState053, besselGridState055, besselGridState057, besselGridState063, besselGridState067, besselGridState072, besselGridState077, besselGridState081, besselGridState083, besselStateSubset, linearInterval, widenInterval,
    rationalErrorInterval, rationalIntervalSubset, orderedInterval, Finset.sum_range_succ,
    IntervalRat.add, IntervalRat.mul, IntervalRat.scale, IntervalRat.singleton]

theorem compactCertificate236_stateChecks6 :
    compactCertificate236.stateChecks 18 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 37 12 (464368500893303 / 4000000000000)) (orderedInterval (-44075975785 / 1000000000000) (-44075975784 / 1000000000000), orderedInterval (-59317058366 / 1000000000000) (-59317058365 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 31 12 (393650320947583 / 4000000000000)) (orderedInterval (-78189299398 / 1000000000000) (-78189298598 / 1000000000000), orderedInterval (19245194325 / 1000000000000) (19245195124 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 20 12 (246328093078549 / 4000000000000)) (orderedInterval (-45725263285 / 1000000000000) (-45725259114 / 1000000000000), orderedInterval (91185085872 / 1000000000000) (91185090042 / 1000000000000))) = true
  norm_num [besselStateAtRationalPoint, besselIntervalStepZero,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, besselZeroTransition,
    besselInitial, besselGridStateAt, besselGridStateBlock00, besselGridStateBlock01,
    besselGridStateBlock02, besselGridStateBlock03, besselGridStateBlock04,
    besselGridStateBlock05, besselGridStateBlock06, besselGridStateBlock07,
    besselGridStateBlock08, besselGridStateBlock09, besselGridStateBlock10,
    besselGridStateBlock11, besselGridStateBlock12, besselGridStateBlock13,
    besselGridStateBlock14, besselGridState008, besselGridState011, besselGridState017, besselGridState020, besselGridState021, besselGridState027, besselGridState029, besselGridState031, besselGridState036, besselGridState037, besselGridState039, besselGridState042, besselGridState043, besselGridState045, besselGridState046, besselGridState047, besselGridState052, besselGridState053, besselGridState055, besselGridState057, besselGridState063, besselGridState067, besselGridState072, besselGridState077, besselGridState081, besselGridState083, besselStateSubset, linearInterval, widenInterval,
    rationalErrorInterval, rationalIntervalSubset, orderedInterval, Finset.sum_range_succ,
    IntervalRat.add, IntervalRat.mul, IntervalRat.scale, IntervalRat.singleton]

theorem compactCertificate236_stateChecks7 :
    compactCertificate236.stateChecks 21 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 11 12 (132476067707883 / 4000000000000)) (orderedInterval (84657675308 / 1000000000000) (84657706240 / 1000000000000), orderedInterval (-111076774414 / 1000000000000) (-111076743481 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 29 12 (359698294092649 / 4000000000000)) (orderedInterval (32579599987 / 1000000000000) (32579601663 / 1000000000000), orderedInterval (-77757767278 / 1000000000000) (-77757765603 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 39 12 (491137269030473 / 4000000000000)) (orderedInterval (-62336651863 / 1000000000000) (-62336651862 / 1000000000000), orderedInterval (-35787559889 / 1000000000000) (-35787559888 / 1000000000000))) = true
  norm_num [besselStateAtRationalPoint, besselIntervalStepZero,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, besselZeroTransition,
    besselInitial, besselGridStateAt, besselGridStateBlock00, besselGridStateBlock01,
    besselGridStateBlock02, besselGridStateBlock03, besselGridStateBlock04,
    besselGridStateBlock05, besselGridStateBlock06, besselGridStateBlock07,
    besselGridStateBlock08, besselGridStateBlock09, besselGridStateBlock10,
    besselGridStateBlock11, besselGridStateBlock12, besselGridStateBlock13,
    besselGridStateBlock14, besselGridState008, besselGridState011, besselGridState017, besselGridState020, besselGridState021, besselGridState027, besselGridState029, besselGridState031, besselGridState036, besselGridState037, besselGridState039, besselGridState042, besselGridState043, besselGridState045, besselGridState046, besselGridState047, besselGridState052, besselGridState053, besselGridState055, besselGridState057, besselGridState063, besselGridState067, besselGridState072, besselGridState077, besselGridState081, besselGridState083, besselStateSubset, linearInterval, widenInterval,
    rationalErrorInterval, rationalIntervalSubset, orderedInterval, Finset.sum_range_succ,
    IntervalRat.add, IntervalRat.mul, IntervalRat.scale, IntervalRat.singleton]

theorem compactCertificate236_stateChecks8 :
    compactCertificate236.stateChecks 24 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 17 12 (207671906921451 / 4000000000000)) (orderedInterval (71851070681 / 1000000000000) (71851115469 / 1000000000000), orderedInterval (-84950689888 / 1000000000000) (-84950645099 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 67 12 (844174772036171 / 4000000000000)) (orderedInterval (-53488986952 / 1000000000000) (-53488986950 / 1000000000000), orderedInterval (-12341288892 / 1000000000000) (-12341288890 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 45 12 (563869625230789 / 4000000000000)) (orderedInterval (-24941931769 / 1000000000000) (-24941931768 / 1000000000000), orderedInterval (-62313444376 / 1000000000000) (-62313444375 / 1000000000000))) = true
  norm_num [besselStateAtRationalPoint, besselIntervalStepZero,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, besselZeroTransition,
    besselInitial, besselGridStateAt, besselGridStateBlock00, besselGridStateBlock01,
    besselGridStateBlock02, besselGridStateBlock03, besselGridStateBlock04,
    besselGridStateBlock05, besselGridStateBlock06, besselGridStateBlock07,
    besselGridStateBlock08, besselGridStateBlock09, besselGridStateBlock10,
    besselGridStateBlock11, besselGridStateBlock12, besselGridStateBlock13,
    besselGridStateBlock14, besselGridState008, besselGridState011, besselGridState017, besselGridState020, besselGridState021, besselGridState027, besselGridState029, besselGridState031, besselGridState036, besselGridState037, besselGridState039, besselGridState042, besselGridState043, besselGridState045, besselGridState046, besselGridState047, besselGridState052, besselGridState053, besselGridState055, besselGridState057, besselGridState063, besselGridState067, besselGridState072, besselGridState077, besselGridState081, besselGridState083, besselStateSubset, linearInterval, widenInterval,
    rationalErrorInterval, rationalIntervalSubset, orderedInterval, Finset.sum_range_succ,
    IntervalRat.add, IntervalRat.mul, IntervalRat.scale, IntervalRat.singleton]

theorem compactCertificate236_states : ∀ j,
    BesselStateValid (compactCertificate236.point j) (compactCertificate236.state j) :=
  compactCertificate236.statesValid_of_checks3 compactCertificate236_stateChecks0
    compactCertificate236_stateChecks1 compactCertificate236_stateChecks2
    compactCertificate236_stateChecks3 compactCertificate236_stateChecks4
    compactCertificate236_stateChecks5 compactCertificate236_stateChecks6
    compactCertificate236_stateChecks7 compactCertificate236_stateChecks8

theorem compactCertificate236_chunkChecks0_0 :
    compactCertificate236.chunkChecks (0 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 0) <| besselDerivativeNearFromState (227 / 2) 0 (IntervalRat.scale (227 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (69443243969 / 1000000000000) (69443243970 / 1000000000000), orderedInterval (27740148711 / 1000000000000) (27740148712 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 0) <| besselDerivativeNearFromState (334414345173527 / 4000000000000) 0 (IntervalRat.scale (227 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (36813521833 / 1000000000000) (36813524489 / 1000000000000), orderedInterval (-79337760205 / 1000000000000) (-79337757550 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 0) <| besselDerivativeNearFromState (108142728252791 / 800000000000) 0 (IntervalRat.scale (227 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-52646566276 / 1000000000000) (-52646566275 / 1000000000000), orderedInterval (-43825853429 / 1000000000000) (-43825853428 / 1000000000000)))) (orderedInterval (24778540984 / 1000000000000) (24778541018 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 0) <| besselDerivativeNearFromState (97581271880389 / 4000000000000) 0 (IntervalRat.scale (227 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (6920130062 / 1000000000000) (6920130067 / 1000000000000), orderedInterval (161269317261 / 1000000000000) (161269317267 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 0) <| besselDerivativeNearFromState (262117022212033 / 4000000000000) 0 (IntervalRat.scale (227 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-32804665728 / 1000000000000) (-32804665727 / 1000000000000), orderedInterval (-92696578789 / 1000000000000) (-92696578788 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 0) <| besselDerivativeNearFromState (711698704328061 / 4000000000000) 0 (IntervalRat.scale (227 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (21150705033 / 1000000000000) (21150705681 / 1000000000000), orderedInterval (-56011987879 / 1000000000000) (-56011987232 / 1000000000000)))) (orderedInterval (-2776430209 / 1000000000000) (-2776430148 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 0) <| besselDerivativeNearFromState (524234044424293 / 4000000000000) 0 (IntervalRat.scale (227 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-7230849902 / 1000000000000) (-7230849876 / 1000000000000), orderedInterval (69347660248 / 1000000000000) (69347660274 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 0) <| besselDerivativeNearFromState (898283970404089 / 4000000000000) 0 (IntervalRat.scale (227 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-39605721440 / 1000000000000) (-39605653872 / 1000000000000), orderedInterval (35672060622 / 1000000000000) (35672128190 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 0) <| besselDerivativeNearFromState (661671906921451 / 4000000000000) 0 (IntervalRat.scale (227 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (18439196152 / 1000000000000) (18439196483 / 1000000000000), orderedInterval (-59288859328 / 1000000000000) (-59288858997 / 1000000000000)))) (orderedInterval (1667235814 / 1000000000000) (1667237914 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate236_chunkChecks0_1 :
    compactCertificate236.chunkChecks (0 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 0) <| besselDerivativeNearFromState (1015174861784773 / 4000000000000) 0 (IntervalRat.scale (227 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-5479029846 / 1000000000000) (-5479029845 / 1000000000000), orderedInterval (-49772729496 / 1000000000000) (-49772729495 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 0) <| besselDerivativeNearFromState (586111479725917 / 4000000000000) 0 (IntervalRat.scale (227 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (22133057544 / 1000000000000) (22133058166 / 1000000000000), orderedInterval (-62162948875 / 1000000000000) (-62162948253 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 0) <| besselDerivativeNearFromState (1040065106047553 / 4000000000000) 0 (IntervalRat.scale (227 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-2423786505 / 1000000000000) (-2423786504 / 1000000000000), orderedInterval (-49417136764 / 1000000000000) (-49417136763 / 1000000000000)))) (orderedInterval (2268879325 / 1000000000000) (2268879417 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 0) <| besselDerivativeNearFromState (971763735766757 / 4000000000000) 0 (IntervalRat.scale (227 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-49568727831 / 1000000000000) (-49568725595 / 1000000000000), orderedInterval (12885125760 / 1000000000000) (12885127996 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 0) <| besselDerivativeNearFromState (693496455169781 / 4000000000000) 0 (IntervalRat.scale (227 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-59393329990 / 1000000000000) (-59393329987 / 1000000000000), orderedInterval (-11843737016 / 1000000000000) (-11843737013 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 0) <| besselDerivativeNearFromState (786351066636099 / 4000000000000) 0 (IntervalRat.scale (227 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (29637841273 / 1000000000000) (29637846124 / 1000000000000), orderedInterval (-48654718463 / 1000000000000) (-48654713612 / 1000000000000)))) (orderedInterval (-4871519619 / 1000000000000) (-4871519539 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 0) <| besselDerivativeNearFromState (655577538141331 / 4000000000000) 0 (IntervalRat.scale (227 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (60315255922 / 1000000000000) (60315255923 / 1000000000000), orderedInterval (15512603055 / 1000000000000) (15512603056 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 0) <| besselDerivativeNearFromState (579222636619951 / 4000000000000) 0 (IntervalRat.scale (227 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (58382021871 / 1000000000000) (58382021872 / 1000000000000), orderedInterval (31229270146 / 1000000000000) (31229270147 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 0) <| besselDerivativeNearFromState (167881296379149 / 800000000000) 0 (IntervalRat.scale (227 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-8215339623 / 1000000000000) (-8215339622 / 1000000000000), orderedInterval (-54443097964 / 1000000000000) (-54443097963 / 1000000000000)))) (orderedInterval (-2854853588 / 1000000000000) (-2854853576 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate236_chunkChecks0_2 :
    compactCertificate236.chunkChecks (0 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 0) <| besselDerivativeNearFromState (464368500893303 / 4000000000000) 0 (IntervalRat.scale (227 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-44075975785 / 1000000000000) (-44075975784 / 1000000000000), orderedInterval (-59317058366 / 1000000000000) (-59317058365 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 0) <| besselDerivativeNearFromState (393650320947583 / 4000000000000) 0 (IntervalRat.scale (227 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-78189299398 / 1000000000000) (-78189298598 / 1000000000000), orderedInterval (19245194325 / 1000000000000) (19245195124 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 0) <| besselDerivativeNearFromState (246328093078549 / 4000000000000) 0 (IntervalRat.scale (227 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-45725263285 / 1000000000000) (-45725259114 / 1000000000000), orderedInterval (91185085872 / 1000000000000) (91185090042 / 1000000000000)))) (orderedInterval (9984327910 / 1000000000000) (9984328120 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 0) <| besselDerivativeNearFromState (132476067707883 / 4000000000000) 0 (IntervalRat.scale (227 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (84657675308 / 1000000000000) (84657706240 / 1000000000000), orderedInterval (-111076774414 / 1000000000000) (-111076743481 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 0) <| besselDerivativeNearFromState (359698294092649 / 4000000000000) 0 (IntervalRat.scale (227 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (32579599987 / 1000000000000) (32579601663 / 1000000000000), orderedInterval (-77757767278 / 1000000000000) (-77757765603 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 0) <| besselDerivativeNearFromState (491137269030473 / 4000000000000) 0 (IntervalRat.scale (227 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-62336651863 / 1000000000000) (-62336651862 / 1000000000000), orderedInterval (-35787559889 / 1000000000000) (-35787559888 / 1000000000000)))) (orderedInterval (2475067173 / 1000000000000) (2475067797 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 0) <| besselDerivativeNearFromState (207671906921451 / 4000000000000) 0 (IntervalRat.scale (227 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (71851070681 / 1000000000000) (71851115469 / 1000000000000), orderedInterval (-84950689888 / 1000000000000) (-84950645099 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 0) <| besselDerivativeNearFromState (844174772036171 / 4000000000000) 0 (IntervalRat.scale (227 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-53488986952 / 1000000000000) (-53488986950 / 1000000000000), orderedInterval (-12341288892 / 1000000000000) (-12341288890 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 0) <| besselDerivativeNearFromState (563869625230789 / 4000000000000) 0 (IntervalRat.scale (227 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-24941931769 / 1000000000000) (-24941931768 / 1000000000000), orderedInterval (-62313444376 / 1000000000000) (-62313444375 / 1000000000000)))) (orderedInterval (9467008427 / 1000000000000) (9467008730 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate236_chunkChecks0 :
    compactCertificate236.chunkChecks (0 : Fin 5) 0 9 = true :=
  compactCertificate236.chunkChecks_nine_of_three (0 : Fin 5) compactCertificate236_chunkChecks0_0
    compactCertificate236_chunkChecks0_1 compactCertificate236_chunkChecks0_2

theorem compactCertificate236_chunkChecks1_0 :
    compactCertificate236.chunkChecks (1 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 1) <| besselDerivativeNearFromState (227 / 2) 1 (IntervalRat.scale (227 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (69443243969 / 1000000000000) (69443243970 / 1000000000000), orderedInterval (27740148711 / 1000000000000) (27740148712 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 1) <| besselDerivativeNearFromState (334414345173527 / 4000000000000) 1 (IntervalRat.scale (227 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (36813521833 / 1000000000000) (36813524489 / 1000000000000), orderedInterval (-79337760205 / 1000000000000) (-79337757550 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 1) <| besselDerivativeNearFromState (108142728252791 / 800000000000) 1 (IntervalRat.scale (227 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-52646566276 / 1000000000000) (-52646566275 / 1000000000000), orderedInterval (-43825853429 / 1000000000000) (-43825853428 / 1000000000000)))) (orderedInterval (7387724498 / 1000000000000) (7387724526 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 1) <| besselDerivativeNearFromState (97581271880389 / 4000000000000) 1 (IntervalRat.scale (227 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (6920130062 / 1000000000000) (6920130067 / 1000000000000), orderedInterval (161269317261 / 1000000000000) (161269317267 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 1) <| besselDerivativeNearFromState (262117022212033 / 4000000000000) 1 (IntervalRat.scale (227 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-32804665728 / 1000000000000) (-32804665727 / 1000000000000), orderedInterval (-92696578789 / 1000000000000) (-92696578788 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 1) <| besselDerivativeNearFromState (711698704328061 / 4000000000000) 1 (IntervalRat.scale (227 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (21150705033 / 1000000000000) (21150705681 / 1000000000000), orderedInterval (-56011987879 / 1000000000000) (-56011987232 / 1000000000000)))) (orderedInterval (3911939737 / 1000000000000) (3911939826 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 1) <| besselDerivativeNearFromState (524234044424293 / 4000000000000) 1 (IntervalRat.scale (227 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-7230849902 / 1000000000000) (-7230849876 / 1000000000000), orderedInterval (69347660248 / 1000000000000) (69347660274 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 1) <| besselDerivativeNearFromState (898283970404089 / 4000000000000) 1 (IntervalRat.scale (227 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-39605721440 / 1000000000000) (-39605653872 / 1000000000000), orderedInterval (35672060622 / 1000000000000) (35672128190 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 1) <| besselDerivativeNearFromState (661671906921451 / 4000000000000) 1 (IntervalRat.scale (227 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (18439196152 / 1000000000000) (18439196483 / 1000000000000), orderedInterval (-59288859328 / 1000000000000) (-59288858997 / 1000000000000)))) (orderedInterval (-4265335133 / 1000000000000) (-4265330986 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate236_chunkChecks1_1 :
    compactCertificate236.chunkChecks (1 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 1) <| besselDerivativeNearFromState (1015174861784773 / 4000000000000) 1 (IntervalRat.scale (227 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-5479029846 / 1000000000000) (-5479029845 / 1000000000000), orderedInterval (-49772729496 / 1000000000000) (-49772729495 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 1) <| besselDerivativeNearFromState (586111479725917 / 4000000000000) 1 (IntervalRat.scale (227 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (22133057544 / 1000000000000) (22133058166 / 1000000000000), orderedInterval (-62162948875 / 1000000000000) (-62162948253 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 1) <| besselDerivativeNearFromState (1040065106047553 / 4000000000000) 1 (IntervalRat.scale (227 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-2423786505 / 1000000000000) (-2423786504 / 1000000000000), orderedInterval (-49417136764 / 1000000000000) (-49417136763 / 1000000000000)))) (orderedInterval (-2263574516 / 1000000000000) (-2263574362 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 1) <| besselDerivativeNearFromState (971763735766757 / 4000000000000) 1 (IntervalRat.scale (227 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-49568727831 / 1000000000000) (-49568725595 / 1000000000000), orderedInterval (12885125760 / 1000000000000) (12885127996 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 1) <| besselDerivativeNearFromState (693496455169781 / 4000000000000) 1 (IntervalRat.scale (227 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-59393329990 / 1000000000000) (-59393329987 / 1000000000000), orderedInterval (-11843737016 / 1000000000000) (-11843737013 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 1) <| besselDerivativeNearFromState (786351066636099 / 4000000000000) 1 (IntervalRat.scale (227 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (29637841273 / 1000000000000) (29637846124 / 1000000000000), orderedInterval (-48654718463 / 1000000000000) (-48654713612 / 1000000000000)))) (orderedInterval (-1782230486 / 1000000000000) (-1782230334 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 1) <| besselDerivativeNearFromState (655577538141331 / 4000000000000) 1 (IntervalRat.scale (227 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (60315255922 / 1000000000000) (60315255923 / 1000000000000), orderedInterval (15512603055 / 1000000000000) (15512603056 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 1) <| besselDerivativeNearFromState (579222636619951 / 4000000000000) 1 (IntervalRat.scale (227 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (58382021871 / 1000000000000) (58382021872 / 1000000000000), orderedInterval (31229270146 / 1000000000000) (31229270147 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 1) <| besselDerivativeNearFromState (167881296379149 / 800000000000) 1 (IntervalRat.scale (227 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-8215339623 / 1000000000000) (-8215339622 / 1000000000000), orderedInterval (-54443097964 / 1000000000000) (-54443097963 / 1000000000000)))) (orderedInterval (-4598716709 / 1000000000000) (-4598716692 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate236_chunkChecks1_2 :
    compactCertificate236.chunkChecks (1 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 1) <| besselDerivativeNearFromState (464368500893303 / 4000000000000) 1 (IntervalRat.scale (227 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-44075975785 / 1000000000000) (-44075975784 / 1000000000000), orderedInterval (-59317058366 / 1000000000000) (-59317058365 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 1) <| besselDerivativeNearFromState (393650320947583 / 4000000000000) 1 (IntervalRat.scale (227 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-78189299398 / 1000000000000) (-78189298598 / 1000000000000), orderedInterval (19245194325 / 1000000000000) (19245195124 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 1) <| besselDerivativeNearFromState (246328093078549 / 4000000000000) 1 (IntervalRat.scale (227 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-45725263285 / 1000000000000) (-45725259114 / 1000000000000), orderedInterval (91185085872 / 1000000000000) (91185090042 / 1000000000000)))) (orderedInterval (10367130585 / 1000000000000) (10367130725 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 1) <| besselDerivativeNearFromState (132476067707883 / 4000000000000) 1 (IntervalRat.scale (227 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (84657675308 / 1000000000000) (84657706240 / 1000000000000), orderedInterval (-111076774414 / 1000000000000) (-111076743481 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 1) <| besselDerivativeNearFromState (359698294092649 / 4000000000000) 1 (IntervalRat.scale (227 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (32579599987 / 1000000000000) (32579601663 / 1000000000000), orderedInterval (-77757767278 / 1000000000000) (-77757765603 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 1) <| besselDerivativeNearFromState (491137269030473 / 4000000000000) 1 (IntervalRat.scale (227 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-62336651863 / 1000000000000) (-62336651862 / 1000000000000), orderedInterval (-35787559889 / 1000000000000) (-35787559888 / 1000000000000)))) (orderedInterval (4963220136 / 1000000000000) (4963220346 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 1) <| besselDerivativeNearFromState (207671906921451 / 4000000000000) 1 (IntervalRat.scale (227 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (71851070681 / 1000000000000) (71851115469 / 1000000000000), orderedInterval (-84950689888 / 1000000000000) (-84950645099 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 1) <| besselDerivativeNearFromState (844174772036171 / 4000000000000) 1 (IntervalRat.scale (227 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-53488986952 / 1000000000000) (-53488986950 / 1000000000000), orderedInterval (-12341288892 / 1000000000000) (-12341288890 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 1) <| besselDerivativeNearFromState (563869625230789 / 4000000000000) 1 (IntervalRat.scale (227 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-24941931769 / 1000000000000) (-24941931768 / 1000000000000), orderedInterval (-62313444376 / 1000000000000) (-62313444375 / 1000000000000)))) (orderedInterval (16154798653 / 1000000000000) (16154798822 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate236_chunkChecks1 :
    compactCertificate236.chunkChecks (1 : Fin 5) 0 9 = true :=
  compactCertificate236.chunkChecks_nine_of_three (1 : Fin 5) compactCertificate236_chunkChecks1_0
    compactCertificate236_chunkChecks1_1 compactCertificate236_chunkChecks1_2

theorem compactCertificate236_chunkChecks2_0 :
    compactCertificate236.chunkChecks (2 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 2) <| besselDerivativeNearFromState (227 / 2) 2 (IntervalRat.scale (227 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (69443243969 / 1000000000000) (69443243970 / 1000000000000), orderedInterval (27740148711 / 1000000000000) (27740148712 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 2) <| besselDerivativeNearFromState (334414345173527 / 4000000000000) 2 (IntervalRat.scale (227 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (36813521833 / 1000000000000) (36813524489 / 1000000000000), orderedInterval (-79337760205 / 1000000000000) (-79337757550 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 2) <| besselDerivativeNearFromState (108142728252791 / 800000000000) 2 (IntervalRat.scale (227 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-52646566276 / 1000000000000) (-52646566275 / 1000000000000), orderedInterval (-43825853429 / 1000000000000) (-43825853428 / 1000000000000)))) (orderedInterval (-23393886727 / 1000000000000) (-23393886702 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 2) <| besselDerivativeNearFromState (97581271880389 / 4000000000000) 2 (IntervalRat.scale (227 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (6920130062 / 1000000000000) (6920130067 / 1000000000000), orderedInterval (161269317261 / 1000000000000) (161269317267 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 2) <| besselDerivativeNearFromState (262117022212033 / 4000000000000) 2 (IntervalRat.scale (227 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-32804665728 / 1000000000000) (-32804665727 / 1000000000000), orderedInterval (-92696578789 / 1000000000000) (-92696578788 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 2) <| besselDerivativeNearFromState (711698704328061 / 4000000000000) 2 (IntervalRat.scale (227 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (21150705033 / 1000000000000) (21150705681 / 1000000000000), orderedInterval (-56011987879 / 1000000000000) (-56011987232 / 1000000000000)))) (orderedInterval (4063231532 / 1000000000000) (4063231668 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 2) <| besselDerivativeNearFromState (524234044424293 / 4000000000000) 2 (IntervalRat.scale (227 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-7230849902 / 1000000000000) (-7230849876 / 1000000000000), orderedInterval (69347660248 / 1000000000000) (69347660274 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 2) <| besselDerivativeNearFromState (898283970404089 / 4000000000000) 2 (IntervalRat.scale (227 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-39605721440 / 1000000000000) (-39605653872 / 1000000000000), orderedInterval (35672060622 / 1000000000000) (35672128190 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 2) <| besselDerivativeNearFromState (661671906921451 / 4000000000000) 2 (IntervalRat.scale (227 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (18439196152 / 1000000000000) (18439196483 / 1000000000000), orderedInterval (-59288859328 / 1000000000000) (-59288858997 / 1000000000000)))) (orderedInterval (-5691380673 / 1000000000000) (-5691372440 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate236_chunkChecks2_1 :
    compactCertificate236.chunkChecks (2 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 2) <| besselDerivativeNearFromState (1015174861784773 / 4000000000000) 2 (IntervalRat.scale (227 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-5479029846 / 1000000000000) (-5479029845 / 1000000000000), orderedInterval (-49772729496 / 1000000000000) (-49772729495 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 2) <| besselDerivativeNearFromState (586111479725917 / 4000000000000) 2 (IntervalRat.scale (227 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (22133057544 / 1000000000000) (22133058166 / 1000000000000), orderedInterval (-62162948875 / 1000000000000) (-62162948253 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 2) <| besselDerivativeNearFromState (1040065106047553 / 4000000000000) 2 (IntervalRat.scale (227 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-2423786505 / 1000000000000) (-2423786504 / 1000000000000), orderedInterval (-49417136764 / 1000000000000) (-49417136763 / 1000000000000)))) (orderedInterval (-5772681036 / 1000000000000) (-5772680756 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 2) <| besselDerivativeNearFromState (971763735766757 / 4000000000000) 2 (IntervalRat.scale (227 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-49568727831 / 1000000000000) (-49568725595 / 1000000000000), orderedInterval (12885125760 / 1000000000000) (12885127996 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 2) <| besselDerivativeNearFromState (693496455169781 / 4000000000000) 2 (IntervalRat.scale (227 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-59393329990 / 1000000000000) (-59393329987 / 1000000000000), orderedInterval (-11843737016 / 1000000000000) (-11843737013 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 2) <| besselDerivativeNearFromState (786351066636099 / 4000000000000) 2 (IntervalRat.scale (227 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (29637841273 / 1000000000000) (29637846124 / 1000000000000), orderedInterval (-48654718463 / 1000000000000) (-48654713612 / 1000000000000)))) (orderedInterval (9470738858 / 1000000000000) (9470739156 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 2) <| besselDerivativeNearFromState (655577538141331 / 4000000000000) 2 (IntervalRat.scale (227 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (60315255922 / 1000000000000) (60315255923 / 1000000000000), orderedInterval (15512603055 / 1000000000000) (15512603056 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 2) <| besselDerivativeNearFromState (579222636619951 / 4000000000000) 2 (IntervalRat.scale (227 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (58382021871 / 1000000000000) (58382021872 / 1000000000000), orderedInterval (31229270146 / 1000000000000) (31229270147 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 2) <| besselDerivativeNearFromState (167881296379149 / 800000000000) 2 (IntervalRat.scale (227 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-8215339623 / 1000000000000) (-8215339622 / 1000000000000), orderedInterval (-54443097964 / 1000000000000) (-54443097963 / 1000000000000)))) (orderedInterval (4745495287 / 1000000000000) (4745495311 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate236_chunkChecks2_2 :
    compactCertificate236.chunkChecks (2 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 2) <| besselDerivativeNearFromState (464368500893303 / 4000000000000) 2 (IntervalRat.scale (227 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-44075975785 / 1000000000000) (-44075975784 / 1000000000000), orderedInterval (-59317058366 / 1000000000000) (-59317058365 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 2) <| besselDerivativeNearFromState (393650320947583 / 4000000000000) 2 (IntervalRat.scale (227 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-78189299398 / 1000000000000) (-78189298598 / 1000000000000), orderedInterval (19245194325 / 1000000000000) (19245195124 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 2) <| besselDerivativeNearFromState (246328093078549 / 4000000000000) 2 (IntervalRat.scale (227 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-45725263285 / 1000000000000) (-45725259114 / 1000000000000), orderedInterval (91185085872 / 1000000000000) (91185090042 / 1000000000000)))) (orderedInterval (-10353263531 / 1000000000000) (-10353263430 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 2) <| besselDerivativeNearFromState (132476067707883 / 4000000000000) 2 (IntervalRat.scale (227 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (84657675308 / 1000000000000) (84657706240 / 1000000000000), orderedInterval (-111076774414 / 1000000000000) (-111076743481 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 2) <| besselDerivativeNearFromState (359698294092649 / 4000000000000) 2 (IntervalRat.scale (227 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (32579599987 / 1000000000000) (32579601663 / 1000000000000), orderedInterval (-77757767278 / 1000000000000) (-77757765603 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 2) <| besselDerivativeNearFromState (491137269030473 / 4000000000000) 2 (IntervalRat.scale (227 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-62336651863 / 1000000000000) (-62336651862 / 1000000000000), orderedInterval (-35787559889 / 1000000000000) (-35787559888 / 1000000000000)))) (orderedInterval (-5037626038 / 1000000000000) (-5037625951 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 2) <| besselDerivativeNearFromState (207671906921451 / 4000000000000) 2 (IntervalRat.scale (227 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (71851070681 / 1000000000000) (71851115469 / 1000000000000), orderedInterval (-84950689888 / 1000000000000) (-84950645099 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 2) <| besselDerivativeNearFromState (844174772036171 / 4000000000000) 2 (IntervalRat.scale (227 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-53488986952 / 1000000000000) (-53488986950 / 1000000000000), orderedInterval (-12341288892 / 1000000000000) (-12341288890 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 2) <| besselDerivativeNearFromState (563869625230789 / 4000000000000) 2 (IntervalRat.scale (227 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-24941931769 / 1000000000000) (-24941931768 / 1000000000000), orderedInterval (-62313444376 / 1000000000000) (-62313444375 / 1000000000000)))) (orderedInterval (-22505825322 / 1000000000000) (-22505825197 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate236_chunkChecks2 :
    compactCertificate236.chunkChecks (2 : Fin 5) 0 9 = true :=
  compactCertificate236.chunkChecks_nine_of_three (2 : Fin 5) compactCertificate236_chunkChecks2_0
    compactCertificate236_chunkChecks2_1 compactCertificate236_chunkChecks2_2

theorem compactCertificate236_chunkChecks3_0 :
    compactCertificate236.chunkChecks (3 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 3) <| besselDerivativeNearFromState (227 / 2) 3 (IntervalRat.scale (227 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (69443243969 / 1000000000000) (69443243970 / 1000000000000), orderedInterval (27740148711 / 1000000000000) (27740148712 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 3) <| besselDerivativeNearFromState (334414345173527 / 4000000000000) 3 (IntervalRat.scale (227 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (36813521833 / 1000000000000) (36813524489 / 1000000000000), orderedInterval (-79337760205 / 1000000000000) (-79337757550 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 3) <| besselDerivativeNearFromState (108142728252791 / 800000000000) 3 (IntervalRat.scale (227 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-52646566276 / 1000000000000) (-52646566275 / 1000000000000), orderedInterval (-43825853429 / 1000000000000) (-43825853428 / 1000000000000)))) (orderedInterval (-6148345490 / 1000000000000) (-6148345467 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 3) <| besselDerivativeNearFromState (97581271880389 / 4000000000000) 3 (IntervalRat.scale (227 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (6920130062 / 1000000000000) (6920130067 / 1000000000000), orderedInterval (161269317261 / 1000000000000) (161269317267 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 3) <| besselDerivativeNearFromState (262117022212033 / 4000000000000) 3 (IntervalRat.scale (227 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-32804665728 / 1000000000000) (-32804665727 / 1000000000000), orderedInterval (-92696578789 / 1000000000000) (-92696578788 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 3) <| besselDerivativeNearFromState (711698704328061 / 4000000000000) 3 (IntervalRat.scale (227 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (21150705033 / 1000000000000) (21150705681 / 1000000000000), orderedInterval (-56011987879 / 1000000000000) (-56011987232 / 1000000000000)))) (orderedInterval (-14706168854 / 1000000000000) (-14706168643 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 3) <| besselDerivativeNearFromState (524234044424293 / 4000000000000) 3 (IntervalRat.scale (227 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-7230849902 / 1000000000000) (-7230849876 / 1000000000000), orderedInterval (69347660248 / 1000000000000) (69347660274 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 3) <| besselDerivativeNearFromState (898283970404089 / 4000000000000) 3 (IntervalRat.scale (227 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-39605721440 / 1000000000000) (-39605653872 / 1000000000000), orderedInterval (35672060622 / 1000000000000) (35672128190 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 3) <| besselDerivativeNearFromState (661671906921451 / 4000000000000) 3 (IntervalRat.scale (227 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (18439196152 / 1000000000000) (18439196483 / 1000000000000), orderedInterval (-59288859328 / 1000000000000) (-59288858997 / 1000000000000)))) (orderedInterval (13008246123 / 1000000000000) (13008262398 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate236_chunkChecks3_1 :
    compactCertificate236.chunkChecks (3 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 3) <| besselDerivativeNearFromState (1015174861784773 / 4000000000000) 3 (IntervalRat.scale (227 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-5479029846 / 1000000000000) (-5479029845 / 1000000000000), orderedInterval (-49772729496 / 1000000000000) (-49772729495 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 3) <| besselDerivativeNearFromState (586111479725917 / 4000000000000) 3 (IntervalRat.scale (227 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (22133057544 / 1000000000000) (22133058166 / 1000000000000), orderedInterval (-62162948875 / 1000000000000) (-62162948253 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 3) <| besselDerivativeNearFromState (1040065106047553 / 4000000000000) 3 (IntervalRat.scale (227 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-2423786505 / 1000000000000) (-2423786504 / 1000000000000), orderedInterval (-49417136764 / 1000000000000) (-49417136763 / 1000000000000)))) (orderedInterval (-4457316005 / 1000000000000) (-4457315463 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 3) <| besselDerivativeNearFromState (971763735766757 / 4000000000000) 3 (IntervalRat.scale (227 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-49568727831 / 1000000000000) (-49568725595 / 1000000000000), orderedInterval (12885125760 / 1000000000000) (12885127996 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 3) <| besselDerivativeNearFromState (693496455169781 / 4000000000000) 3 (IntervalRat.scale (227 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-59393329990 / 1000000000000) (-59393329987 / 1000000000000), orderedInterval (-11843737016 / 1000000000000) (-11843737013 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 3) <| besselDerivativeNearFromState (786351066636099 / 4000000000000) 3 (IntervalRat.scale (227 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (29637841273 / 1000000000000) (29637846124 / 1000000000000), orderedInterval (-48654718463 / 1000000000000) (-48654713612 / 1000000000000)))) (orderedInterval (4910024905 / 1000000000000) (4910025494 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 3) <| besselDerivativeNearFromState (655577538141331 / 4000000000000) 3 (IntervalRat.scale (227 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (60315255922 / 1000000000000) (60315255923 / 1000000000000), orderedInterval (15512603055 / 1000000000000) (15512603056 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 3) <| besselDerivativeNearFromState (579222636619951 / 4000000000000) 3 (IntervalRat.scale (227 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (58382021871 / 1000000000000) (58382021872 / 1000000000000), orderedInterval (31229270146 / 1000000000000) (31229270147 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 3) <| besselDerivativeNearFromState (167881296379149 / 800000000000) 3 (IntervalRat.scale (227 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-8215339623 / 1000000000000) (-8215339622 / 1000000000000), orderedInterval (-54443097964 / 1000000000000) (-54443097963 / 1000000000000)))) (orderedInterval (11940267153 / 1000000000000) (11940267190 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate236_chunkChecks3_2 :
    compactCertificate236.chunkChecks (3 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 3) <| besselDerivativeNearFromState (464368500893303 / 4000000000000) 3 (IntervalRat.scale (227 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-44075975785 / 1000000000000) (-44075975784 / 1000000000000), orderedInterval (-59317058366 / 1000000000000) (-59317058365 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 3) <| besselDerivativeNearFromState (393650320947583 / 4000000000000) 3 (IntervalRat.scale (227 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-78189299398 / 1000000000000) (-78189298598 / 1000000000000), orderedInterval (19245194325 / 1000000000000) (19245195124 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 3) <| besselDerivativeNearFromState (246328093078549 / 4000000000000) 3 (IntervalRat.scale (227 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-45725263285 / 1000000000000) (-45725259114 / 1000000000000), orderedInterval (91185085872 / 1000000000000) (91185090042 / 1000000000000)))) (orderedInterval (-9821175202 / 1000000000000) (-9821175125 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 3) <| besselDerivativeNearFromState (132476067707883 / 4000000000000) 3 (IntervalRat.scale (227 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (84657675308 / 1000000000000) (84657706240 / 1000000000000), orderedInterval (-111076774414 / 1000000000000) (-111076743481 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 3) <| besselDerivativeNearFromState (359698294092649 / 4000000000000) 3 (IntervalRat.scale (227 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (32579599987 / 1000000000000) (32579601663 / 1000000000000), orderedInterval (-77757767278 / 1000000000000) (-77757765603 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 3) <| besselDerivativeNearFromState (491137269030473 / 4000000000000) 3 (IntervalRat.scale (227 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-62336651863 / 1000000000000) (-62336651862 / 1000000000000), orderedInterval (-35787559889 / 1000000000000) (-35787559888 / 1000000000000)))) (orderedInterval (-4355865345 / 1000000000000) (-4355865298 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 3) <| besselDerivativeNearFromState (207671906921451 / 4000000000000) 3 (IntervalRat.scale (227 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (71851070681 / 1000000000000) (71851115469 / 1000000000000), orderedInterval (-84950689888 / 1000000000000) (-84950645099 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 3) <| besselDerivativeNearFromState (844174772036171 / 4000000000000) 3 (IntervalRat.scale (227 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-53488986952 / 1000000000000) (-53488986950 / 1000000000000), orderedInterval (-12341288892 / 1000000000000) (-12341288890 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 3) <| besselDerivativeNearFromState (563869625230789 / 4000000000000) 3 (IntervalRat.scale (227 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-24941931769 / 1000000000000) (-24941931768 / 1000000000000), orderedInterval (-62313444376 / 1000000000000) (-62313444375 / 1000000000000)))) (orderedInterval (-28609647717 / 1000000000000) (-28609647588 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate236_chunkChecks3 :
    compactCertificate236.chunkChecks (3 : Fin 5) 0 9 = true :=
  compactCertificate236.chunkChecks_nine_of_three (3 : Fin 5) compactCertificate236_chunkChecks3_0
    compactCertificate236_chunkChecks3_1 compactCertificate236_chunkChecks3_2

theorem compactCertificate236_chunkChecks4_0 :
    compactCertificate236.chunkChecks (4 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 4) <| besselDerivativeNearFromState (227 / 2) 4 (IntervalRat.scale (227 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (69443243969 / 1000000000000) (69443243970 / 1000000000000), orderedInterval (27740148711 / 1000000000000) (27740148712 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 4) <| besselDerivativeNearFromState (334414345173527 / 4000000000000) 4 (IntervalRat.scale (227 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (36813521833 / 1000000000000) (36813524489 / 1000000000000), orderedInterval (-79337760205 / 1000000000000) (-79337757550 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 4) <| besselDerivativeNearFromState (108142728252791 / 800000000000) 4 (IntervalRat.scale (227 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-52646566276 / 1000000000000) (-52646566275 / 1000000000000), orderedInterval (-43825853429 / 1000000000000) (-43825853428 / 1000000000000)))) (orderedInterval (21516324124 / 1000000000000) (21516324147 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 4) <| besselDerivativeNearFromState (97581271880389 / 4000000000000) 4 (IntervalRat.scale (227 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (6920130062 / 1000000000000) (6920130067 / 1000000000000), orderedInterval (161269317261 / 1000000000000) (161269317267 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 4) <| besselDerivativeNearFromState (262117022212033 / 4000000000000) 4 (IntervalRat.scale (227 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-32804665728 / 1000000000000) (-32804665727 / 1000000000000), orderedInterval (-92696578789 / 1000000000000) (-92696578788 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 4) <| besselDerivativeNearFromState (711698704328061 / 4000000000000) 4 (IntervalRat.scale (227 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (21150705033 / 1000000000000) (21150705681 / 1000000000000), orderedInterval (-56011987879 / 1000000000000) (-56011987232 / 1000000000000)))) (orderedInterval (-8953930432 / 1000000000000) (-8953930101 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 4) <| besselDerivativeNearFromState (524234044424293 / 4000000000000) 4 (IntervalRat.scale (227 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-7230849902 / 1000000000000) (-7230849876 / 1000000000000), orderedInterval (69347660248 / 1000000000000) (69347660274 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 4) <| besselDerivativeNearFromState (898283970404089 / 4000000000000) 4 (IntervalRat.scale (227 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-39605721440 / 1000000000000) (-39605653872 / 1000000000000), orderedInterval (35672060622 / 1000000000000) (35672128190 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 4) <| besselDerivativeNearFromState (661671906921451 / 4000000000000) 4 (IntervalRat.scale (227 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (18439196152 / 1000000000000) (18439196483 / 1000000000000), orderedInterval (-59288859328 / 1000000000000) (-59288858997 / 1000000000000)))) (orderedInterval (20503258194 / 1000000000000) (20503290520 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate236_chunkChecks4_1 :
    compactCertificate236.chunkChecks (4 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 4) <| besselDerivativeNearFromState (1015174861784773 / 4000000000000) 4 (IntervalRat.scale (227 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-5479029846 / 1000000000000) (-5479029845 / 1000000000000), orderedInterval (-49772729496 / 1000000000000) (-49772729495 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 4) <| besselDerivativeNearFromState (586111479725917 / 4000000000000) 4 (IntervalRat.scale (227 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (22133057544 / 1000000000000) (22133058166 / 1000000000000), orderedInterval (-62162948875 / 1000000000000) (-62162948253 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 4) <| besselDerivativeNearFromState (1040065106047553 / 4000000000000) 4 (IntervalRat.scale (227 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-2423786505 / 1000000000000) (-2423786504 / 1000000000000), orderedInterval (-49417136764 / 1000000000000) (-49417136763 / 1000000000000)))) (orderedInterval (19481991431 / 1000000000000) (19481992542 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 4) <| besselDerivativeNearFromState (971763735766757 / 4000000000000) 4 (IntervalRat.scale (227 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-49568727831 / 1000000000000) (-49568725595 / 1000000000000), orderedInterval (12885125760 / 1000000000000) (12885127996 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 4) <| besselDerivativeNearFromState (693496455169781 / 4000000000000) 4 (IntervalRat.scale (227 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-59393329990 / 1000000000000) (-59393329987 / 1000000000000), orderedInterval (-11843737016 / 1000000000000) (-11843737013 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 4) <| besselDerivativeNearFromState (786351066636099 / 4000000000000) 4 (IntervalRat.scale (227 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (29637841273 / 1000000000000) (29637846124 / 1000000000000), orderedInterval (-48654718463 / 1000000000000) (-48654713612 / 1000000000000)))) (orderedInterval (-13230254321 / 1000000000000) (-13230253134 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 4) <| besselDerivativeNearFromState (655577538141331 / 4000000000000) 4 (IntervalRat.scale (227 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (60315255922 / 1000000000000) (60315255923 / 1000000000000), orderedInterval (15512603055 / 1000000000000) (15512603056 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 4) <| besselDerivativeNearFromState (579222636619951 / 4000000000000) 4 (IntervalRat.scale (227 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (58382021871 / 1000000000000) (58382021872 / 1000000000000), orderedInterval (31229270146 / 1000000000000) (31229270147 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 4) <| besselDerivativeNearFromState (167881296379149 / 800000000000) 4 (IntervalRat.scale (227 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-8215339623 / 1000000000000) (-8215339622 / 1000000000000), orderedInterval (-54443097964 / 1000000000000) (-54443097963 / 1000000000000)))) (orderedInterval (-8491751406 / 1000000000000) (-8491751348 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate236_chunkChecks4_2 :
    compactCertificate236.chunkChecks (4 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 4) <| besselDerivativeNearFromState (464368500893303 / 4000000000000) 4 (IntervalRat.scale (227 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-44075975785 / 1000000000000) (-44075975784 / 1000000000000), orderedInterval (-59317058366 / 1000000000000) (-59317058365 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 4) <| besselDerivativeNearFromState (393650320947583 / 4000000000000) 4 (IntervalRat.scale (227 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-78189299398 / 1000000000000) (-78189298598 / 1000000000000), orderedInterval (19245194325 / 1000000000000) (19245195124 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 4) <| besselDerivativeNearFromState (246328093078549 / 4000000000000) 4 (IntervalRat.scale (227 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-45725263285 / 1000000000000) (-45725259114 / 1000000000000), orderedInterval (91185085872 / 1000000000000) (91185090042 / 1000000000000)))) (orderedInterval (10258245850 / 1000000000000) (10258245913 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 4) <| besselDerivativeNearFromState (132476067707883 / 4000000000000) 4 (IntervalRat.scale (227 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (84657675308 / 1000000000000) (84657706240 / 1000000000000), orderedInterval (-111076774414 / 1000000000000) (-111076743481 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 4) <| besselDerivativeNearFromState (359698294092649 / 4000000000000) 4 (IntervalRat.scale (227 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (32579599987 / 1000000000000) (32579601663 / 1000000000000), orderedInterval (-77757767278 / 1000000000000) (-77757765603 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 4) <| besselDerivativeNearFromState (491137269030473 / 4000000000000) 4 (IntervalRat.scale (227 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-62336651863 / 1000000000000) (-62336651862 / 1000000000000), orderedInterval (-35787559889 / 1000000000000) (-35787559888 / 1000000000000)))) (orderedInterval (6316845577 / 1000000000000) (6316845611 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 4) <| besselDerivativeNearFromState (207671906921451 / 4000000000000) 4 (IntervalRat.scale (227 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (71851070681 / 1000000000000) (71851115469 / 1000000000000), orderedInterval (-84950689888 / 1000000000000) (-84950645099 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 4) <| besselDerivativeNearFromState (844174772036171 / 4000000000000) 4 (IntervalRat.scale (227 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-53488986952 / 1000000000000) (-53488986950 / 1000000000000), orderedInterval (-12341288892 / 1000000000000) (-12341288890 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 4) <| besselDerivativeNearFromState (563869625230789 / 4000000000000) 4 (IntervalRat.scale (227 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-24941931769 / 1000000000000) (-24941931768 / 1000000000000), orderedInterval (-62313444376 / 1000000000000) (-62313444375 / 1000000000000)))) (orderedInterval (63705027063 / 1000000000000) (63705027240 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate236_chunkChecks4 :
    compactCertificate236.chunkChecks (4 : Fin 5) 0 9 = true :=
  compactCertificate236.chunkChecks_nine_of_three (4 : Fin 5) compactCertificate236_chunkChecks4_0
    compactCertificate236_chunkChecks4_1 compactCertificate236_chunkChecks4_2

theorem compactCertificate236_chunks :
    ∀ r : Fin 5, ∀ b, compactCertificate236.chunkCheck r b = true :=
  compactCertificate236.chunkChecks_all (by
    intro r
    fin_cases r
    · exact compactCertificate236_chunkChecks0
    · exact compactCertificate236_chunkChecks1
    · exact compactCertificate236_chunkChecks2
    · exact compactCertificate236_chunkChecks3
    · exact compactCertificate236_chunkChecks4)

theorem compactCertificate236_coefficient0 :
    compactCertificate236.coefficientCheck (0 : Fin 5) = true := by
  norm_num [CompactCertificate.coefficientCheck, intervalFinSumHull,
    compactCertificate236, rationalIntervalSubset, orderedInterval, Fin.sum_univ_succ]

theorem compactCertificate236_coefficient1 :
    compactCertificate236.coefficientCheck (1 : Fin 5) = true := by
  norm_num [CompactCertificate.coefficientCheck, intervalFinSumHull,
    compactCertificate236, rationalIntervalSubset, orderedInterval, Fin.sum_univ_succ]

theorem compactCertificate236_coefficient2 :
    compactCertificate236.coefficientCheck (2 : Fin 5) = true := by
  norm_num [CompactCertificate.coefficientCheck, intervalFinSumHull,
    compactCertificate236, rationalIntervalSubset, orderedInterval, Fin.sum_univ_succ]

theorem compactCertificate236_coefficient3 :
    compactCertificate236.coefficientCheck (3 : Fin 5) = true := by
  norm_num [CompactCertificate.coefficientCheck, intervalFinSumHull,
    compactCertificate236, rationalIntervalSubset, orderedInterval, Fin.sum_univ_succ]

theorem compactCertificate236_coefficient4 :
    compactCertificate236.coefficientCheck (4 : Fin 5) = true := by
  norm_num [CompactCertificate.coefficientCheck, intervalFinSumHull,
    compactCertificate236, rationalIntervalSubset, orderedInterval, Fin.sum_univ_succ]

theorem compactCertificate236_coefficients : ∀ r : Fin 5,
    compactCertificate236.coefficientCheck r = true := by
  intro r
  fin_cases r
  · exact compactCertificate236_coefficient0
  · exact compactCertificate236_coefficient1
  · exact compactCertificate236_coefficient2
  · exact compactCertificate236_coefficient3
  · exact compactCertificate236_coefficient4

theorem compactCertificate236_lower : (1 : ℚ) ≤ compactCertificate236.output.lo := by
  norm_num [CompactCertificate.output, CompactCertificate.interval,
    CompactCertificate.coefficientTargetNat, compactCertificate236, dualConstant,
    intervalTaylorSum, intervalPow, intervalSub, intervalMaxAbs, widenInterval,
    rationalErrorInterval, orderedInterval, IntervalRat.add, IntervalRat.mul, IntervalRat.scale,
    IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4]

theorem compactCertificate236_proves {t : ℝ} (ht : t ∈ compactCertificate236.interval) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t :=
  compactCertificate236.proves compactCertificate236_states compactCertificate236_chunks
    compactCertificate236_coefficients compactCertificate236_lower ht

end Erdos232
