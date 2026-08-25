/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, OpenAI Codex
-/
import ErdosProblems.Erdos232.CompactBase

open LeanCert.Core
namespace Erdos232

def compactCertificate271 : CompactCertificate where
  left := 145
  right := 146
  center := 291 / 2
  grid := fun i =>
    match i.val with
    | 0 => 46
    | 1 => 34
    | 2 => 55
    | 3 => 10
    | 4 => 27
    | 5 => 73
    | 6 => 54
    | 7 => 92
    | 8 => 68
    | 9 => 104
    | 10 => 60
    | 11 => 106
    | 12 => 99
    | 13 => 71
    | 14 => 80
    | 15 => 67
    | 16 => 59
    | 17 => 86
    | 18 => 47
    | 19 => 40
    | 20 => 25
    | 21 => 14
    | 22 => 37
    | 23 => 50
    | 24 => 21
    | 25 => 86
    | _ => 58
  point := fun i =>
    match i.val with
    | 0 => 291 / 2
    | 1 => 428698565839191 / 4000000000000
    | 2 => 138632308024503 / 800000000000
    | 3 => 125093172322437 / 4000000000000
    | 4 => 336017856668289 / 4000000000000
    | 5 => 912353845636413 / 4000000000000
    | 6 => 672035713336869 / 4000000000000
    | 7 => 1151544649284537 / 4000000000000
    | 8 => 848222576714283 / 4000000000000
    | 9 => 1301391562904709 / 4000000000000
    | 10 => 751358769164061 / 4000000000000
    | 11 => 1333299320968449 / 4000000000000
    | 12 => 1245741176687781 / 4000000000000
    | 13 => 889019684821173 / 4000000000000
    | 14 => 1008053570004867 / 4000000000000
    | 15 => 840409971802323 / 4000000000000
    | 16 => 742527697164783 / 4000000000000
    | 17 => 215213468045517 / 800000000000
    | 18 => 595291778678199 / 4000000000000
    | 19 => 504635433461439 / 4000000000000
    | 20 => 315777423285717 / 4000000000000
    | 21 => 169826148471339 / 4000000000000
    | 22 => 461111028991017 / 4000000000000
    | 23 => 629607688492809 / 4000000000000
    | 24 => 266222576714283 / 4000000000000
    | 25 => 1082179994108043 / 4000000000000
    | _ => 722846083445637 / 4000000000000
  state := fun i =>
    match i.val with
    | 0 => (orderedInterval (64821710916 / 1000000000000) (64821711602 / 1000000000000), orderedInterval (-13395284302 / 1000000000000) (-13395283616 / 1000000000000))
    | 1 => (orderedInterval (70180632548 / 1000000000000) (70180632549 / 1000000000000), orderedInterval (31526302049 / 1000000000000) (31526302050 / 1000000000000))
    | 2 => (orderedInterval (-58194487030 / 1000000000000) (-58194487029 / 1000000000000), orderedInterval (-16776276688 / 1000000000000) (-16776276687 / 1000000000000))
    | 3 => (orderedInterval (85059638782 / 1000000000000) (85059638783 / 1000000000000), orderedInterval (113192874996 / 1000000000000) (113192874997 / 1000000000000))
    | 4 => (orderedInterval (3013810215 / 1000000000000) (3013810228 / 1000000000000), orderedInterval (-87020552079 / 1000000000000) (-87020552066 / 1000000000000))
    | 5 => (orderedInterval (23593821292 / 1000000000000) (23593822894 / 1000000000000), orderedInterval (-47321634076 / 1000000000000) (-47321632474 / 1000000000000))
    | 6 => (orderedInterval (-46344343566 / 1000000000000) (-46344246968 / 1000000000000), orderedInterval (40652138282 / 1000000000000) (40652234880 / 1000000000000))
    | 7 => (orderedInterval (-16362997911 / 1000000000000) (-16362997614 / 1000000000000), orderedInterval (44114859474 / 1000000000000) (44114859772 / 1000000000000))
    | 8 => (orderedInterval (-38838365600 / 1000000000000) (-38838319874 / 1000000000000), orderedInterval (38740206187 / 1000000000000) (38740251913 / 1000000000000))
    | 9 => (orderedInterval (-24710920003 / 1000000000000) (-24710916087 / 1000000000000), orderedInterval (36727303684 / 1000000000000) (36727307601 / 1000000000000))
    | 10 => (orderedInterval (7481360192 / 1000000000000) (7481360193 / 1000000000000), orderedInterval (57714011719 / 1000000000000) (57714011720 / 1000000000000))
    | 11 => (orderedInterval (38968402154 / 1000000000000) (38968402155 / 1000000000000), orderedInterval (19724629793 / 1000000000000) (19724629794 / 1000000000000))
    | 12 => (orderedInterval (-42182310159 / 1000000000000) (-42182310158 / 1000000000000), orderedInterval (-16204910010 / 1000000000000) (-16204910009 / 1000000000000))
    | 13 => (orderedInterval (712939029 / 1000000000000) (712939032 / 1000000000000), orderedInterval (-53516708846 / 1000000000000) (-53516708842 / 1000000000000))
    | 14 => (orderedInterval (50009955766 / 1000000000000) (50009955789 / 1000000000000), orderedInterval (4914175324 / 1000000000000) (4914175347 / 1000000000000))
    | 15 => (orderedInterval (-21465654795 / 1000000000000) (-21465654794 / 1000000000000), orderedInterval (-50636937905 / 1000000000000) (-50636937904 / 1000000000000))
    | 16 => (orderedInterval (-51163148127 / 1000000000000) (-51163148126 / 1000000000000), orderedInterval (-28354284174 / 1000000000000) (-28354284173 / 1000000000000))
    | 17 => (orderedInterval (-17826845918 / 1000000000000) (-17826845484 / 1000000000000), orderedInterval (45295420969 / 1000000000000) (45295421402 / 1000000000000))
    | 18 => (orderedInterval (-60693295436 / 1000000000000) (-60693290007 / 1000000000000), orderedInterval (24576140958 / 1000000000000) (24576146387 / 1000000000000))
    | 19 => (orderedInterval (68044792387 / 1000000000000) (68044792388 / 1000000000000), orderedInterval (20127601789 / 1000000000000) (20127601790 / 1000000000000))
    | 20 => (orderedInterval (-83312273026 / 1000000000000) (-83312273025 / 1000000000000), orderedInterval (-32985140430 / 1000000000000) (-32985140429 / 1000000000000))
    | 21 => (orderedInterval (-82863852009 / 1000000000000) (-82863787598 / 1000000000000), orderedInterval (91132767285 / 1000000000000) (91132831696 / 1000000000000))
    | 22 => (orderedInterval (13074386017 / 1000000000000) (13074386103 / 1000000000000), orderedInterval (-73211303121 / 1000000000000) (-73211303036 / 1000000000000))
    | 23 => (orderedInterval (56875273951 / 1000000000000) (56875273952 / 1000000000000), orderedInterval (28275261751 / 1000000000000) (28275261752 / 1000000000000))
    | 24 => (orderedInterval (-95751199824 / 1000000000000) (-95751199822 / 1000000000000), orderedInterval (-19197691530 / 1000000000000) (-19197691528 / 1000000000000))
    | 25 => (orderedInterval (44335608731 / 1000000000000) (44335608732 / 1000000000000), orderedInterval (19601871939 / 1000000000000) (19601871940 / 1000000000000))
    | _ => (orderedInterval (-38964560615 / 1000000000000) (-38964533039 / 1000000000000), orderedInterval (44880742566 / 1000000000000) (44880770142 / 1000000000000))
  chunkTarget := fun r b =>
    match r.val with
    | 0 =>
      match b.val with
      | 0 => orderedInterval (22932085492 / 1000000000000) (22932085775 / 1000000000000)
      | 1 => orderedInterval (-2490073709 / 1000000000000) (-2490073576 / 1000000000000)
      | 2 => orderedInterval (-433946358 / 1000000000000) (-433945235 / 1000000000000)
      | 3 => orderedInterval (10484726594 / 1000000000000) (10484727348 / 1000000000000)
      | 4 => orderedInterval (575859240 / 1000000000000) (575859258 / 1000000000000)
      | 5 => orderedInterval (2223580975 / 1000000000000) (2223581001 / 1000000000000)
      | 6 => orderedInterval (3140812452 / 1000000000000) (3140813358 / 1000000000000)
      | 7 => orderedInterval (-3125383996 / 1000000000000) (-3125382786 / 1000000000000)
      | _ => orderedInterval (3124563016 / 1000000000000) (3124568231 / 1000000000000)
    | 1 =>
      match b.val with
      | 0 => orderedInterval (-6265516973 / 1000000000000) (-6265516689 / 1000000000000)
      | 1 => orderedInterval (3175235253 / 1000000000000) (3175235453 / 1000000000000)
      | 2 => orderedInterval (-1327686135 / 1000000000000) (-1327684491 / 1000000000000)
      | 3 => orderedInterval (-2648514639 / 1000000000000) (-2648512962 / 1000000000000)
      | 4 => orderedInterval (-7147225068 / 1000000000000) (-7147225039 / 1000000000000)
      | 5 => orderedInterval (3370071031 / 1000000000000) (3370071072 / 1000000000000)
      | 6 => orderedInterval (-5589705948 / 1000000000000) (-5589705026 / 1000000000000)
      | 7 => orderedInterval (-1519337308 / 1000000000000) (-1519336943 / 1000000000000)
      | _ => orderedInterval (-13478564847 / 1000000000000) (-13478558363 / 1000000000000)
    | 2 =>
      match b.val with
      | 0 => orderedInterval (-21160818340 / 1000000000000) (-21160818052 / 1000000000000)
      | 1 => orderedInterval (4105914472 / 1000000000000) (4105914782 / 1000000000000)
      | 2 => orderedInterval (27067973 / 1000000000000) (27070394 / 1000000000000)
      | 3 => orderedInterval (-51932599891 / 1000000000000) (-51932596144 / 1000000000000)
      | 4 => orderedInterval (-2837872074 / 1000000000000) (-2837872025 / 1000000000000)
      | 5 => orderedInterval (-2711769570 / 1000000000000) (-2711769501 / 1000000000000)
      | 6 => orderedInterval (-6420376603 / 1000000000000) (-6420375656 / 1000000000000)
      | 7 => orderedInterval (5167486572 / 1000000000000) (5167486694 / 1000000000000)
      | _ => orderedInterval (1413839452 / 1000000000000) (1413847562 / 1000000000000)
    | 3 =>
      match b.val with
      | 0 => orderedInterval (7000294935 / 1000000000000) (7000295225 / 1000000000000)
      | 1 => orderedInterval (-12363872315 / 1000000000000) (-12363871833 / 1000000000000)
      | 2 => orderedInterval (7641030408 / 1000000000000) (7641033963 / 1000000000000)
      | 3 => orderedInterval (30406655589 / 1000000000000) (30406663958 / 1000000000000)
      | 4 => orderedInterval (15316958693 / 1000000000000) (15316958774 / 1000000000000)
      | 5 => orderedInterval (-8920354204 / 1000000000000) (-8920354086 / 1000000000000)
      | 6 => orderedInterval (5162976166 / 1000000000000) (5162977134 / 1000000000000)
      | 7 => orderedInterval (1923632466 / 1000000000000) (1923632514 / 1000000000000)
      | _ => orderedInterval (26391967773 / 1000000000000) (26391977870 / 1000000000000)
    | _ =>
      match b.val with
      | 0 => orderedInterval (18917247816 / 1000000000000) (18917248111 / 1000000000000)
      | 1 => orderedInterval (-9948584871 / 1000000000000) (-9948584113 / 1000000000000)
      | 2 => orderedInterval (3395087480 / 1000000000000) (3395092739 / 1000000000000)
      | 3 => orderedInterval (263469603275 / 1000000000000) (263469622029 / 1000000000000)
      | 4 => orderedInterval (13863241486 / 1000000000000) (13863241626 / 1000000000000)
      | 5 => orderedInterval (1468193053 / 1000000000000) (1468193258 / 1000000000000)
      | 6 => orderedInterval (8138574324 / 1000000000000) (8138575318 / 1000000000000)
      | 7 => orderedInterval (-6101793658 / 1000000000000) (-6101793630 / 1000000000000)
      | _ => orderedInterval (-26132988335 / 1000000000000) (-26132975680 / 1000000000000)
  coefficientTarget := fun i =>
    match i.val with
    | 0 => orderedInterval (36432223706 / 1000000000000) (36432233374 / 1000000000000)
    | 1 => orderedInterval (-31431244634 / 1000000000000) (-31431232988 / 1000000000000)
    | 2 => orderedInterval (-74349128009 / 1000000000000) (-74349111946 / 1000000000000)
    | 3 => orderedInterval (72559289511 / 1000000000000) (72559313519 / 1000000000000)
    | _ => orderedInterval (267068580570 / 1000000000000) (267068619658 / 1000000000000)

theorem compactCertificate271_stateChecks0 :
    compactCertificate271.stateChecks 0 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 46 12 (291 / 2)) (orderedInterval (64821710916 / 1000000000000) (64821711602 / 1000000000000), orderedInterval (-13395284302 / 1000000000000) (-13395283616 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 34 12 (428698565839191 / 4000000000000)) (orderedInterval (70180632548 / 1000000000000) (70180632549 / 1000000000000), orderedInterval (31526302049 / 1000000000000) (31526302050 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 55 12 (138632308024503 / 800000000000)) (orderedInterval (-58194487030 / 1000000000000) (-58194487029 / 1000000000000), orderedInterval (-16776276688 / 1000000000000) (-16776276687 / 1000000000000))) = true
  norm_num [besselStateAtRationalPoint, besselIntervalStepZero,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, besselZeroTransition,
    besselInitial, besselGridStateAt, besselGridStateBlock00, besselGridStateBlock01,
    besselGridStateBlock02, besselGridStateBlock03, besselGridStateBlock04,
    besselGridStateBlock05, besselGridStateBlock06, besselGridStateBlock07,
    besselGridStateBlock08, besselGridStateBlock09, besselGridStateBlock10,
    besselGridStateBlock11, besselGridStateBlock12, besselGridStateBlock13,
    besselGridStateBlock14, besselGridState010, besselGridState014, besselGridState021, besselGridState025, besselGridState027, besselGridState034, besselGridState037, besselGridState040, besselGridState046, besselGridState047, besselGridState050, besselGridState054, besselGridState055, besselGridState058, besselGridState059, besselGridState060, besselGridState067, besselGridState068, besselGridState071, besselGridState073, besselGridState080, besselGridState086, besselGridState092, besselGridState099, besselGridState104, besselGridState106, besselStateSubset, linearInterval, widenInterval,
    rationalErrorInterval, rationalIntervalSubset, orderedInterval, Finset.sum_range_succ,
    IntervalRat.add, IntervalRat.mul, IntervalRat.scale, IntervalRat.singleton]

theorem compactCertificate271_stateChecks1 :
    compactCertificate271.stateChecks 3 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 10 12 (125093172322437 / 4000000000000)) (orderedInterval (85059638782 / 1000000000000) (85059638783 / 1000000000000), orderedInterval (113192874996 / 1000000000000) (113192874997 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 27 12 (336017856668289 / 4000000000000)) (orderedInterval (3013810215 / 1000000000000) (3013810228 / 1000000000000), orderedInterval (-87020552079 / 1000000000000) (-87020552066 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 73 12 (912353845636413 / 4000000000000)) (orderedInterval (23593821292 / 1000000000000) (23593822894 / 1000000000000), orderedInterval (-47321634076 / 1000000000000) (-47321632474 / 1000000000000))) = true
  norm_num [besselStateAtRationalPoint, besselIntervalStepZero,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, besselZeroTransition,
    besselInitial, besselGridStateAt, besselGridStateBlock00, besselGridStateBlock01,
    besselGridStateBlock02, besselGridStateBlock03, besselGridStateBlock04,
    besselGridStateBlock05, besselGridStateBlock06, besselGridStateBlock07,
    besselGridStateBlock08, besselGridStateBlock09, besselGridStateBlock10,
    besselGridStateBlock11, besselGridStateBlock12, besselGridStateBlock13,
    besselGridStateBlock14, besselGridState010, besselGridState014, besselGridState021, besselGridState025, besselGridState027, besselGridState034, besselGridState037, besselGridState040, besselGridState046, besselGridState047, besselGridState050, besselGridState054, besselGridState055, besselGridState058, besselGridState059, besselGridState060, besselGridState067, besselGridState068, besselGridState071, besselGridState073, besselGridState080, besselGridState086, besselGridState092, besselGridState099, besselGridState104, besselGridState106, besselStateSubset, linearInterval, widenInterval,
    rationalErrorInterval, rationalIntervalSubset, orderedInterval, Finset.sum_range_succ,
    IntervalRat.add, IntervalRat.mul, IntervalRat.scale, IntervalRat.singleton]

theorem compactCertificate271_stateChecks2 :
    compactCertificate271.stateChecks 6 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 54 12 (672035713336869 / 4000000000000)) (orderedInterval (-46344343566 / 1000000000000) (-46344246968 / 1000000000000), orderedInterval (40652138282 / 1000000000000) (40652234880 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 92 12 (1151544649284537 / 4000000000000)) (orderedInterval (-16362997911 / 1000000000000) (-16362997614 / 1000000000000), orderedInterval (44114859474 / 1000000000000) (44114859772 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 68 12 (848222576714283 / 4000000000000)) (orderedInterval (-38838365600 / 1000000000000) (-38838319874 / 1000000000000), orderedInterval (38740206187 / 1000000000000) (38740251913 / 1000000000000))) = true
  norm_num [besselStateAtRationalPoint, besselIntervalStepZero,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, besselZeroTransition,
    besselInitial, besselGridStateAt, besselGridStateBlock00, besselGridStateBlock01,
    besselGridStateBlock02, besselGridStateBlock03, besselGridStateBlock04,
    besselGridStateBlock05, besselGridStateBlock06, besselGridStateBlock07,
    besselGridStateBlock08, besselGridStateBlock09, besselGridStateBlock10,
    besselGridStateBlock11, besselGridStateBlock12, besselGridStateBlock13,
    besselGridStateBlock14, besselGridState010, besselGridState014, besselGridState021, besselGridState025, besselGridState027, besselGridState034, besselGridState037, besselGridState040, besselGridState046, besselGridState047, besselGridState050, besselGridState054, besselGridState055, besselGridState058, besselGridState059, besselGridState060, besselGridState067, besselGridState068, besselGridState071, besselGridState073, besselGridState080, besselGridState086, besselGridState092, besselGridState099, besselGridState104, besselGridState106, besselStateSubset, linearInterval, widenInterval,
    rationalErrorInterval, rationalIntervalSubset, orderedInterval, Finset.sum_range_succ,
    IntervalRat.add, IntervalRat.mul, IntervalRat.scale, IntervalRat.singleton]

theorem compactCertificate271_stateChecks3 :
    compactCertificate271.stateChecks 9 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 104 12 (1301391562904709 / 4000000000000)) (orderedInterval (-24710920003 / 1000000000000) (-24710916087 / 1000000000000), orderedInterval (36727303684 / 1000000000000) (36727307601 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 60 12 (751358769164061 / 4000000000000)) (orderedInterval (7481360192 / 1000000000000) (7481360193 / 1000000000000), orderedInterval (57714011719 / 1000000000000) (57714011720 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 106 12 (1333299320968449 / 4000000000000)) (orderedInterval (38968402154 / 1000000000000) (38968402155 / 1000000000000), orderedInterval (19724629793 / 1000000000000) (19724629794 / 1000000000000))) = true
  norm_num [besselStateAtRationalPoint, besselIntervalStepZero,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, besselZeroTransition,
    besselInitial, besselGridStateAt, besselGridStateBlock00, besselGridStateBlock01,
    besselGridStateBlock02, besselGridStateBlock03, besselGridStateBlock04,
    besselGridStateBlock05, besselGridStateBlock06, besselGridStateBlock07,
    besselGridStateBlock08, besselGridStateBlock09, besselGridStateBlock10,
    besselGridStateBlock11, besselGridStateBlock12, besselGridStateBlock13,
    besselGridStateBlock14, besselGridState010, besselGridState014, besselGridState021, besselGridState025, besselGridState027, besselGridState034, besselGridState037, besselGridState040, besselGridState046, besselGridState047, besselGridState050, besselGridState054, besselGridState055, besselGridState058, besselGridState059, besselGridState060, besselGridState067, besselGridState068, besselGridState071, besselGridState073, besselGridState080, besselGridState086, besselGridState092, besselGridState099, besselGridState104, besselGridState106, besselStateSubset, linearInterval, widenInterval,
    rationalErrorInterval, rationalIntervalSubset, orderedInterval, Finset.sum_range_succ,
    IntervalRat.add, IntervalRat.mul, IntervalRat.scale, IntervalRat.singleton]

theorem compactCertificate271_stateChecks4 :
    compactCertificate271.stateChecks 12 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 99 12 (1245741176687781 / 4000000000000)) (orderedInterval (-42182310159 / 1000000000000) (-42182310158 / 1000000000000), orderedInterval (-16204910010 / 1000000000000) (-16204910009 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 71 12 (889019684821173 / 4000000000000)) (orderedInterval (712939029 / 1000000000000) (712939032 / 1000000000000), orderedInterval (-53516708846 / 1000000000000) (-53516708842 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 80 12 (1008053570004867 / 4000000000000)) (orderedInterval (50009955766 / 1000000000000) (50009955789 / 1000000000000), orderedInterval (4914175324 / 1000000000000) (4914175347 / 1000000000000))) = true
  norm_num [besselStateAtRationalPoint, besselIntervalStepZero,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, besselZeroTransition,
    besselInitial, besselGridStateAt, besselGridStateBlock00, besselGridStateBlock01,
    besselGridStateBlock02, besselGridStateBlock03, besselGridStateBlock04,
    besselGridStateBlock05, besselGridStateBlock06, besselGridStateBlock07,
    besselGridStateBlock08, besselGridStateBlock09, besselGridStateBlock10,
    besselGridStateBlock11, besselGridStateBlock12, besselGridStateBlock13,
    besselGridStateBlock14, besselGridState010, besselGridState014, besselGridState021, besselGridState025, besselGridState027, besselGridState034, besselGridState037, besselGridState040, besselGridState046, besselGridState047, besselGridState050, besselGridState054, besselGridState055, besselGridState058, besselGridState059, besselGridState060, besselGridState067, besselGridState068, besselGridState071, besselGridState073, besselGridState080, besselGridState086, besselGridState092, besselGridState099, besselGridState104, besselGridState106, besselStateSubset, linearInterval, widenInterval,
    rationalErrorInterval, rationalIntervalSubset, orderedInterval, Finset.sum_range_succ,
    IntervalRat.add, IntervalRat.mul, IntervalRat.scale, IntervalRat.singleton]

theorem compactCertificate271_stateChecks5 :
    compactCertificate271.stateChecks 15 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 67 12 (840409971802323 / 4000000000000)) (orderedInterval (-21465654795 / 1000000000000) (-21465654794 / 1000000000000), orderedInterval (-50636937905 / 1000000000000) (-50636937904 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 59 12 (742527697164783 / 4000000000000)) (orderedInterval (-51163148127 / 1000000000000) (-51163148126 / 1000000000000), orderedInterval (-28354284174 / 1000000000000) (-28354284173 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 86 12 (215213468045517 / 800000000000)) (orderedInterval (-17826845918 / 1000000000000) (-17826845484 / 1000000000000), orderedInterval (45295420969 / 1000000000000) (45295421402 / 1000000000000))) = true
  norm_num [besselStateAtRationalPoint, besselIntervalStepZero,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, besselZeroTransition,
    besselInitial, besselGridStateAt, besselGridStateBlock00, besselGridStateBlock01,
    besselGridStateBlock02, besselGridStateBlock03, besselGridStateBlock04,
    besselGridStateBlock05, besselGridStateBlock06, besselGridStateBlock07,
    besselGridStateBlock08, besselGridStateBlock09, besselGridStateBlock10,
    besselGridStateBlock11, besselGridStateBlock12, besselGridStateBlock13,
    besselGridStateBlock14, besselGridState010, besselGridState014, besselGridState021, besselGridState025, besselGridState027, besselGridState034, besselGridState037, besselGridState040, besselGridState046, besselGridState047, besselGridState050, besselGridState054, besselGridState055, besselGridState058, besselGridState059, besselGridState060, besselGridState067, besselGridState068, besselGridState071, besselGridState073, besselGridState080, besselGridState086, besselGridState092, besselGridState099, besselGridState104, besselGridState106, besselStateSubset, linearInterval, widenInterval,
    rationalErrorInterval, rationalIntervalSubset, orderedInterval, Finset.sum_range_succ,
    IntervalRat.add, IntervalRat.mul, IntervalRat.scale, IntervalRat.singleton]

theorem compactCertificate271_stateChecks6 :
    compactCertificate271.stateChecks 18 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 47 12 (595291778678199 / 4000000000000)) (orderedInterval (-60693295436 / 1000000000000) (-60693290007 / 1000000000000), orderedInterval (24576140958 / 1000000000000) (24576146387 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 40 12 (504635433461439 / 4000000000000)) (orderedInterval (68044792387 / 1000000000000) (68044792388 / 1000000000000), orderedInterval (20127601789 / 1000000000000) (20127601790 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 25 12 (315777423285717 / 4000000000000)) (orderedInterval (-83312273026 / 1000000000000) (-83312273025 / 1000000000000), orderedInterval (-32985140430 / 1000000000000) (-32985140429 / 1000000000000))) = true
  norm_num [besselStateAtRationalPoint, besselIntervalStepZero,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, besselZeroTransition,
    besselInitial, besselGridStateAt, besselGridStateBlock00, besselGridStateBlock01,
    besselGridStateBlock02, besselGridStateBlock03, besselGridStateBlock04,
    besselGridStateBlock05, besselGridStateBlock06, besselGridStateBlock07,
    besselGridStateBlock08, besselGridStateBlock09, besselGridStateBlock10,
    besselGridStateBlock11, besselGridStateBlock12, besselGridStateBlock13,
    besselGridStateBlock14, besselGridState010, besselGridState014, besselGridState021, besselGridState025, besselGridState027, besselGridState034, besselGridState037, besselGridState040, besselGridState046, besselGridState047, besselGridState050, besselGridState054, besselGridState055, besselGridState058, besselGridState059, besselGridState060, besselGridState067, besselGridState068, besselGridState071, besselGridState073, besselGridState080, besselGridState086, besselGridState092, besselGridState099, besselGridState104, besselGridState106, besselStateSubset, linearInterval, widenInterval,
    rationalErrorInterval, rationalIntervalSubset, orderedInterval, Finset.sum_range_succ,
    IntervalRat.add, IntervalRat.mul, IntervalRat.scale, IntervalRat.singleton]

theorem compactCertificate271_stateChecks7 :
    compactCertificate271.stateChecks 21 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 14 12 (169826148471339 / 4000000000000)) (orderedInterval (-82863852009 / 1000000000000) (-82863787598 / 1000000000000), orderedInterval (91132767285 / 1000000000000) (91132831696 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 37 12 (461111028991017 / 4000000000000)) (orderedInterval (13074386017 / 1000000000000) (13074386103 / 1000000000000), orderedInterval (-73211303121 / 1000000000000) (-73211303036 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 50 12 (629607688492809 / 4000000000000)) (orderedInterval (56875273951 / 1000000000000) (56875273952 / 1000000000000), orderedInterval (28275261751 / 1000000000000) (28275261752 / 1000000000000))) = true
  norm_num [besselStateAtRationalPoint, besselIntervalStepZero,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, besselZeroTransition,
    besselInitial, besselGridStateAt, besselGridStateBlock00, besselGridStateBlock01,
    besselGridStateBlock02, besselGridStateBlock03, besselGridStateBlock04,
    besselGridStateBlock05, besselGridStateBlock06, besselGridStateBlock07,
    besselGridStateBlock08, besselGridStateBlock09, besselGridStateBlock10,
    besselGridStateBlock11, besselGridStateBlock12, besselGridStateBlock13,
    besselGridStateBlock14, besselGridState010, besselGridState014, besselGridState021, besselGridState025, besselGridState027, besselGridState034, besselGridState037, besselGridState040, besselGridState046, besselGridState047, besselGridState050, besselGridState054, besselGridState055, besselGridState058, besselGridState059, besselGridState060, besselGridState067, besselGridState068, besselGridState071, besselGridState073, besselGridState080, besselGridState086, besselGridState092, besselGridState099, besselGridState104, besselGridState106, besselStateSubset, linearInterval, widenInterval,
    rationalErrorInterval, rationalIntervalSubset, orderedInterval, Finset.sum_range_succ,
    IntervalRat.add, IntervalRat.mul, IntervalRat.scale, IntervalRat.singleton]

theorem compactCertificate271_stateChecks8 :
    compactCertificate271.stateChecks 24 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 21 12 (266222576714283 / 4000000000000)) (orderedInterval (-95751199824 / 1000000000000) (-95751199822 / 1000000000000), orderedInterval (-19197691530 / 1000000000000) (-19197691528 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 86 12 (1082179994108043 / 4000000000000)) (orderedInterval (44335608731 / 1000000000000) (44335608732 / 1000000000000), orderedInterval (19601871939 / 1000000000000) (19601871940 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 58 12 (722846083445637 / 4000000000000)) (orderedInterval (-38964560615 / 1000000000000) (-38964533039 / 1000000000000), orderedInterval (44880742566 / 1000000000000) (44880770142 / 1000000000000))) = true
  norm_num [besselStateAtRationalPoint, besselIntervalStepZero,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, besselZeroTransition,
    besselInitial, besselGridStateAt, besselGridStateBlock00, besselGridStateBlock01,
    besselGridStateBlock02, besselGridStateBlock03, besselGridStateBlock04,
    besselGridStateBlock05, besselGridStateBlock06, besselGridStateBlock07,
    besselGridStateBlock08, besselGridStateBlock09, besselGridStateBlock10,
    besselGridStateBlock11, besselGridStateBlock12, besselGridStateBlock13,
    besselGridStateBlock14, besselGridState010, besselGridState014, besselGridState021, besselGridState025, besselGridState027, besselGridState034, besselGridState037, besselGridState040, besselGridState046, besselGridState047, besselGridState050, besselGridState054, besselGridState055, besselGridState058, besselGridState059, besselGridState060, besselGridState067, besselGridState068, besselGridState071, besselGridState073, besselGridState080, besselGridState086, besselGridState092, besselGridState099, besselGridState104, besselGridState106, besselStateSubset, linearInterval, widenInterval,
    rationalErrorInterval, rationalIntervalSubset, orderedInterval, Finset.sum_range_succ,
    IntervalRat.add, IntervalRat.mul, IntervalRat.scale, IntervalRat.singleton]

theorem compactCertificate271_states : ∀ j,
    BesselStateValid (compactCertificate271.point j) (compactCertificate271.state j) :=
  compactCertificate271.statesValid_of_checks3 compactCertificate271_stateChecks0
    compactCertificate271_stateChecks1 compactCertificate271_stateChecks2
    compactCertificate271_stateChecks3 compactCertificate271_stateChecks4
    compactCertificate271_stateChecks5 compactCertificate271_stateChecks6
    compactCertificate271_stateChecks7 compactCertificate271_stateChecks8

theorem compactCertificate271_chunkChecks0_0 :
    compactCertificate271.chunkChecks (0 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 0) <| besselDerivativeNearFromState (291 / 2) 0 (IntervalRat.scale (291 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (64821710916 / 1000000000000) (64821711602 / 1000000000000), orderedInterval (-13395284302 / 1000000000000) (-13395283616 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 0) <| besselDerivativeNearFromState (428698565839191 / 4000000000000) 0 (IntervalRat.scale (291 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (70180632548 / 1000000000000) (70180632549 / 1000000000000), orderedInterval (31526302049 / 1000000000000) (31526302050 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 0) <| besselDerivativeNearFromState (138632308024503 / 800000000000) 0 (IntervalRat.scale (291 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-58194487030 / 1000000000000) (-58194487029 / 1000000000000), orderedInterval (-16776276688 / 1000000000000) (-16776276687 / 1000000000000)))) (orderedInterval (22932085492 / 1000000000000) (22932085775 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 0) <| besselDerivativeNearFromState (125093172322437 / 4000000000000) 0 (IntervalRat.scale (291 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (85059638782 / 1000000000000) (85059638783 / 1000000000000), orderedInterval (113192874996 / 1000000000000) (113192874997 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 0) <| besselDerivativeNearFromState (336017856668289 / 4000000000000) 0 (IntervalRat.scale (291 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (3013810215 / 1000000000000) (3013810228 / 1000000000000), orderedInterval (-87020552079 / 1000000000000) (-87020552066 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 0) <| besselDerivativeNearFromState (912353845636413 / 4000000000000) 0 (IntervalRat.scale (291 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (23593821292 / 1000000000000) (23593822894 / 1000000000000), orderedInterval (-47321634076 / 1000000000000) (-47321632474 / 1000000000000)))) (orderedInterval (-2490073709 / 1000000000000) (-2490073576 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 0) <| besselDerivativeNearFromState (672035713336869 / 4000000000000) 0 (IntervalRat.scale (291 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-46344343566 / 1000000000000) (-46344246968 / 1000000000000), orderedInterval (40652138282 / 1000000000000) (40652234880 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 0) <| besselDerivativeNearFromState (1151544649284537 / 4000000000000) 0 (IntervalRat.scale (291 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-16362997911 / 1000000000000) (-16362997614 / 1000000000000), orderedInterval (44114859474 / 1000000000000) (44114859772 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 0) <| besselDerivativeNearFromState (848222576714283 / 4000000000000) 0 (IntervalRat.scale (291 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-38838365600 / 1000000000000) (-38838319874 / 1000000000000), orderedInterval (38740206187 / 1000000000000) (38740251913 / 1000000000000)))) (orderedInterval (-433946358 / 1000000000000) (-433945235 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate271_chunkChecks0_1 :
    compactCertificate271.chunkChecks (0 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 0) <| besselDerivativeNearFromState (1301391562904709 / 4000000000000) 0 (IntervalRat.scale (291 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-24710920003 / 1000000000000) (-24710916087 / 1000000000000), orderedInterval (36727303684 / 1000000000000) (36727307601 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 0) <| besselDerivativeNearFromState (751358769164061 / 4000000000000) 0 (IntervalRat.scale (291 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (7481360192 / 1000000000000) (7481360193 / 1000000000000), orderedInterval (57714011719 / 1000000000000) (57714011720 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 0) <| besselDerivativeNearFromState (1333299320968449 / 4000000000000) 0 (IntervalRat.scale (291 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (38968402154 / 1000000000000) (38968402155 / 1000000000000), orderedInterval (19724629793 / 1000000000000) (19724629794 / 1000000000000)))) (orderedInterval (10484726594 / 1000000000000) (10484727348 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 0) <| besselDerivativeNearFromState (1245741176687781 / 4000000000000) 0 (IntervalRat.scale (291 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-42182310159 / 1000000000000) (-42182310158 / 1000000000000), orderedInterval (-16204910010 / 1000000000000) (-16204910009 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 0) <| besselDerivativeNearFromState (889019684821173 / 4000000000000) 0 (IntervalRat.scale (291 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (712939029 / 1000000000000) (712939032 / 1000000000000), orderedInterval (-53516708846 / 1000000000000) (-53516708842 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 0) <| besselDerivativeNearFromState (1008053570004867 / 4000000000000) 0 (IntervalRat.scale (291 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (50009955766 / 1000000000000) (50009955789 / 1000000000000), orderedInterval (4914175324 / 1000000000000) (4914175347 / 1000000000000)))) (orderedInterval (575859240 / 1000000000000) (575859258 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 0) <| besselDerivativeNearFromState (840409971802323 / 4000000000000) 0 (IntervalRat.scale (291 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-21465654795 / 1000000000000) (-21465654794 / 1000000000000), orderedInterval (-50636937905 / 1000000000000) (-50636937904 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 0) <| besselDerivativeNearFromState (742527697164783 / 4000000000000) 0 (IntervalRat.scale (291 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-51163148127 / 1000000000000) (-51163148126 / 1000000000000), orderedInterval (-28354284174 / 1000000000000) (-28354284173 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 0) <| besselDerivativeNearFromState (215213468045517 / 800000000000) 0 (IntervalRat.scale (291 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-17826845918 / 1000000000000) (-17826845484 / 1000000000000), orderedInterval (45295420969 / 1000000000000) (45295421402 / 1000000000000)))) (orderedInterval (2223580975 / 1000000000000) (2223581001 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate271_chunkChecks0_2 :
    compactCertificate271.chunkChecks (0 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 0) <| besselDerivativeNearFromState (595291778678199 / 4000000000000) 0 (IntervalRat.scale (291 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-60693295436 / 1000000000000) (-60693290007 / 1000000000000), orderedInterval (24576140958 / 1000000000000) (24576146387 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 0) <| besselDerivativeNearFromState (504635433461439 / 4000000000000) 0 (IntervalRat.scale (291 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (68044792387 / 1000000000000) (68044792388 / 1000000000000), orderedInterval (20127601789 / 1000000000000) (20127601790 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 0) <| besselDerivativeNearFromState (315777423285717 / 4000000000000) 0 (IntervalRat.scale (291 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-83312273026 / 1000000000000) (-83312273025 / 1000000000000), orderedInterval (-32985140430 / 1000000000000) (-32985140429 / 1000000000000)))) (orderedInterval (3140812452 / 1000000000000) (3140813358 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 0) <| besselDerivativeNearFromState (169826148471339 / 4000000000000) 0 (IntervalRat.scale (291 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-82863852009 / 1000000000000) (-82863787598 / 1000000000000), orderedInterval (91132767285 / 1000000000000) (91132831696 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 0) <| besselDerivativeNearFromState (461111028991017 / 4000000000000) 0 (IntervalRat.scale (291 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (13074386017 / 1000000000000) (13074386103 / 1000000000000), orderedInterval (-73211303121 / 1000000000000) (-73211303036 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 0) <| besselDerivativeNearFromState (629607688492809 / 4000000000000) 0 (IntervalRat.scale (291 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (56875273951 / 1000000000000) (56875273952 / 1000000000000), orderedInterval (28275261751 / 1000000000000) (28275261752 / 1000000000000)))) (orderedInterval (-3125383996 / 1000000000000) (-3125382786 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 0) <| besselDerivativeNearFromState (266222576714283 / 4000000000000) 0 (IntervalRat.scale (291 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-95751199824 / 1000000000000) (-95751199822 / 1000000000000), orderedInterval (-19197691530 / 1000000000000) (-19197691528 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 0) <| besselDerivativeNearFromState (1082179994108043 / 4000000000000) 0 (IntervalRat.scale (291 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (44335608731 / 1000000000000) (44335608732 / 1000000000000), orderedInterval (19601871939 / 1000000000000) (19601871940 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 0) <| besselDerivativeNearFromState (722846083445637 / 4000000000000) 0 (IntervalRat.scale (291 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-38964560615 / 1000000000000) (-38964533039 / 1000000000000), orderedInterval (44880742566 / 1000000000000) (44880770142 / 1000000000000)))) (orderedInterval (3124563016 / 1000000000000) (3124568231 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate271_chunkChecks0 :
    compactCertificate271.chunkChecks (0 : Fin 5) 0 9 = true :=
  compactCertificate271.chunkChecks_nine_of_three (0 : Fin 5) compactCertificate271_chunkChecks0_0
    compactCertificate271_chunkChecks0_1 compactCertificate271_chunkChecks0_2

theorem compactCertificate271_chunkChecks1_0 :
    compactCertificate271.chunkChecks (1 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 1) <| besselDerivativeNearFromState (291 / 2) 1 (IntervalRat.scale (291 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (64821710916 / 1000000000000) (64821711602 / 1000000000000), orderedInterval (-13395284302 / 1000000000000) (-13395283616 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 1) <| besselDerivativeNearFromState (428698565839191 / 4000000000000) 1 (IntervalRat.scale (291 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (70180632548 / 1000000000000) (70180632549 / 1000000000000), orderedInterval (31526302049 / 1000000000000) (31526302050 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 1) <| besselDerivativeNearFromState (138632308024503 / 800000000000) 1 (IntervalRat.scale (291 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-58194487030 / 1000000000000) (-58194487029 / 1000000000000), orderedInterval (-16776276688 / 1000000000000) (-16776276687 / 1000000000000)))) (orderedInterval (-6265516973 / 1000000000000) (-6265516689 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 1) <| besselDerivativeNearFromState (125093172322437 / 4000000000000) 1 (IntervalRat.scale (291 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (85059638782 / 1000000000000) (85059638783 / 1000000000000), orderedInterval (113192874996 / 1000000000000) (113192874997 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 1) <| besselDerivativeNearFromState (336017856668289 / 4000000000000) 1 (IntervalRat.scale (291 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (3013810215 / 1000000000000) (3013810228 / 1000000000000), orderedInterval (-87020552079 / 1000000000000) (-87020552066 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 1) <| besselDerivativeNearFromState (912353845636413 / 4000000000000) 1 (IntervalRat.scale (291 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (23593821292 / 1000000000000) (23593822894 / 1000000000000), orderedInterval (-47321634076 / 1000000000000) (-47321632474 / 1000000000000)))) (orderedInterval (3175235253 / 1000000000000) (3175235453 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 1) <| besselDerivativeNearFromState (672035713336869 / 4000000000000) 1 (IntervalRat.scale (291 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-46344343566 / 1000000000000) (-46344246968 / 1000000000000), orderedInterval (40652138282 / 1000000000000) (40652234880 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 1) <| besselDerivativeNearFromState (1151544649284537 / 4000000000000) 1 (IntervalRat.scale (291 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-16362997911 / 1000000000000) (-16362997614 / 1000000000000), orderedInterval (44114859474 / 1000000000000) (44114859772 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 1) <| besselDerivativeNearFromState (848222576714283 / 4000000000000) 1 (IntervalRat.scale (291 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-38838365600 / 1000000000000) (-38838319874 / 1000000000000), orderedInterval (38740206187 / 1000000000000) (38740251913 / 1000000000000)))) (orderedInterval (-1327686135 / 1000000000000) (-1327684491 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate271_chunkChecks1_1 :
    compactCertificate271.chunkChecks (1 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 1) <| besselDerivativeNearFromState (1301391562904709 / 4000000000000) 1 (IntervalRat.scale (291 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-24710920003 / 1000000000000) (-24710916087 / 1000000000000), orderedInterval (36727303684 / 1000000000000) (36727307601 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 1) <| besselDerivativeNearFromState (751358769164061 / 4000000000000) 1 (IntervalRat.scale (291 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (7481360192 / 1000000000000) (7481360193 / 1000000000000), orderedInterval (57714011719 / 1000000000000) (57714011720 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 1) <| besselDerivativeNearFromState (1333299320968449 / 4000000000000) 1 (IntervalRat.scale (291 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (38968402154 / 1000000000000) (38968402155 / 1000000000000), orderedInterval (19724629793 / 1000000000000) (19724629794 / 1000000000000)))) (orderedInterval (-2648514639 / 1000000000000) (-2648512962 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 1) <| besselDerivativeNearFromState (1245741176687781 / 4000000000000) 1 (IntervalRat.scale (291 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-42182310159 / 1000000000000) (-42182310158 / 1000000000000), orderedInterval (-16204910010 / 1000000000000) (-16204910009 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 1) <| besselDerivativeNearFromState (889019684821173 / 4000000000000) 1 (IntervalRat.scale (291 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (712939029 / 1000000000000) (712939032 / 1000000000000), orderedInterval (-53516708846 / 1000000000000) (-53516708842 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 1) <| besselDerivativeNearFromState (1008053570004867 / 4000000000000) 1 (IntervalRat.scale (291 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (50009955766 / 1000000000000) (50009955789 / 1000000000000), orderedInterval (4914175324 / 1000000000000) (4914175347 / 1000000000000)))) (orderedInterval (-7147225068 / 1000000000000) (-7147225039 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 1) <| besselDerivativeNearFromState (840409971802323 / 4000000000000) 1 (IntervalRat.scale (291 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-21465654795 / 1000000000000) (-21465654794 / 1000000000000), orderedInterval (-50636937905 / 1000000000000) (-50636937904 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 1) <| besselDerivativeNearFromState (742527697164783 / 4000000000000) 1 (IntervalRat.scale (291 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-51163148127 / 1000000000000) (-51163148126 / 1000000000000), orderedInterval (-28354284174 / 1000000000000) (-28354284173 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 1) <| besselDerivativeNearFromState (215213468045517 / 800000000000) 1 (IntervalRat.scale (291 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-17826845918 / 1000000000000) (-17826845484 / 1000000000000), orderedInterval (45295420969 / 1000000000000) (45295421402 / 1000000000000)))) (orderedInterval (3370071031 / 1000000000000) (3370071072 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate271_chunkChecks1_2 :
    compactCertificate271.chunkChecks (1 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 1) <| besselDerivativeNearFromState (595291778678199 / 4000000000000) 1 (IntervalRat.scale (291 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-60693295436 / 1000000000000) (-60693290007 / 1000000000000), orderedInterval (24576140958 / 1000000000000) (24576146387 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 1) <| besselDerivativeNearFromState (504635433461439 / 4000000000000) 1 (IntervalRat.scale (291 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (68044792387 / 1000000000000) (68044792388 / 1000000000000), orderedInterval (20127601789 / 1000000000000) (20127601790 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 1) <| besselDerivativeNearFromState (315777423285717 / 4000000000000) 1 (IntervalRat.scale (291 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-83312273026 / 1000000000000) (-83312273025 / 1000000000000), orderedInterval (-32985140430 / 1000000000000) (-32985140429 / 1000000000000)))) (orderedInterval (-5589705948 / 1000000000000) (-5589705026 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 1) <| besselDerivativeNearFromState (169826148471339 / 4000000000000) 1 (IntervalRat.scale (291 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-82863852009 / 1000000000000) (-82863787598 / 1000000000000), orderedInterval (91132767285 / 1000000000000) (91132831696 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 1) <| besselDerivativeNearFromState (461111028991017 / 4000000000000) 1 (IntervalRat.scale (291 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (13074386017 / 1000000000000) (13074386103 / 1000000000000), orderedInterval (-73211303121 / 1000000000000) (-73211303036 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 1) <| besselDerivativeNearFromState (629607688492809 / 4000000000000) 1 (IntervalRat.scale (291 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (56875273951 / 1000000000000) (56875273952 / 1000000000000), orderedInterval (28275261751 / 1000000000000) (28275261752 / 1000000000000)))) (orderedInterval (-1519337308 / 1000000000000) (-1519336943 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 1) <| besselDerivativeNearFromState (266222576714283 / 4000000000000) 1 (IntervalRat.scale (291 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-95751199824 / 1000000000000) (-95751199822 / 1000000000000), orderedInterval (-19197691530 / 1000000000000) (-19197691528 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 1) <| besselDerivativeNearFromState (1082179994108043 / 4000000000000) 1 (IntervalRat.scale (291 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (44335608731 / 1000000000000) (44335608732 / 1000000000000), orderedInterval (19601871939 / 1000000000000) (19601871940 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 1) <| besselDerivativeNearFromState (722846083445637 / 4000000000000) 1 (IntervalRat.scale (291 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-38964560615 / 1000000000000) (-38964533039 / 1000000000000), orderedInterval (44880742566 / 1000000000000) (44880770142 / 1000000000000)))) (orderedInterval (-13478564847 / 1000000000000) (-13478558363 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate271_chunkChecks1 :
    compactCertificate271.chunkChecks (1 : Fin 5) 0 9 = true :=
  compactCertificate271.chunkChecks_nine_of_three (1 : Fin 5) compactCertificate271_chunkChecks1_0
    compactCertificate271_chunkChecks1_1 compactCertificate271_chunkChecks1_2

theorem compactCertificate271_chunkChecks2_0 :
    compactCertificate271.chunkChecks (2 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 2) <| besselDerivativeNearFromState (291 / 2) 2 (IntervalRat.scale (291 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (64821710916 / 1000000000000) (64821711602 / 1000000000000), orderedInterval (-13395284302 / 1000000000000) (-13395283616 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 2) <| besselDerivativeNearFromState (428698565839191 / 4000000000000) 2 (IntervalRat.scale (291 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (70180632548 / 1000000000000) (70180632549 / 1000000000000), orderedInterval (31526302049 / 1000000000000) (31526302050 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 2) <| besselDerivativeNearFromState (138632308024503 / 800000000000) 2 (IntervalRat.scale (291 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-58194487030 / 1000000000000) (-58194487029 / 1000000000000), orderedInterval (-16776276688 / 1000000000000) (-16776276687 / 1000000000000)))) (orderedInterval (-21160818340 / 1000000000000) (-21160818052 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 2) <| besselDerivativeNearFromState (125093172322437 / 4000000000000) 2 (IntervalRat.scale (291 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (85059638782 / 1000000000000) (85059638783 / 1000000000000), orderedInterval (113192874996 / 1000000000000) (113192874997 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 2) <| besselDerivativeNearFromState (336017856668289 / 4000000000000) 2 (IntervalRat.scale (291 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (3013810215 / 1000000000000) (3013810228 / 1000000000000), orderedInterval (-87020552079 / 1000000000000) (-87020552066 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 2) <| besselDerivativeNearFromState (912353845636413 / 4000000000000) 2 (IntervalRat.scale (291 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (23593821292 / 1000000000000) (23593822894 / 1000000000000), orderedInterval (-47321634076 / 1000000000000) (-47321632474 / 1000000000000)))) (orderedInterval (4105914472 / 1000000000000) (4105914782 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 2) <| besselDerivativeNearFromState (672035713336869 / 4000000000000) 2 (IntervalRat.scale (291 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-46344343566 / 1000000000000) (-46344246968 / 1000000000000), orderedInterval (40652138282 / 1000000000000) (40652234880 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 2) <| besselDerivativeNearFromState (1151544649284537 / 4000000000000) 2 (IntervalRat.scale (291 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-16362997911 / 1000000000000) (-16362997614 / 1000000000000), orderedInterval (44114859474 / 1000000000000) (44114859772 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 2) <| besselDerivativeNearFromState (848222576714283 / 4000000000000) 2 (IntervalRat.scale (291 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-38838365600 / 1000000000000) (-38838319874 / 1000000000000), orderedInterval (38740206187 / 1000000000000) (38740251913 / 1000000000000)))) (orderedInterval (27067973 / 1000000000000) (27070394 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate271_chunkChecks2_1 :
    compactCertificate271.chunkChecks (2 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 2) <| besselDerivativeNearFromState (1301391562904709 / 4000000000000) 2 (IntervalRat.scale (291 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-24710920003 / 1000000000000) (-24710916087 / 1000000000000), orderedInterval (36727303684 / 1000000000000) (36727307601 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 2) <| besselDerivativeNearFromState (751358769164061 / 4000000000000) 2 (IntervalRat.scale (291 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (7481360192 / 1000000000000) (7481360193 / 1000000000000), orderedInterval (57714011719 / 1000000000000) (57714011720 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 2) <| besselDerivativeNearFromState (1333299320968449 / 4000000000000) 2 (IntervalRat.scale (291 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (38968402154 / 1000000000000) (38968402155 / 1000000000000), orderedInterval (19724629793 / 1000000000000) (19724629794 / 1000000000000)))) (orderedInterval (-51932599891 / 1000000000000) (-51932596144 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 2) <| besselDerivativeNearFromState (1245741176687781 / 4000000000000) 2 (IntervalRat.scale (291 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-42182310159 / 1000000000000) (-42182310158 / 1000000000000), orderedInterval (-16204910010 / 1000000000000) (-16204910009 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 2) <| besselDerivativeNearFromState (889019684821173 / 4000000000000) 2 (IntervalRat.scale (291 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (712939029 / 1000000000000) (712939032 / 1000000000000), orderedInterval (-53516708846 / 1000000000000) (-53516708842 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 2) <| besselDerivativeNearFromState (1008053570004867 / 4000000000000) 2 (IntervalRat.scale (291 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (50009955766 / 1000000000000) (50009955789 / 1000000000000), orderedInterval (4914175324 / 1000000000000) (4914175347 / 1000000000000)))) (orderedInterval (-2837872074 / 1000000000000) (-2837872025 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 2) <| besselDerivativeNearFromState (840409971802323 / 4000000000000) 2 (IntervalRat.scale (291 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-21465654795 / 1000000000000) (-21465654794 / 1000000000000), orderedInterval (-50636937905 / 1000000000000) (-50636937904 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 2) <| besselDerivativeNearFromState (742527697164783 / 4000000000000) 2 (IntervalRat.scale (291 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-51163148127 / 1000000000000) (-51163148126 / 1000000000000), orderedInterval (-28354284174 / 1000000000000) (-28354284173 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 2) <| besselDerivativeNearFromState (215213468045517 / 800000000000) 2 (IntervalRat.scale (291 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-17826845918 / 1000000000000) (-17826845484 / 1000000000000), orderedInterval (45295420969 / 1000000000000) (45295421402 / 1000000000000)))) (orderedInterval (-2711769570 / 1000000000000) (-2711769501 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate271_chunkChecks2_2 :
    compactCertificate271.chunkChecks (2 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 2) <| besselDerivativeNearFromState (595291778678199 / 4000000000000) 2 (IntervalRat.scale (291 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-60693295436 / 1000000000000) (-60693290007 / 1000000000000), orderedInterval (24576140958 / 1000000000000) (24576146387 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 2) <| besselDerivativeNearFromState (504635433461439 / 4000000000000) 2 (IntervalRat.scale (291 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (68044792387 / 1000000000000) (68044792388 / 1000000000000), orderedInterval (20127601789 / 1000000000000) (20127601790 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 2) <| besselDerivativeNearFromState (315777423285717 / 4000000000000) 2 (IntervalRat.scale (291 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-83312273026 / 1000000000000) (-83312273025 / 1000000000000), orderedInterval (-32985140430 / 1000000000000) (-32985140429 / 1000000000000)))) (orderedInterval (-6420376603 / 1000000000000) (-6420375656 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 2) <| besselDerivativeNearFromState (169826148471339 / 4000000000000) 2 (IntervalRat.scale (291 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-82863852009 / 1000000000000) (-82863787598 / 1000000000000), orderedInterval (91132767285 / 1000000000000) (91132831696 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 2) <| besselDerivativeNearFromState (461111028991017 / 4000000000000) 2 (IntervalRat.scale (291 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (13074386017 / 1000000000000) (13074386103 / 1000000000000), orderedInterval (-73211303121 / 1000000000000) (-73211303036 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 2) <| besselDerivativeNearFromState (629607688492809 / 4000000000000) 2 (IntervalRat.scale (291 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (56875273951 / 1000000000000) (56875273952 / 1000000000000), orderedInterval (28275261751 / 1000000000000) (28275261752 / 1000000000000)))) (orderedInterval (5167486572 / 1000000000000) (5167486694 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 2) <| besselDerivativeNearFromState (266222576714283 / 4000000000000) 2 (IntervalRat.scale (291 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-95751199824 / 1000000000000) (-95751199822 / 1000000000000), orderedInterval (-19197691530 / 1000000000000) (-19197691528 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 2) <| besselDerivativeNearFromState (1082179994108043 / 4000000000000) 2 (IntervalRat.scale (291 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (44335608731 / 1000000000000) (44335608732 / 1000000000000), orderedInterval (19601871939 / 1000000000000) (19601871940 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 2) <| besselDerivativeNearFromState (722846083445637 / 4000000000000) 2 (IntervalRat.scale (291 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-38964560615 / 1000000000000) (-38964533039 / 1000000000000), orderedInterval (44880742566 / 1000000000000) (44880770142 / 1000000000000)))) (orderedInterval (1413839452 / 1000000000000) (1413847562 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate271_chunkChecks2 :
    compactCertificate271.chunkChecks (2 : Fin 5) 0 9 = true :=
  compactCertificate271.chunkChecks_nine_of_three (2 : Fin 5) compactCertificate271_chunkChecks2_0
    compactCertificate271_chunkChecks2_1 compactCertificate271_chunkChecks2_2

theorem compactCertificate271_chunkChecks3_0 :
    compactCertificate271.chunkChecks (3 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 3) <| besselDerivativeNearFromState (291 / 2) 3 (IntervalRat.scale (291 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (64821710916 / 1000000000000) (64821711602 / 1000000000000), orderedInterval (-13395284302 / 1000000000000) (-13395283616 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 3) <| besselDerivativeNearFromState (428698565839191 / 4000000000000) 3 (IntervalRat.scale (291 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (70180632548 / 1000000000000) (70180632549 / 1000000000000), orderedInterval (31526302049 / 1000000000000) (31526302050 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 3) <| besselDerivativeNearFromState (138632308024503 / 800000000000) 3 (IntervalRat.scale (291 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-58194487030 / 1000000000000) (-58194487029 / 1000000000000), orderedInterval (-16776276688 / 1000000000000) (-16776276687 / 1000000000000)))) (orderedInterval (7000294935 / 1000000000000) (7000295225 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 3) <| besselDerivativeNearFromState (125093172322437 / 4000000000000) 3 (IntervalRat.scale (291 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (85059638782 / 1000000000000) (85059638783 / 1000000000000), orderedInterval (113192874996 / 1000000000000) (113192874997 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 3) <| besselDerivativeNearFromState (336017856668289 / 4000000000000) 3 (IntervalRat.scale (291 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (3013810215 / 1000000000000) (3013810228 / 1000000000000), orderedInterval (-87020552079 / 1000000000000) (-87020552066 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 3) <| besselDerivativeNearFromState (912353845636413 / 4000000000000) 3 (IntervalRat.scale (291 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (23593821292 / 1000000000000) (23593822894 / 1000000000000), orderedInterval (-47321634076 / 1000000000000) (-47321632474 / 1000000000000)))) (orderedInterval (-12363872315 / 1000000000000) (-12363871833 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 3) <| besselDerivativeNearFromState (672035713336869 / 4000000000000) 3 (IntervalRat.scale (291 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-46344343566 / 1000000000000) (-46344246968 / 1000000000000), orderedInterval (40652138282 / 1000000000000) (40652234880 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 3) <| besselDerivativeNearFromState (1151544649284537 / 4000000000000) 3 (IntervalRat.scale (291 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-16362997911 / 1000000000000) (-16362997614 / 1000000000000), orderedInterval (44114859474 / 1000000000000) (44114859772 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 3) <| besselDerivativeNearFromState (848222576714283 / 4000000000000) 3 (IntervalRat.scale (291 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-38838365600 / 1000000000000) (-38838319874 / 1000000000000), orderedInterval (38740206187 / 1000000000000) (38740251913 / 1000000000000)))) (orderedInterval (7641030408 / 1000000000000) (7641033963 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate271_chunkChecks3_1 :
    compactCertificate271.chunkChecks (3 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 3) <| besselDerivativeNearFromState (1301391562904709 / 4000000000000) 3 (IntervalRat.scale (291 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-24710920003 / 1000000000000) (-24710916087 / 1000000000000), orderedInterval (36727303684 / 1000000000000) (36727307601 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 3) <| besselDerivativeNearFromState (751358769164061 / 4000000000000) 3 (IntervalRat.scale (291 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (7481360192 / 1000000000000) (7481360193 / 1000000000000), orderedInterval (57714011719 / 1000000000000) (57714011720 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 3) <| besselDerivativeNearFromState (1333299320968449 / 4000000000000) 3 (IntervalRat.scale (291 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (38968402154 / 1000000000000) (38968402155 / 1000000000000), orderedInterval (19724629793 / 1000000000000) (19724629794 / 1000000000000)))) (orderedInterval (30406655589 / 1000000000000) (30406663958 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 3) <| besselDerivativeNearFromState (1245741176687781 / 4000000000000) 3 (IntervalRat.scale (291 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-42182310159 / 1000000000000) (-42182310158 / 1000000000000), orderedInterval (-16204910010 / 1000000000000) (-16204910009 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 3) <| besselDerivativeNearFromState (889019684821173 / 4000000000000) 3 (IntervalRat.scale (291 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (712939029 / 1000000000000) (712939032 / 1000000000000), orderedInterval (-53516708846 / 1000000000000) (-53516708842 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 3) <| besselDerivativeNearFromState (1008053570004867 / 4000000000000) 3 (IntervalRat.scale (291 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (50009955766 / 1000000000000) (50009955789 / 1000000000000), orderedInterval (4914175324 / 1000000000000) (4914175347 / 1000000000000)))) (orderedInterval (15316958693 / 1000000000000) (15316958774 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 3) <| besselDerivativeNearFromState (840409971802323 / 4000000000000) 3 (IntervalRat.scale (291 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-21465654795 / 1000000000000) (-21465654794 / 1000000000000), orderedInterval (-50636937905 / 1000000000000) (-50636937904 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 3) <| besselDerivativeNearFromState (742527697164783 / 4000000000000) 3 (IntervalRat.scale (291 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-51163148127 / 1000000000000) (-51163148126 / 1000000000000), orderedInterval (-28354284174 / 1000000000000) (-28354284173 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 3) <| besselDerivativeNearFromState (215213468045517 / 800000000000) 3 (IntervalRat.scale (291 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-17826845918 / 1000000000000) (-17826845484 / 1000000000000), orderedInterval (45295420969 / 1000000000000) (45295421402 / 1000000000000)))) (orderedInterval (-8920354204 / 1000000000000) (-8920354086 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate271_chunkChecks3_2 :
    compactCertificate271.chunkChecks (3 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 3) <| besselDerivativeNearFromState (595291778678199 / 4000000000000) 3 (IntervalRat.scale (291 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-60693295436 / 1000000000000) (-60693290007 / 1000000000000), orderedInterval (24576140958 / 1000000000000) (24576146387 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 3) <| besselDerivativeNearFromState (504635433461439 / 4000000000000) 3 (IntervalRat.scale (291 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (68044792387 / 1000000000000) (68044792388 / 1000000000000), orderedInterval (20127601789 / 1000000000000) (20127601790 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 3) <| besselDerivativeNearFromState (315777423285717 / 4000000000000) 3 (IntervalRat.scale (291 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-83312273026 / 1000000000000) (-83312273025 / 1000000000000), orderedInterval (-32985140430 / 1000000000000) (-32985140429 / 1000000000000)))) (orderedInterval (5162976166 / 1000000000000) (5162977134 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 3) <| besselDerivativeNearFromState (169826148471339 / 4000000000000) 3 (IntervalRat.scale (291 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-82863852009 / 1000000000000) (-82863787598 / 1000000000000), orderedInterval (91132767285 / 1000000000000) (91132831696 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 3) <| besselDerivativeNearFromState (461111028991017 / 4000000000000) 3 (IntervalRat.scale (291 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (13074386017 / 1000000000000) (13074386103 / 1000000000000), orderedInterval (-73211303121 / 1000000000000) (-73211303036 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 3) <| besselDerivativeNearFromState (629607688492809 / 4000000000000) 3 (IntervalRat.scale (291 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (56875273951 / 1000000000000) (56875273952 / 1000000000000), orderedInterval (28275261751 / 1000000000000) (28275261752 / 1000000000000)))) (orderedInterval (1923632466 / 1000000000000) (1923632514 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 3) <| besselDerivativeNearFromState (266222576714283 / 4000000000000) 3 (IntervalRat.scale (291 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-95751199824 / 1000000000000) (-95751199822 / 1000000000000), orderedInterval (-19197691530 / 1000000000000) (-19197691528 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 3) <| besselDerivativeNearFromState (1082179994108043 / 4000000000000) 3 (IntervalRat.scale (291 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (44335608731 / 1000000000000) (44335608732 / 1000000000000), orderedInterval (19601871939 / 1000000000000) (19601871940 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 3) <| besselDerivativeNearFromState (722846083445637 / 4000000000000) 3 (IntervalRat.scale (291 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-38964560615 / 1000000000000) (-38964533039 / 1000000000000), orderedInterval (44880742566 / 1000000000000) (44880770142 / 1000000000000)))) (orderedInterval (26391967773 / 1000000000000) (26391977870 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate271_chunkChecks3 :
    compactCertificate271.chunkChecks (3 : Fin 5) 0 9 = true :=
  compactCertificate271.chunkChecks_nine_of_three (3 : Fin 5) compactCertificate271_chunkChecks3_0
    compactCertificate271_chunkChecks3_1 compactCertificate271_chunkChecks3_2

theorem compactCertificate271_chunkChecks4_0 :
    compactCertificate271.chunkChecks (4 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 4) <| besselDerivativeNearFromState (291 / 2) 4 (IntervalRat.scale (291 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (64821710916 / 1000000000000) (64821711602 / 1000000000000), orderedInterval (-13395284302 / 1000000000000) (-13395283616 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 4) <| besselDerivativeNearFromState (428698565839191 / 4000000000000) 4 (IntervalRat.scale (291 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (70180632548 / 1000000000000) (70180632549 / 1000000000000), orderedInterval (31526302049 / 1000000000000) (31526302050 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 4) <| besselDerivativeNearFromState (138632308024503 / 800000000000) 4 (IntervalRat.scale (291 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-58194487030 / 1000000000000) (-58194487029 / 1000000000000), orderedInterval (-16776276688 / 1000000000000) (-16776276687 / 1000000000000)))) (orderedInterval (18917247816 / 1000000000000) (18917248111 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 4) <| besselDerivativeNearFromState (125093172322437 / 4000000000000) 4 (IntervalRat.scale (291 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (85059638782 / 1000000000000) (85059638783 / 1000000000000), orderedInterval (113192874996 / 1000000000000) (113192874997 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 4) <| besselDerivativeNearFromState (336017856668289 / 4000000000000) 4 (IntervalRat.scale (291 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (3013810215 / 1000000000000) (3013810228 / 1000000000000), orderedInterval (-87020552079 / 1000000000000) (-87020552066 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 4) <| besselDerivativeNearFromState (912353845636413 / 4000000000000) 4 (IntervalRat.scale (291 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (23593821292 / 1000000000000) (23593822894 / 1000000000000), orderedInterval (-47321634076 / 1000000000000) (-47321632474 / 1000000000000)))) (orderedInterval (-9948584871 / 1000000000000) (-9948584113 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 4) <| besselDerivativeNearFromState (672035713336869 / 4000000000000) 4 (IntervalRat.scale (291 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-46344343566 / 1000000000000) (-46344246968 / 1000000000000), orderedInterval (40652138282 / 1000000000000) (40652234880 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 4) <| besselDerivativeNearFromState (1151544649284537 / 4000000000000) 4 (IntervalRat.scale (291 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-16362997911 / 1000000000000) (-16362997614 / 1000000000000), orderedInterval (44114859474 / 1000000000000) (44114859772 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 4) <| besselDerivativeNearFromState (848222576714283 / 4000000000000) 4 (IntervalRat.scale (291 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-38838365600 / 1000000000000) (-38838319874 / 1000000000000), orderedInterval (38740206187 / 1000000000000) (38740251913 / 1000000000000)))) (orderedInterval (3395087480 / 1000000000000) (3395092739 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate271_chunkChecks4_1 :
    compactCertificate271.chunkChecks (4 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 4) <| besselDerivativeNearFromState (1301391562904709 / 4000000000000) 4 (IntervalRat.scale (291 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-24710920003 / 1000000000000) (-24710916087 / 1000000000000), orderedInterval (36727303684 / 1000000000000) (36727307601 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 4) <| besselDerivativeNearFromState (751358769164061 / 4000000000000) 4 (IntervalRat.scale (291 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (7481360192 / 1000000000000) (7481360193 / 1000000000000), orderedInterval (57714011719 / 1000000000000) (57714011720 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 4) <| besselDerivativeNearFromState (1333299320968449 / 4000000000000) 4 (IntervalRat.scale (291 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (38968402154 / 1000000000000) (38968402155 / 1000000000000), orderedInterval (19724629793 / 1000000000000) (19724629794 / 1000000000000)))) (orderedInterval (263469603275 / 1000000000000) (263469622029 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 4) <| besselDerivativeNearFromState (1245741176687781 / 4000000000000) 4 (IntervalRat.scale (291 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-42182310159 / 1000000000000) (-42182310158 / 1000000000000), orderedInterval (-16204910010 / 1000000000000) (-16204910009 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 4) <| besselDerivativeNearFromState (889019684821173 / 4000000000000) 4 (IntervalRat.scale (291 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (712939029 / 1000000000000) (712939032 / 1000000000000), orderedInterval (-53516708846 / 1000000000000) (-53516708842 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 4) <| besselDerivativeNearFromState (1008053570004867 / 4000000000000) 4 (IntervalRat.scale (291 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (50009955766 / 1000000000000) (50009955789 / 1000000000000), orderedInterval (4914175324 / 1000000000000) (4914175347 / 1000000000000)))) (orderedInterval (13863241486 / 1000000000000) (13863241626 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 4) <| besselDerivativeNearFromState (840409971802323 / 4000000000000) 4 (IntervalRat.scale (291 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-21465654795 / 1000000000000) (-21465654794 / 1000000000000), orderedInterval (-50636937905 / 1000000000000) (-50636937904 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 4) <| besselDerivativeNearFromState (742527697164783 / 4000000000000) 4 (IntervalRat.scale (291 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-51163148127 / 1000000000000) (-51163148126 / 1000000000000), orderedInterval (-28354284174 / 1000000000000) (-28354284173 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 4) <| besselDerivativeNearFromState (215213468045517 / 800000000000) 4 (IntervalRat.scale (291 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-17826845918 / 1000000000000) (-17826845484 / 1000000000000), orderedInterval (45295420969 / 1000000000000) (45295421402 / 1000000000000)))) (orderedInterval (1468193053 / 1000000000000) (1468193258 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate271_chunkChecks4_2 :
    compactCertificate271.chunkChecks (4 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 4) <| besselDerivativeNearFromState (595291778678199 / 4000000000000) 4 (IntervalRat.scale (291 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-60693295436 / 1000000000000) (-60693290007 / 1000000000000), orderedInterval (24576140958 / 1000000000000) (24576146387 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 4) <| besselDerivativeNearFromState (504635433461439 / 4000000000000) 4 (IntervalRat.scale (291 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (68044792387 / 1000000000000) (68044792388 / 1000000000000), orderedInterval (20127601789 / 1000000000000) (20127601790 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 4) <| besselDerivativeNearFromState (315777423285717 / 4000000000000) 4 (IntervalRat.scale (291 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-83312273026 / 1000000000000) (-83312273025 / 1000000000000), orderedInterval (-32985140430 / 1000000000000) (-32985140429 / 1000000000000)))) (orderedInterval (8138574324 / 1000000000000) (8138575318 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 4) <| besselDerivativeNearFromState (169826148471339 / 4000000000000) 4 (IntervalRat.scale (291 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-82863852009 / 1000000000000) (-82863787598 / 1000000000000), orderedInterval (91132767285 / 1000000000000) (91132831696 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 4) <| besselDerivativeNearFromState (461111028991017 / 4000000000000) 4 (IntervalRat.scale (291 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (13074386017 / 1000000000000) (13074386103 / 1000000000000), orderedInterval (-73211303121 / 1000000000000) (-73211303036 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 4) <| besselDerivativeNearFromState (629607688492809 / 4000000000000) 4 (IntervalRat.scale (291 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (56875273951 / 1000000000000) (56875273952 / 1000000000000), orderedInterval (28275261751 / 1000000000000) (28275261752 / 1000000000000)))) (orderedInterval (-6101793658 / 1000000000000) (-6101793630 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 4) <| besselDerivativeNearFromState (266222576714283 / 4000000000000) 4 (IntervalRat.scale (291 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-95751199824 / 1000000000000) (-95751199822 / 1000000000000), orderedInterval (-19197691530 / 1000000000000) (-19197691528 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 4) <| besselDerivativeNearFromState (1082179994108043 / 4000000000000) 4 (IntervalRat.scale (291 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (44335608731 / 1000000000000) (44335608732 / 1000000000000), orderedInterval (19601871939 / 1000000000000) (19601871940 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 4) <| besselDerivativeNearFromState (722846083445637 / 4000000000000) 4 (IntervalRat.scale (291 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-38964560615 / 1000000000000) (-38964533039 / 1000000000000), orderedInterval (44880742566 / 1000000000000) (44880770142 / 1000000000000)))) (orderedInterval (-26132988335 / 1000000000000) (-26132975680 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate271_chunkChecks4 :
    compactCertificate271.chunkChecks (4 : Fin 5) 0 9 = true :=
  compactCertificate271.chunkChecks_nine_of_three (4 : Fin 5) compactCertificate271_chunkChecks4_0
    compactCertificate271_chunkChecks4_1 compactCertificate271_chunkChecks4_2

theorem compactCertificate271_chunks :
    ∀ r : Fin 5, ∀ b, compactCertificate271.chunkCheck r b = true :=
  compactCertificate271.chunkChecks_all (by
    intro r
    fin_cases r
    · exact compactCertificate271_chunkChecks0
    · exact compactCertificate271_chunkChecks1
    · exact compactCertificate271_chunkChecks2
    · exact compactCertificate271_chunkChecks3
    · exact compactCertificate271_chunkChecks4)

theorem compactCertificate271_coefficient0 :
    compactCertificate271.coefficientCheck (0 : Fin 5) = true := by
  norm_num [CompactCertificate.coefficientCheck, intervalFinSumHull,
    compactCertificate271, rationalIntervalSubset, orderedInterval, Fin.sum_univ_succ]

theorem compactCertificate271_coefficient1 :
    compactCertificate271.coefficientCheck (1 : Fin 5) = true := by
  norm_num [CompactCertificate.coefficientCheck, intervalFinSumHull,
    compactCertificate271, rationalIntervalSubset, orderedInterval, Fin.sum_univ_succ]

theorem compactCertificate271_coefficient2 :
    compactCertificate271.coefficientCheck (2 : Fin 5) = true := by
  norm_num [CompactCertificate.coefficientCheck, intervalFinSumHull,
    compactCertificate271, rationalIntervalSubset, orderedInterval, Fin.sum_univ_succ]

theorem compactCertificate271_coefficient3 :
    compactCertificate271.coefficientCheck (3 : Fin 5) = true := by
  norm_num [CompactCertificate.coefficientCheck, intervalFinSumHull,
    compactCertificate271, rationalIntervalSubset, orderedInterval, Fin.sum_univ_succ]

theorem compactCertificate271_coefficient4 :
    compactCertificate271.coefficientCheck (4 : Fin 5) = true := by
  norm_num [CompactCertificate.coefficientCheck, intervalFinSumHull,
    compactCertificate271, rationalIntervalSubset, orderedInterval, Fin.sum_univ_succ]

theorem compactCertificate271_coefficients : ∀ r : Fin 5,
    compactCertificate271.coefficientCheck r = true := by
  intro r
  fin_cases r
  · exact compactCertificate271_coefficient0
  · exact compactCertificate271_coefficient1
  · exact compactCertificate271_coefficient2
  · exact compactCertificate271_coefficient3
  · exact compactCertificate271_coefficient4

theorem compactCertificate271_lower : (1 : ℚ) ≤ compactCertificate271.output.lo := by
  norm_num [CompactCertificate.output, CompactCertificate.interval,
    CompactCertificate.coefficientTargetNat, compactCertificate271, dualConstant,
    intervalTaylorSum, intervalPow, intervalSub, intervalMaxAbs, widenInterval,
    rationalErrorInterval, orderedInterval, IntervalRat.add, IntervalRat.mul, IntervalRat.scale,
    IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4]

theorem compactCertificate271_proves {t : ℝ} (ht : t ∈ compactCertificate271.interval) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t :=
  compactCertificate271.proves compactCertificate271_states compactCertificate271_chunks
    compactCertificate271_coefficients compactCertificate271_lower ht

end Erdos232
