/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, OpenAI Codex
-/
import ErdosProblems.Erdos232.CompactBase

open LeanCert.Core
namespace Erdos232

def compactCertificate263 : CompactCertificate where
  left := 137
  right := 138
  center := 275 / 2
  grid := fun i =>
    match i.val with
    | 0 => 44
    | 1 => 32
    | 2 => 52
    | 3 => 9
    | 4 => 25
    | 5 => 69
    | 6 => 51
    | 7 => 87
    | 8 => 64
    | 9 => 98
    | 10 => 57
    | 11 => 100
    | 12 => 94
    | 13 => 67
    | 14 => 76
    | 15 => 63
    | 16 => 56
    | 17 => 81
    | 18 => 45
    | 19 => 38
    | 20 => 24
    | 21 => 13
    | 22 => 35
    | 23 => 47
    | 24 => 20
    | 25 => 81
    | _ => 54
  point := fun i =>
    match i.val with
    | 0 => 275 / 2
    | 1 => 16205100426911 / 160000000000
    | 2 => 5240396523263 / 32000000000
    | 3 => 4728607888477 / 160000000000
    | 4 => 12701705922169 / 160000000000
    | 5 => 34487602412373 / 160000000000
    | 6 => 25403411844349 / 160000000000
    | 7 => 43529179182577 / 160000000000
    | 8 => 32063396370643 / 160000000000
    | 9 => 49193495504989 / 160000000000
    | 10 => 28401877872181 / 160000000000
    | 11 => 50399630689529 / 160000000000
    | 12 => 47089872658301 / 160000000000
    | 13 => 33605555096333 / 160000000000
    | 14 => 38105117766507 / 160000000000
    | 15 => 31768074535483 / 160000000000
    | 16 => 28068057281143 / 160000000000
    | 17 => 8135217005157 / 32000000000
    | 18 => 22502438369279 / 160000000000
    | 19 => 19075566213319 / 160000000000
    | 20 => 11936603629357 / 160000000000
    | 21 => 6419545131219 / 160000000000
    | 22 => 17430313810657 / 160000000000
    | 23 => 23799603345089 / 160000000000
    | 24 => 10063396370643 / 160000000000
    | 25 => 40907147543603 / 160000000000
    | _ => 27324078755677 / 160000000000
  state := fun i =>
    match i.val with
    | 0 => (orderedInterval (3700584730 / 1000000000000) (3700584733 / 1000000000000), orderedInterval (67929888147 / 1000000000000) (67929888150 / 1000000000000))
    | 1 => (orderedInterval (79230870949 / 1000000000000) (79230870968 / 1000000000000), orderedInterval (2440197056 / 1000000000000) (2440197075 / 1000000000000))
    | 2 => (orderedInterval (57748025074 / 1000000000000) (57748025075 / 1000000000000), orderedInterval (23331402901 / 1000000000000) (23331402902 / 1000000000000))
    | 3 => (orderedInterval (-129500623852 / 1000000000000) (-129500614709 / 1000000000000), orderedInterval (71247679566 / 1000000000000) (71247688708 / 1000000000000))
    | 4 => (orderedInterval (-89394674006 / 1000000000000) (-89394673938 / 1000000000000), orderedInterval (5832148508 / 1000000000000) (5832148575 / 1000000000000))
    | 5 => (orderedInterval (23028071718 / 1000000000000) (23028073003 / 1000000000000), orderedInterval (-49279567923 / 1000000000000) (-49279566638 / 1000000000000))
    | 6 => (orderedInterval (39087727790 / 1000000000000) (39087746787 / 1000000000000), orderedInterval (-49940952387 / 1000000000000) (-49940933390 / 1000000000000))
    | 7 => (orderedInterval (22177012367 / 1000000000000) (22177013813 / 1000000000000), orderedInterval (-43031486546 / 1000000000000) (-43031485100 / 1000000000000))
    | 8 => (orderedInterval (6695409514 / 1000000000000) (6695409515 / 1000000000000), orderedInterval (55947446390 / 1000000000000) (55947446391 / 1000000000000))
    | 9 => (orderedInterval (16380901921 / 1000000000000) (16380901922 / 1000000000000), orderedInterval (42426276324 / 1000000000000) (42426276325 / 1000000000000))
    | 10 => (orderedInterval (41875412092 / 1000000000000) (41875459430 / 1000000000000), orderedInterval (-42929200912 / 1000000000000) (-42929153574 / 1000000000000))
    | 11 => (orderedInterval (44893587267 / 1000000000000) (44893587580 / 1000000000000), orderedInterval (-2436262372 / 1000000000000) (-2436262059 / 1000000000000))
    | 12 => (orderedInterval (-9833105338 / 1000000000000) (-9833105299 / 1000000000000), orderedInterval (45474299945 / 1000000000000) (45474299984 / 1000000000000))
    | 13 => (orderedInterval (-17986595608 / 1000000000000) (-17986595607 / 1000000000000), orderedInterval (-51990928253 / 1000000000000) (-51990928252 / 1000000000000))
    | 14 => (orderedInterval (9297788530 / 1000000000000) (9297788531 / 1000000000000), orderedInterval (50839760502 / 1000000000000) (50839760503 / 1000000000000))
    | 15 => (orderedInterval (-55937717566 / 1000000000000) (-55937717560 / 1000000000000), orderedInterval (-8651144362 / 1000000000000) (-8651144356 / 1000000000000))
    | 16 => (orderedInterval (16697467891 / 1000000000000) (16697467892 / 1000000000000), orderedInterval (57833438598 / 1000000000000) (57833438599 / 1000000000000))
    | 17 => (orderedInterval (-25789597991 / 1000000000000) (-25789597990 / 1000000000000), orderedInterval (-42833453445 / 1000000000000) (-42833453444 / 1000000000000))
    | 18 => (orderedInterval (-3569514397 / 1000000000000) (-3569514394 / 1000000000000), orderedInterval (-67172653511 / 1000000000000) (-67172653508 / 1000000000000))
    | 19 => (orderedInterval (42821268052 / 1000000000000) (42821268053 / 1000000000000), orderedInterval (59032959440 / 1000000000000) (59032959441 / 1000000000000))
    | 20 => (orderedInterval (-990999342 / 1000000000000) (-990999332 / 1000000000000), orderedInterval (92378471741 / 1000000000000) (92378471750 / 1000000000000))
    | 21 => (orderedInterval (-8022755518 / 1000000000000) (-8022755514 / 1000000000000), orderedInterval (-125613575151 / 1000000000000) (-125613575147 / 1000000000000))
    | 22 => (orderedInterval (17578701136 / 1000000000000) (17578701327 / 1000000000000), orderedInterval (-74477173416 / 1000000000000) (-74477173225 / 1000000000000))
    | 23 => (orderedInterval (-62373050050 / 1000000000000) (-62373047644 / 1000000000000), orderedInterval (19944172919 / 1000000000000) (19944175325 / 1000000000000))
    | 24 => (orderedInterval (75435559729 / 1000000000000) (75435559730 / 1000000000000), orderedInterval (65967499419 / 1000000000000) (65967499420 / 1000000000000))
    | 25 => (orderedInterval (-45668679804 / 1000000000000) (-45668666758 / 1000000000000), orderedInterval (20198456837 / 1000000000000) (20198469882 / 1000000000000))
    | _ => (orderedInterval (57491848335 / 1000000000000) (57491852396 / 1000000000000), orderedInterval (-20722929546 / 1000000000000) (-20722925485 / 1000000000000))
  chunkTarget := fun r b =>
    match r.val with
    | 0 =>
      match b.val with
      | 0 => orderedInterval (5593780189 / 1000000000000) (5593780201 / 1000000000000)
      | 1 => orderedInterval (-3496023229 / 1000000000000) (-3496023018 / 1000000000000)
      | 2 => orderedInterval (-522213003 / 1000000000000) (-522212949 / 1000000000000)
      | 3 => orderedInterval (6573822870 / 1000000000000) (6573826477 / 1000000000000)
      | 4 => orderedInterval (-1570398309 / 1000000000000) (-1570398291 / 1000000000000)
      | 5 => orderedInterval (-2261806489 / 1000000000000) (-2261806475 / 1000000000000)
      | 6 => orderedInterval (-1885205784 / 1000000000000) (-1885205748 / 1000000000000)
      | 7 => orderedInterval (4529535429 / 1000000000000) (4529535635 / 1000000000000)
      | _ => orderedInterval (-6614735691 / 1000000000000) (-6614733828 / 1000000000000)
    | 1 =>
      match b.val with
      | 0 => orderedInterval (28572391153 / 1000000000000) (28572391165 / 1000000000000)
      | 1 => orderedInterval (5448583756 / 1000000000000) (5448583941 / 1000000000000)
      | 2 => orderedInterval (4596766252 / 1000000000000) (4596766354 / 1000000000000)
      | 3 => orderedInterval (-21756574229 / 1000000000000) (-21756569485 / 1000000000000)
      | 4 => orderedInterval (-9712766035 / 1000000000000) (-9712766006 / 1000000000000)
      | 5 => orderedInterval (-6394446211 / 1000000000000) (-6394446191 / 1000000000000)
      | 6 => orderedInterval (9720314252 / 1000000000000) (9720314285 / 1000000000000)
      | 7 => orderedInterval (361975222 / 1000000000000) (361975440 / 1000000000000)
      | _ => orderedInterval (1953793088 / 1000000000000) (1953796063 / 1000000000000)
    | 2 =>
      match b.val with
      | 0 => orderedInterval (-6881979569 / 1000000000000) (-6881979554 / 1000000000000)
      | 1 => orderedInterval (5006400806 / 1000000000000) (5006401064 / 1000000000000)
      | 2 => orderedInterval (2300728153 / 1000000000000) (2300728353 / 1000000000000)
      | 3 => orderedInterval (-23952718075 / 1000000000000) (-23952711718 / 1000000000000)
      | 4 => orderedInterval (3367175561 / 1000000000000) (3367175609 / 1000000000000)
      | 5 => orderedInterval (5206031896 / 1000000000000) (5206031926 / 1000000000000)
      | 6 => orderedInterval (1163853317 / 1000000000000) (1163853349 / 1000000000000)
      | 7 => orderedInterval (-5359136290 / 1000000000000) (-5359136055 / 1000000000000)
      | _ => orderedInterval (3677340457 / 1000000000000) (3677345405 / 1000000000000)
    | 3 =>
      match b.val with
      | 0 => orderedInterval (-29195545300 / 1000000000000) (-29195545284 / 1000000000000)
      | 1 => orderedInterval (-13565088844 / 1000000000000) (-13565088450 / 1000000000000)
      | 2 => orderedInterval (-14483207162 / 1000000000000) (-14483206771 / 1000000000000)
      | 3 => orderedInterval (95465270201 / 1000000000000) (95465278860 / 1000000000000)
      | 4 => orderedInterval (26885723273 / 1000000000000) (26885723356 / 1000000000000)
      | 5 => orderedInterval (14067294736 / 1000000000000) (14067294780 / 1000000000000)
      | 6 => orderedInterval (-9803428924 / 1000000000000) (-9803428893 / 1000000000000)
      | 7 => orderedInterval (1076158335 / 1000000000000) (1076158588 / 1000000000000)
      | _ => orderedInterval (3056184694 / 1000000000000) (3056193138 / 1000000000000)
    | _ =>
      match b.val with
      | 0 => orderedInterval (8926793755 / 1000000000000) (8926793774 / 1000000000000)
      | 1 => orderedInterval (-10048194857 / 1000000000000) (-10048194239 / 1000000000000)
      | 2 => orderedInterval (-9542611008 / 1000000000000) (-9542610238 / 1000000000000)
      | 3 => orderedInterval (110240696592 / 1000000000000) (110240708860 / 1000000000000)
      | 4 => orderedInterval (-6348452659 / 1000000000000) (-6348452513 / 1000000000000)
      | 5 => orderedInterval (-13260943246 / 1000000000000) (-13260943175 / 1000000000000)
      | 6 => orderedInterval (-605370859 / 1000000000000) (-605370829 / 1000000000000)
      | 7 => orderedInterval (6374872949 / 1000000000000) (6374873223 / 1000000000000)
      | _ => orderedInterval (18746042007 / 1000000000000) (18746056831 / 1000000000000)
  coefficientTarget := fun i =>
    match i.val with
    | 0 => orderedInterval (346755983 / 1000000000000) (346762004 / 1000000000000)
    | 1 => orderedInterval (12790037248 / 1000000000000) (12790045566 / 1000000000000)
    | 2 => orderedInterval (-15472303744 / 1000000000000) (-15472291621 / 1000000000000)
    | 3 => orderedInterval (73503361009 / 1000000000000) (73503379324 / 1000000000000)
    | _ => orderedInterval (104482832674 / 1000000000000) (104482861694 / 1000000000000)

theorem compactCertificate263_stateChecks0 :
    compactCertificate263.stateChecks 0 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 44 12 (275 / 2)) (orderedInterval (3700584730 / 1000000000000) (3700584733 / 1000000000000), orderedInterval (67929888147 / 1000000000000) (67929888150 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 32 12 (16205100426911 / 160000000000)) (orderedInterval (79230870949 / 1000000000000) (79230870968 / 1000000000000), orderedInterval (2440197056 / 1000000000000) (2440197075 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 52 12 (5240396523263 / 32000000000)) (orderedInterval (57748025074 / 1000000000000) (57748025075 / 1000000000000), orderedInterval (23331402901 / 1000000000000) (23331402902 / 1000000000000))) = true
  norm_num [besselStateAtRationalPoint, besselIntervalStepZero,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, besselZeroTransition,
    besselInitial, besselGridStateAt, besselGridStateBlock00, besselGridStateBlock01,
    besselGridStateBlock02, besselGridStateBlock03, besselGridStateBlock04,
    besselGridStateBlock05, besselGridStateBlock06, besselGridStateBlock07,
    besselGridStateBlock08, besselGridStateBlock09, besselGridStateBlock10,
    besselGridStateBlock11, besselGridStateBlock12, besselGridStateBlock13,
    besselGridStateBlock14, besselGridState009, besselGridState013, besselGridState020, besselGridState024, besselGridState025, besselGridState032, besselGridState035, besselGridState038, besselGridState044, besselGridState045, besselGridState047, besselGridState051, besselGridState052, besselGridState054, besselGridState056, besselGridState057, besselGridState063, besselGridState064, besselGridState067, besselGridState069, besselGridState076, besselGridState081, besselGridState087, besselGridState094, besselGridState098, besselGridState100, besselStateSubset, linearInterval, widenInterval,
    rationalErrorInterval, rationalIntervalSubset, orderedInterval, Finset.sum_range_succ,
    IntervalRat.add, IntervalRat.mul, IntervalRat.scale, IntervalRat.singleton]

theorem compactCertificate263_stateChecks1 :
    compactCertificate263.stateChecks 3 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 9 12 (4728607888477 / 160000000000)) (orderedInterval (-129500623852 / 1000000000000) (-129500614709 / 1000000000000), orderedInterval (71247679566 / 1000000000000) (71247688708 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 25 12 (12701705922169 / 160000000000)) (orderedInterval (-89394674006 / 1000000000000) (-89394673938 / 1000000000000), orderedInterval (5832148508 / 1000000000000) (5832148575 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 69 12 (34487602412373 / 160000000000)) (orderedInterval (23028071718 / 1000000000000) (23028073003 / 1000000000000), orderedInterval (-49279567923 / 1000000000000) (-49279566638 / 1000000000000))) = true
  norm_num [besselStateAtRationalPoint, besselIntervalStepZero,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, besselZeroTransition,
    besselInitial, besselGridStateAt, besselGridStateBlock00, besselGridStateBlock01,
    besselGridStateBlock02, besselGridStateBlock03, besselGridStateBlock04,
    besselGridStateBlock05, besselGridStateBlock06, besselGridStateBlock07,
    besselGridStateBlock08, besselGridStateBlock09, besselGridStateBlock10,
    besselGridStateBlock11, besselGridStateBlock12, besselGridStateBlock13,
    besselGridStateBlock14, besselGridState009, besselGridState013, besselGridState020, besselGridState024, besselGridState025, besselGridState032, besselGridState035, besselGridState038, besselGridState044, besselGridState045, besselGridState047, besselGridState051, besselGridState052, besselGridState054, besselGridState056, besselGridState057, besselGridState063, besselGridState064, besselGridState067, besselGridState069, besselGridState076, besselGridState081, besselGridState087, besselGridState094, besselGridState098, besselGridState100, besselStateSubset, linearInterval, widenInterval,
    rationalErrorInterval, rationalIntervalSubset, orderedInterval, Finset.sum_range_succ,
    IntervalRat.add, IntervalRat.mul, IntervalRat.scale, IntervalRat.singleton]

theorem compactCertificate263_stateChecks2 :
    compactCertificate263.stateChecks 6 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 51 12 (25403411844349 / 160000000000)) (orderedInterval (39087727790 / 1000000000000) (39087746787 / 1000000000000), orderedInterval (-49940952387 / 1000000000000) (-49940933390 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 87 12 (43529179182577 / 160000000000)) (orderedInterval (22177012367 / 1000000000000) (22177013813 / 1000000000000), orderedInterval (-43031486546 / 1000000000000) (-43031485100 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 64 12 (32063396370643 / 160000000000)) (orderedInterval (6695409514 / 1000000000000) (6695409515 / 1000000000000), orderedInterval (55947446390 / 1000000000000) (55947446391 / 1000000000000))) = true
  norm_num [besselStateAtRationalPoint, besselIntervalStepZero,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, besselZeroTransition,
    besselInitial, besselGridStateAt, besselGridStateBlock00, besselGridStateBlock01,
    besselGridStateBlock02, besselGridStateBlock03, besselGridStateBlock04,
    besselGridStateBlock05, besselGridStateBlock06, besselGridStateBlock07,
    besselGridStateBlock08, besselGridStateBlock09, besselGridStateBlock10,
    besselGridStateBlock11, besselGridStateBlock12, besselGridStateBlock13,
    besselGridStateBlock14, besselGridState009, besselGridState013, besselGridState020, besselGridState024, besselGridState025, besselGridState032, besselGridState035, besselGridState038, besselGridState044, besselGridState045, besselGridState047, besselGridState051, besselGridState052, besselGridState054, besselGridState056, besselGridState057, besselGridState063, besselGridState064, besselGridState067, besselGridState069, besselGridState076, besselGridState081, besselGridState087, besselGridState094, besselGridState098, besselGridState100, besselStateSubset, linearInterval, widenInterval,
    rationalErrorInterval, rationalIntervalSubset, orderedInterval, Finset.sum_range_succ,
    IntervalRat.add, IntervalRat.mul, IntervalRat.scale, IntervalRat.singleton]

theorem compactCertificate263_stateChecks3 :
    compactCertificate263.stateChecks 9 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 98 12 (49193495504989 / 160000000000)) (orderedInterval (16380901921 / 1000000000000) (16380901922 / 1000000000000), orderedInterval (42426276324 / 1000000000000) (42426276325 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 57 12 (28401877872181 / 160000000000)) (orderedInterval (41875412092 / 1000000000000) (41875459430 / 1000000000000), orderedInterval (-42929200912 / 1000000000000) (-42929153574 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 100 12 (50399630689529 / 160000000000)) (orderedInterval (44893587267 / 1000000000000) (44893587580 / 1000000000000), orderedInterval (-2436262372 / 1000000000000) (-2436262059 / 1000000000000))) = true
  norm_num [besselStateAtRationalPoint, besselIntervalStepZero,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, besselZeroTransition,
    besselInitial, besselGridStateAt, besselGridStateBlock00, besselGridStateBlock01,
    besselGridStateBlock02, besselGridStateBlock03, besselGridStateBlock04,
    besselGridStateBlock05, besselGridStateBlock06, besselGridStateBlock07,
    besselGridStateBlock08, besselGridStateBlock09, besselGridStateBlock10,
    besselGridStateBlock11, besselGridStateBlock12, besselGridStateBlock13,
    besselGridStateBlock14, besselGridState009, besselGridState013, besselGridState020, besselGridState024, besselGridState025, besselGridState032, besselGridState035, besselGridState038, besselGridState044, besselGridState045, besselGridState047, besselGridState051, besselGridState052, besselGridState054, besselGridState056, besselGridState057, besselGridState063, besselGridState064, besselGridState067, besselGridState069, besselGridState076, besselGridState081, besselGridState087, besselGridState094, besselGridState098, besselGridState100, besselStateSubset, linearInterval, widenInterval,
    rationalErrorInterval, rationalIntervalSubset, orderedInterval, Finset.sum_range_succ,
    IntervalRat.add, IntervalRat.mul, IntervalRat.scale, IntervalRat.singleton]

theorem compactCertificate263_stateChecks4 :
    compactCertificate263.stateChecks 12 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 94 12 (47089872658301 / 160000000000)) (orderedInterval (-9833105338 / 1000000000000) (-9833105299 / 1000000000000), orderedInterval (45474299945 / 1000000000000) (45474299984 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 67 12 (33605555096333 / 160000000000)) (orderedInterval (-17986595608 / 1000000000000) (-17986595607 / 1000000000000), orderedInterval (-51990928253 / 1000000000000) (-51990928252 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 76 12 (38105117766507 / 160000000000)) (orderedInterval (9297788530 / 1000000000000) (9297788531 / 1000000000000), orderedInterval (50839760502 / 1000000000000) (50839760503 / 1000000000000))) = true
  norm_num [besselStateAtRationalPoint, besselIntervalStepZero,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, besselZeroTransition,
    besselInitial, besselGridStateAt, besselGridStateBlock00, besselGridStateBlock01,
    besselGridStateBlock02, besselGridStateBlock03, besselGridStateBlock04,
    besselGridStateBlock05, besselGridStateBlock06, besselGridStateBlock07,
    besselGridStateBlock08, besselGridStateBlock09, besselGridStateBlock10,
    besselGridStateBlock11, besselGridStateBlock12, besselGridStateBlock13,
    besselGridStateBlock14, besselGridState009, besselGridState013, besselGridState020, besselGridState024, besselGridState025, besselGridState032, besselGridState035, besselGridState038, besselGridState044, besselGridState045, besselGridState047, besselGridState051, besselGridState052, besselGridState054, besselGridState056, besselGridState057, besselGridState063, besselGridState064, besselGridState067, besselGridState069, besselGridState076, besselGridState081, besselGridState087, besselGridState094, besselGridState098, besselGridState100, besselStateSubset, linearInterval, widenInterval,
    rationalErrorInterval, rationalIntervalSubset, orderedInterval, Finset.sum_range_succ,
    IntervalRat.add, IntervalRat.mul, IntervalRat.scale, IntervalRat.singleton]

theorem compactCertificate263_stateChecks5 :
    compactCertificate263.stateChecks 15 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 63 12 (31768074535483 / 160000000000)) (orderedInterval (-55937717566 / 1000000000000) (-55937717560 / 1000000000000), orderedInterval (-8651144362 / 1000000000000) (-8651144356 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 56 12 (28068057281143 / 160000000000)) (orderedInterval (16697467891 / 1000000000000) (16697467892 / 1000000000000), orderedInterval (57833438598 / 1000000000000) (57833438599 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 81 12 (8135217005157 / 32000000000)) (orderedInterval (-25789597991 / 1000000000000) (-25789597990 / 1000000000000), orderedInterval (-42833453445 / 1000000000000) (-42833453444 / 1000000000000))) = true
  norm_num [besselStateAtRationalPoint, besselIntervalStepZero,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, besselZeroTransition,
    besselInitial, besselGridStateAt, besselGridStateBlock00, besselGridStateBlock01,
    besselGridStateBlock02, besselGridStateBlock03, besselGridStateBlock04,
    besselGridStateBlock05, besselGridStateBlock06, besselGridStateBlock07,
    besselGridStateBlock08, besselGridStateBlock09, besselGridStateBlock10,
    besselGridStateBlock11, besselGridStateBlock12, besselGridStateBlock13,
    besselGridStateBlock14, besselGridState009, besselGridState013, besselGridState020, besselGridState024, besselGridState025, besselGridState032, besselGridState035, besselGridState038, besselGridState044, besselGridState045, besselGridState047, besselGridState051, besselGridState052, besselGridState054, besselGridState056, besselGridState057, besselGridState063, besselGridState064, besselGridState067, besselGridState069, besselGridState076, besselGridState081, besselGridState087, besselGridState094, besselGridState098, besselGridState100, besselStateSubset, linearInterval, widenInterval,
    rationalErrorInterval, rationalIntervalSubset, orderedInterval, Finset.sum_range_succ,
    IntervalRat.add, IntervalRat.mul, IntervalRat.scale, IntervalRat.singleton]

theorem compactCertificate263_stateChecks6 :
    compactCertificate263.stateChecks 18 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 45 12 (22502438369279 / 160000000000)) (orderedInterval (-3569514397 / 1000000000000) (-3569514394 / 1000000000000), orderedInterval (-67172653511 / 1000000000000) (-67172653508 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 38 12 (19075566213319 / 160000000000)) (orderedInterval (42821268052 / 1000000000000) (42821268053 / 1000000000000), orderedInterval (59032959440 / 1000000000000) (59032959441 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 24 12 (11936603629357 / 160000000000)) (orderedInterval (-990999342 / 1000000000000) (-990999332 / 1000000000000), orderedInterval (92378471741 / 1000000000000) (92378471750 / 1000000000000))) = true
  norm_num [besselStateAtRationalPoint, besselIntervalStepZero,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, besselZeroTransition,
    besselInitial, besselGridStateAt, besselGridStateBlock00, besselGridStateBlock01,
    besselGridStateBlock02, besselGridStateBlock03, besselGridStateBlock04,
    besselGridStateBlock05, besselGridStateBlock06, besselGridStateBlock07,
    besselGridStateBlock08, besselGridStateBlock09, besselGridStateBlock10,
    besselGridStateBlock11, besselGridStateBlock12, besselGridStateBlock13,
    besselGridStateBlock14, besselGridState009, besselGridState013, besselGridState020, besselGridState024, besselGridState025, besselGridState032, besselGridState035, besselGridState038, besselGridState044, besselGridState045, besselGridState047, besselGridState051, besselGridState052, besselGridState054, besselGridState056, besselGridState057, besselGridState063, besselGridState064, besselGridState067, besselGridState069, besselGridState076, besselGridState081, besselGridState087, besselGridState094, besselGridState098, besselGridState100, besselStateSubset, linearInterval, widenInterval,
    rationalErrorInterval, rationalIntervalSubset, orderedInterval, Finset.sum_range_succ,
    IntervalRat.add, IntervalRat.mul, IntervalRat.scale, IntervalRat.singleton]

theorem compactCertificate263_stateChecks7 :
    compactCertificate263.stateChecks 21 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 13 12 (6419545131219 / 160000000000)) (orderedInterval (-8022755518 / 1000000000000) (-8022755514 / 1000000000000), orderedInterval (-125613575151 / 1000000000000) (-125613575147 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 35 12 (17430313810657 / 160000000000)) (orderedInterval (17578701136 / 1000000000000) (17578701327 / 1000000000000), orderedInterval (-74477173416 / 1000000000000) (-74477173225 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 47 12 (23799603345089 / 160000000000)) (orderedInterval (-62373050050 / 1000000000000) (-62373047644 / 1000000000000), orderedInterval (19944172919 / 1000000000000) (19944175325 / 1000000000000))) = true
  norm_num [besselStateAtRationalPoint, besselIntervalStepZero,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, besselZeroTransition,
    besselInitial, besselGridStateAt, besselGridStateBlock00, besselGridStateBlock01,
    besselGridStateBlock02, besselGridStateBlock03, besselGridStateBlock04,
    besselGridStateBlock05, besselGridStateBlock06, besselGridStateBlock07,
    besselGridStateBlock08, besselGridStateBlock09, besselGridStateBlock10,
    besselGridStateBlock11, besselGridStateBlock12, besselGridStateBlock13,
    besselGridStateBlock14, besselGridState009, besselGridState013, besselGridState020, besselGridState024, besselGridState025, besselGridState032, besselGridState035, besselGridState038, besselGridState044, besselGridState045, besselGridState047, besselGridState051, besselGridState052, besselGridState054, besselGridState056, besselGridState057, besselGridState063, besselGridState064, besselGridState067, besselGridState069, besselGridState076, besselGridState081, besselGridState087, besselGridState094, besselGridState098, besselGridState100, besselStateSubset, linearInterval, widenInterval,
    rationalErrorInterval, rationalIntervalSubset, orderedInterval, Finset.sum_range_succ,
    IntervalRat.add, IntervalRat.mul, IntervalRat.scale, IntervalRat.singleton]

theorem compactCertificate263_stateChecks8 :
    compactCertificate263.stateChecks 24 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 20 12 (10063396370643 / 160000000000)) (orderedInterval (75435559729 / 1000000000000) (75435559730 / 1000000000000), orderedInterval (65967499419 / 1000000000000) (65967499420 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 81 12 (40907147543603 / 160000000000)) (orderedInterval (-45668679804 / 1000000000000) (-45668666758 / 1000000000000), orderedInterval (20198456837 / 1000000000000) (20198469882 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 54 12 (27324078755677 / 160000000000)) (orderedInterval (57491848335 / 1000000000000) (57491852396 / 1000000000000), orderedInterval (-20722929546 / 1000000000000) (-20722925485 / 1000000000000))) = true
  norm_num [besselStateAtRationalPoint, besselIntervalStepZero,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, besselZeroTransition,
    besselInitial, besselGridStateAt, besselGridStateBlock00, besselGridStateBlock01,
    besselGridStateBlock02, besselGridStateBlock03, besselGridStateBlock04,
    besselGridStateBlock05, besselGridStateBlock06, besselGridStateBlock07,
    besselGridStateBlock08, besselGridStateBlock09, besselGridStateBlock10,
    besselGridStateBlock11, besselGridStateBlock12, besselGridStateBlock13,
    besselGridStateBlock14, besselGridState009, besselGridState013, besselGridState020, besselGridState024, besselGridState025, besselGridState032, besselGridState035, besselGridState038, besselGridState044, besselGridState045, besselGridState047, besselGridState051, besselGridState052, besselGridState054, besselGridState056, besselGridState057, besselGridState063, besselGridState064, besselGridState067, besselGridState069, besselGridState076, besselGridState081, besselGridState087, besselGridState094, besselGridState098, besselGridState100, besselStateSubset, linearInterval, widenInterval,
    rationalErrorInterval, rationalIntervalSubset, orderedInterval, Finset.sum_range_succ,
    IntervalRat.add, IntervalRat.mul, IntervalRat.scale, IntervalRat.singleton]

theorem compactCertificate263_states : ∀ j,
    BesselStateValid (compactCertificate263.point j) (compactCertificate263.state j) :=
  compactCertificate263.statesValid_of_checks3 compactCertificate263_stateChecks0
    compactCertificate263_stateChecks1 compactCertificate263_stateChecks2
    compactCertificate263_stateChecks3 compactCertificate263_stateChecks4
    compactCertificate263_stateChecks5 compactCertificate263_stateChecks6
    compactCertificate263_stateChecks7 compactCertificate263_stateChecks8

theorem compactCertificate263_chunkChecks0_0 :
    compactCertificate263.chunkChecks (0 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 0) <| besselDerivativeNearFromState (275 / 2) 0 (IntervalRat.scale (275 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (3700584730 / 1000000000000) (3700584733 / 1000000000000), orderedInterval (67929888147 / 1000000000000) (67929888150 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 0) <| besselDerivativeNearFromState (16205100426911 / 160000000000) 0 (IntervalRat.scale (275 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (79230870949 / 1000000000000) (79230870968 / 1000000000000), orderedInterval (2440197056 / 1000000000000) (2440197075 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 0) <| besselDerivativeNearFromState (5240396523263 / 32000000000) 0 (IntervalRat.scale (275 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (57748025074 / 1000000000000) (57748025075 / 1000000000000), orderedInterval (23331402901 / 1000000000000) (23331402902 / 1000000000000)))) (orderedInterval (5593780189 / 1000000000000) (5593780201 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 0) <| besselDerivativeNearFromState (4728607888477 / 160000000000) 0 (IntervalRat.scale (275 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-129500623852 / 1000000000000) (-129500614709 / 1000000000000), orderedInterval (71247679566 / 1000000000000) (71247688708 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 0) <| besselDerivativeNearFromState (12701705922169 / 160000000000) 0 (IntervalRat.scale (275 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-89394674006 / 1000000000000) (-89394673938 / 1000000000000), orderedInterval (5832148508 / 1000000000000) (5832148575 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 0) <| besselDerivativeNearFromState (34487602412373 / 160000000000) 0 (IntervalRat.scale (275 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (23028071718 / 1000000000000) (23028073003 / 1000000000000), orderedInterval (-49279567923 / 1000000000000) (-49279566638 / 1000000000000)))) (orderedInterval (-3496023229 / 1000000000000) (-3496023018 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 0) <| besselDerivativeNearFromState (25403411844349 / 160000000000) 0 (IntervalRat.scale (275 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (39087727790 / 1000000000000) (39087746787 / 1000000000000), orderedInterval (-49940952387 / 1000000000000) (-49940933390 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 0) <| besselDerivativeNearFromState (43529179182577 / 160000000000) 0 (IntervalRat.scale (275 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (22177012367 / 1000000000000) (22177013813 / 1000000000000), orderedInterval (-43031486546 / 1000000000000) (-43031485100 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 0) <| besselDerivativeNearFromState (32063396370643 / 160000000000) 0 (IntervalRat.scale (275 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (6695409514 / 1000000000000) (6695409515 / 1000000000000), orderedInterval (55947446390 / 1000000000000) (55947446391 / 1000000000000)))) (orderedInterval (-522213003 / 1000000000000) (-522212949 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate263_chunkChecks0_1 :
    compactCertificate263.chunkChecks (0 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 0) <| besselDerivativeNearFromState (49193495504989 / 160000000000) 0 (IntervalRat.scale (275 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (16380901921 / 1000000000000) (16380901922 / 1000000000000), orderedInterval (42426276324 / 1000000000000) (42426276325 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 0) <| besselDerivativeNearFromState (28401877872181 / 160000000000) 0 (IntervalRat.scale (275 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (41875412092 / 1000000000000) (41875459430 / 1000000000000), orderedInterval (-42929200912 / 1000000000000) (-42929153574 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 0) <| besselDerivativeNearFromState (50399630689529 / 160000000000) 0 (IntervalRat.scale (275 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (44893587267 / 1000000000000) (44893587580 / 1000000000000), orderedInterval (-2436262372 / 1000000000000) (-2436262059 / 1000000000000)))) (orderedInterval (6573822870 / 1000000000000) (6573826477 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 0) <| besselDerivativeNearFromState (47089872658301 / 160000000000) 0 (IntervalRat.scale (275 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-9833105338 / 1000000000000) (-9833105299 / 1000000000000), orderedInterval (45474299945 / 1000000000000) (45474299984 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 0) <| besselDerivativeNearFromState (33605555096333 / 160000000000) 0 (IntervalRat.scale (275 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-17986595608 / 1000000000000) (-17986595607 / 1000000000000), orderedInterval (-51990928253 / 1000000000000) (-51990928252 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 0) <| besselDerivativeNearFromState (38105117766507 / 160000000000) 0 (IntervalRat.scale (275 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (9297788530 / 1000000000000) (9297788531 / 1000000000000), orderedInterval (50839760502 / 1000000000000) (50839760503 / 1000000000000)))) (orderedInterval (-1570398309 / 1000000000000) (-1570398291 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 0) <| besselDerivativeNearFromState (31768074535483 / 160000000000) 0 (IntervalRat.scale (275 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-55937717566 / 1000000000000) (-55937717560 / 1000000000000), orderedInterval (-8651144362 / 1000000000000) (-8651144356 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 0) <| besselDerivativeNearFromState (28068057281143 / 160000000000) 0 (IntervalRat.scale (275 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (16697467891 / 1000000000000) (16697467892 / 1000000000000), orderedInterval (57833438598 / 1000000000000) (57833438599 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 0) <| besselDerivativeNearFromState (8135217005157 / 32000000000) 0 (IntervalRat.scale (275 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-25789597991 / 1000000000000) (-25789597990 / 1000000000000), orderedInterval (-42833453445 / 1000000000000) (-42833453444 / 1000000000000)))) (orderedInterval (-2261806489 / 1000000000000) (-2261806475 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate263_chunkChecks0_2 :
    compactCertificate263.chunkChecks (0 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 0) <| besselDerivativeNearFromState (22502438369279 / 160000000000) 0 (IntervalRat.scale (275 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-3569514397 / 1000000000000) (-3569514394 / 1000000000000), orderedInterval (-67172653511 / 1000000000000) (-67172653508 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 0) <| besselDerivativeNearFromState (19075566213319 / 160000000000) 0 (IntervalRat.scale (275 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (42821268052 / 1000000000000) (42821268053 / 1000000000000), orderedInterval (59032959440 / 1000000000000) (59032959441 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 0) <| besselDerivativeNearFromState (11936603629357 / 160000000000) 0 (IntervalRat.scale (275 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-990999342 / 1000000000000) (-990999332 / 1000000000000), orderedInterval (92378471741 / 1000000000000) (92378471750 / 1000000000000)))) (orderedInterval (-1885205784 / 1000000000000) (-1885205748 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 0) <| besselDerivativeNearFromState (6419545131219 / 160000000000) 0 (IntervalRat.scale (275 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-8022755518 / 1000000000000) (-8022755514 / 1000000000000), orderedInterval (-125613575151 / 1000000000000) (-125613575147 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 0) <| besselDerivativeNearFromState (17430313810657 / 160000000000) 0 (IntervalRat.scale (275 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (17578701136 / 1000000000000) (17578701327 / 1000000000000), orderedInterval (-74477173416 / 1000000000000) (-74477173225 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 0) <| besselDerivativeNearFromState (23799603345089 / 160000000000) 0 (IntervalRat.scale (275 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-62373050050 / 1000000000000) (-62373047644 / 1000000000000), orderedInterval (19944172919 / 1000000000000) (19944175325 / 1000000000000)))) (orderedInterval (4529535429 / 1000000000000) (4529535635 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 0) <| besselDerivativeNearFromState (10063396370643 / 160000000000) 0 (IntervalRat.scale (275 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (75435559729 / 1000000000000) (75435559730 / 1000000000000), orderedInterval (65967499419 / 1000000000000) (65967499420 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 0) <| besselDerivativeNearFromState (40907147543603 / 160000000000) 0 (IntervalRat.scale (275 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-45668679804 / 1000000000000) (-45668666758 / 1000000000000), orderedInterval (20198456837 / 1000000000000) (20198469882 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 0) <| besselDerivativeNearFromState (27324078755677 / 160000000000) 0 (IntervalRat.scale (275 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (57491848335 / 1000000000000) (57491852396 / 1000000000000), orderedInterval (-20722929546 / 1000000000000) (-20722925485 / 1000000000000)))) (orderedInterval (-6614735691 / 1000000000000) (-6614733828 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate263_chunkChecks0 :
    compactCertificate263.chunkChecks (0 : Fin 5) 0 9 = true :=
  compactCertificate263.chunkChecks_nine_of_three (0 : Fin 5) compactCertificate263_chunkChecks0_0
    compactCertificate263_chunkChecks0_1 compactCertificate263_chunkChecks0_2

theorem compactCertificate263_chunkChecks1_0 :
    compactCertificate263.chunkChecks (1 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 1) <| besselDerivativeNearFromState (275 / 2) 1 (IntervalRat.scale (275 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (3700584730 / 1000000000000) (3700584733 / 1000000000000), orderedInterval (67929888147 / 1000000000000) (67929888150 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 1) <| besselDerivativeNearFromState (16205100426911 / 160000000000) 1 (IntervalRat.scale (275 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (79230870949 / 1000000000000) (79230870968 / 1000000000000), orderedInterval (2440197056 / 1000000000000) (2440197075 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 1) <| besselDerivativeNearFromState (5240396523263 / 32000000000) 1 (IntervalRat.scale (275 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (57748025074 / 1000000000000) (57748025075 / 1000000000000), orderedInterval (23331402901 / 1000000000000) (23331402902 / 1000000000000)))) (orderedInterval (28572391153 / 1000000000000) (28572391165 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 1) <| besselDerivativeNearFromState (4728607888477 / 160000000000) 1 (IntervalRat.scale (275 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-129500623852 / 1000000000000) (-129500614709 / 1000000000000), orderedInterval (71247679566 / 1000000000000) (71247688708 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 1) <| besselDerivativeNearFromState (12701705922169 / 160000000000) 1 (IntervalRat.scale (275 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-89394674006 / 1000000000000) (-89394673938 / 1000000000000), orderedInterval (5832148508 / 1000000000000) (5832148575 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 1) <| besselDerivativeNearFromState (34487602412373 / 160000000000) 1 (IntervalRat.scale (275 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (23028071718 / 1000000000000) (23028073003 / 1000000000000), orderedInterval (-49279567923 / 1000000000000) (-49279566638 / 1000000000000)))) (orderedInterval (5448583756 / 1000000000000) (5448583941 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 1) <| besselDerivativeNearFromState (25403411844349 / 160000000000) 1 (IntervalRat.scale (275 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (39087727790 / 1000000000000) (39087746787 / 1000000000000), orderedInterval (-49940952387 / 1000000000000) (-49940933390 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 1) <| besselDerivativeNearFromState (43529179182577 / 160000000000) 1 (IntervalRat.scale (275 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (22177012367 / 1000000000000) (22177013813 / 1000000000000), orderedInterval (-43031486546 / 1000000000000) (-43031485100 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 1) <| besselDerivativeNearFromState (32063396370643 / 160000000000) 1 (IntervalRat.scale (275 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (6695409514 / 1000000000000) (6695409515 / 1000000000000), orderedInterval (55947446390 / 1000000000000) (55947446391 / 1000000000000)))) (orderedInterval (4596766252 / 1000000000000) (4596766354 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate263_chunkChecks1_1 :
    compactCertificate263.chunkChecks (1 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 1) <| besselDerivativeNearFromState (49193495504989 / 160000000000) 1 (IntervalRat.scale (275 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (16380901921 / 1000000000000) (16380901922 / 1000000000000), orderedInterval (42426276324 / 1000000000000) (42426276325 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 1) <| besselDerivativeNearFromState (28401877872181 / 160000000000) 1 (IntervalRat.scale (275 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (41875412092 / 1000000000000) (41875459430 / 1000000000000), orderedInterval (-42929200912 / 1000000000000) (-42929153574 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 1) <| besselDerivativeNearFromState (50399630689529 / 160000000000) 1 (IntervalRat.scale (275 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (44893587267 / 1000000000000) (44893587580 / 1000000000000), orderedInterval (-2436262372 / 1000000000000) (-2436262059 / 1000000000000)))) (orderedInterval (-21756574229 / 1000000000000) (-21756569485 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 1) <| besselDerivativeNearFromState (47089872658301 / 160000000000) 1 (IntervalRat.scale (275 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-9833105338 / 1000000000000) (-9833105299 / 1000000000000), orderedInterval (45474299945 / 1000000000000) (45474299984 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 1) <| besselDerivativeNearFromState (33605555096333 / 160000000000) 1 (IntervalRat.scale (275 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-17986595608 / 1000000000000) (-17986595607 / 1000000000000), orderedInterval (-51990928253 / 1000000000000) (-51990928252 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 1) <| besselDerivativeNearFromState (38105117766507 / 160000000000) 1 (IntervalRat.scale (275 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (9297788530 / 1000000000000) (9297788531 / 1000000000000), orderedInterval (50839760502 / 1000000000000) (50839760503 / 1000000000000)))) (orderedInterval (-9712766035 / 1000000000000) (-9712766006 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 1) <| besselDerivativeNearFromState (31768074535483 / 160000000000) 1 (IntervalRat.scale (275 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-55937717566 / 1000000000000) (-55937717560 / 1000000000000), orderedInterval (-8651144362 / 1000000000000) (-8651144356 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 1) <| besselDerivativeNearFromState (28068057281143 / 160000000000) 1 (IntervalRat.scale (275 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (16697467891 / 1000000000000) (16697467892 / 1000000000000), orderedInterval (57833438598 / 1000000000000) (57833438599 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 1) <| besselDerivativeNearFromState (8135217005157 / 32000000000) 1 (IntervalRat.scale (275 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-25789597991 / 1000000000000) (-25789597990 / 1000000000000), orderedInterval (-42833453445 / 1000000000000) (-42833453444 / 1000000000000)))) (orderedInterval (-6394446211 / 1000000000000) (-6394446191 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate263_chunkChecks1_2 :
    compactCertificate263.chunkChecks (1 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 1) <| besselDerivativeNearFromState (22502438369279 / 160000000000) 1 (IntervalRat.scale (275 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-3569514397 / 1000000000000) (-3569514394 / 1000000000000), orderedInterval (-67172653511 / 1000000000000) (-67172653508 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 1) <| besselDerivativeNearFromState (19075566213319 / 160000000000) 1 (IntervalRat.scale (275 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (42821268052 / 1000000000000) (42821268053 / 1000000000000), orderedInterval (59032959440 / 1000000000000) (59032959441 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 1) <| besselDerivativeNearFromState (11936603629357 / 160000000000) 1 (IntervalRat.scale (275 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-990999342 / 1000000000000) (-990999332 / 1000000000000), orderedInterval (92378471741 / 1000000000000) (92378471750 / 1000000000000)))) (orderedInterval (9720314252 / 1000000000000) (9720314285 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 1) <| besselDerivativeNearFromState (6419545131219 / 160000000000) 1 (IntervalRat.scale (275 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-8022755518 / 1000000000000) (-8022755514 / 1000000000000), orderedInterval (-125613575151 / 1000000000000) (-125613575147 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 1) <| besselDerivativeNearFromState (17430313810657 / 160000000000) 1 (IntervalRat.scale (275 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (17578701136 / 1000000000000) (17578701327 / 1000000000000), orderedInterval (-74477173416 / 1000000000000) (-74477173225 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 1) <| besselDerivativeNearFromState (23799603345089 / 160000000000) 1 (IntervalRat.scale (275 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-62373050050 / 1000000000000) (-62373047644 / 1000000000000), orderedInterval (19944172919 / 1000000000000) (19944175325 / 1000000000000)))) (orderedInterval (361975222 / 1000000000000) (361975440 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 1) <| besselDerivativeNearFromState (10063396370643 / 160000000000) 1 (IntervalRat.scale (275 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (75435559729 / 1000000000000) (75435559730 / 1000000000000), orderedInterval (65967499419 / 1000000000000) (65967499420 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 1) <| besselDerivativeNearFromState (40907147543603 / 160000000000) 1 (IntervalRat.scale (275 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-45668679804 / 1000000000000) (-45668666758 / 1000000000000), orderedInterval (20198456837 / 1000000000000) (20198469882 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 1) <| besselDerivativeNearFromState (27324078755677 / 160000000000) 1 (IntervalRat.scale (275 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (57491848335 / 1000000000000) (57491852396 / 1000000000000), orderedInterval (-20722929546 / 1000000000000) (-20722925485 / 1000000000000)))) (orderedInterval (1953793088 / 1000000000000) (1953796063 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate263_chunkChecks1 :
    compactCertificate263.chunkChecks (1 : Fin 5) 0 9 = true :=
  compactCertificate263.chunkChecks_nine_of_three (1 : Fin 5) compactCertificate263_chunkChecks1_0
    compactCertificate263_chunkChecks1_1 compactCertificate263_chunkChecks1_2

theorem compactCertificate263_chunkChecks2_0 :
    compactCertificate263.chunkChecks (2 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 2) <| besselDerivativeNearFromState (275 / 2) 2 (IntervalRat.scale (275 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (3700584730 / 1000000000000) (3700584733 / 1000000000000), orderedInterval (67929888147 / 1000000000000) (67929888150 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 2) <| besselDerivativeNearFromState (16205100426911 / 160000000000) 2 (IntervalRat.scale (275 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (79230870949 / 1000000000000) (79230870968 / 1000000000000), orderedInterval (2440197056 / 1000000000000) (2440197075 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 2) <| besselDerivativeNearFromState (5240396523263 / 32000000000) 2 (IntervalRat.scale (275 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (57748025074 / 1000000000000) (57748025075 / 1000000000000), orderedInterval (23331402901 / 1000000000000) (23331402902 / 1000000000000)))) (orderedInterval (-6881979569 / 1000000000000) (-6881979554 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 2) <| besselDerivativeNearFromState (4728607888477 / 160000000000) 2 (IntervalRat.scale (275 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-129500623852 / 1000000000000) (-129500614709 / 1000000000000), orderedInterval (71247679566 / 1000000000000) (71247688708 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 2) <| besselDerivativeNearFromState (12701705922169 / 160000000000) 2 (IntervalRat.scale (275 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-89394674006 / 1000000000000) (-89394673938 / 1000000000000), orderedInterval (5832148508 / 1000000000000) (5832148575 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 2) <| besselDerivativeNearFromState (34487602412373 / 160000000000) 2 (IntervalRat.scale (275 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (23028071718 / 1000000000000) (23028073003 / 1000000000000), orderedInterval (-49279567923 / 1000000000000) (-49279566638 / 1000000000000)))) (orderedInterval (5006400806 / 1000000000000) (5006401064 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 2) <| besselDerivativeNearFromState (25403411844349 / 160000000000) 2 (IntervalRat.scale (275 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (39087727790 / 1000000000000) (39087746787 / 1000000000000), orderedInterval (-49940952387 / 1000000000000) (-49940933390 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 2) <| besselDerivativeNearFromState (43529179182577 / 160000000000) 2 (IntervalRat.scale (275 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (22177012367 / 1000000000000) (22177013813 / 1000000000000), orderedInterval (-43031486546 / 1000000000000) (-43031485100 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 2) <| besselDerivativeNearFromState (32063396370643 / 160000000000) 2 (IntervalRat.scale (275 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (6695409514 / 1000000000000) (6695409515 / 1000000000000), orderedInterval (55947446390 / 1000000000000) (55947446391 / 1000000000000)))) (orderedInterval (2300728153 / 1000000000000) (2300728353 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate263_chunkChecks2_1 :
    compactCertificate263.chunkChecks (2 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 2) <| besselDerivativeNearFromState (49193495504989 / 160000000000) 2 (IntervalRat.scale (275 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (16380901921 / 1000000000000) (16380901922 / 1000000000000), orderedInterval (42426276324 / 1000000000000) (42426276325 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 2) <| besselDerivativeNearFromState (28401877872181 / 160000000000) 2 (IntervalRat.scale (275 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (41875412092 / 1000000000000) (41875459430 / 1000000000000), orderedInterval (-42929200912 / 1000000000000) (-42929153574 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 2) <| besselDerivativeNearFromState (50399630689529 / 160000000000) 2 (IntervalRat.scale (275 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (44893587267 / 1000000000000) (44893587580 / 1000000000000), orderedInterval (-2436262372 / 1000000000000) (-2436262059 / 1000000000000)))) (orderedInterval (-23952718075 / 1000000000000) (-23952711718 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 2) <| besselDerivativeNearFromState (47089872658301 / 160000000000) 2 (IntervalRat.scale (275 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-9833105338 / 1000000000000) (-9833105299 / 1000000000000), orderedInterval (45474299945 / 1000000000000) (45474299984 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 2) <| besselDerivativeNearFromState (33605555096333 / 160000000000) 2 (IntervalRat.scale (275 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-17986595608 / 1000000000000) (-17986595607 / 1000000000000), orderedInterval (-51990928253 / 1000000000000) (-51990928252 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 2) <| besselDerivativeNearFromState (38105117766507 / 160000000000) 2 (IntervalRat.scale (275 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (9297788530 / 1000000000000) (9297788531 / 1000000000000), orderedInterval (50839760502 / 1000000000000) (50839760503 / 1000000000000)))) (orderedInterval (3367175561 / 1000000000000) (3367175609 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 2) <| besselDerivativeNearFromState (31768074535483 / 160000000000) 2 (IntervalRat.scale (275 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-55937717566 / 1000000000000) (-55937717560 / 1000000000000), orderedInterval (-8651144362 / 1000000000000) (-8651144356 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 2) <| besselDerivativeNearFromState (28068057281143 / 160000000000) 2 (IntervalRat.scale (275 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (16697467891 / 1000000000000) (16697467892 / 1000000000000), orderedInterval (57833438598 / 1000000000000) (57833438599 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 2) <| besselDerivativeNearFromState (8135217005157 / 32000000000) 2 (IntervalRat.scale (275 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-25789597991 / 1000000000000) (-25789597990 / 1000000000000), orderedInterval (-42833453445 / 1000000000000) (-42833453444 / 1000000000000)))) (orderedInterval (5206031896 / 1000000000000) (5206031926 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate263_chunkChecks2_2 :
    compactCertificate263.chunkChecks (2 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 2) <| besselDerivativeNearFromState (22502438369279 / 160000000000) 2 (IntervalRat.scale (275 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-3569514397 / 1000000000000) (-3569514394 / 1000000000000), orderedInterval (-67172653511 / 1000000000000) (-67172653508 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 2) <| besselDerivativeNearFromState (19075566213319 / 160000000000) 2 (IntervalRat.scale (275 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (42821268052 / 1000000000000) (42821268053 / 1000000000000), orderedInterval (59032959440 / 1000000000000) (59032959441 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 2) <| besselDerivativeNearFromState (11936603629357 / 160000000000) 2 (IntervalRat.scale (275 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-990999342 / 1000000000000) (-990999332 / 1000000000000), orderedInterval (92378471741 / 1000000000000) (92378471750 / 1000000000000)))) (orderedInterval (1163853317 / 1000000000000) (1163853349 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 2) <| besselDerivativeNearFromState (6419545131219 / 160000000000) 2 (IntervalRat.scale (275 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-8022755518 / 1000000000000) (-8022755514 / 1000000000000), orderedInterval (-125613575151 / 1000000000000) (-125613575147 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 2) <| besselDerivativeNearFromState (17430313810657 / 160000000000) 2 (IntervalRat.scale (275 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (17578701136 / 1000000000000) (17578701327 / 1000000000000), orderedInterval (-74477173416 / 1000000000000) (-74477173225 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 2) <| besselDerivativeNearFromState (23799603345089 / 160000000000) 2 (IntervalRat.scale (275 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-62373050050 / 1000000000000) (-62373047644 / 1000000000000), orderedInterval (19944172919 / 1000000000000) (19944175325 / 1000000000000)))) (orderedInterval (-5359136290 / 1000000000000) (-5359136055 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 2) <| besselDerivativeNearFromState (10063396370643 / 160000000000) 2 (IntervalRat.scale (275 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (75435559729 / 1000000000000) (75435559730 / 1000000000000), orderedInterval (65967499419 / 1000000000000) (65967499420 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 2) <| besselDerivativeNearFromState (40907147543603 / 160000000000) 2 (IntervalRat.scale (275 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-45668679804 / 1000000000000) (-45668666758 / 1000000000000), orderedInterval (20198456837 / 1000000000000) (20198469882 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 2) <| besselDerivativeNearFromState (27324078755677 / 160000000000) 2 (IntervalRat.scale (275 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (57491848335 / 1000000000000) (57491852396 / 1000000000000), orderedInterval (-20722929546 / 1000000000000) (-20722925485 / 1000000000000)))) (orderedInterval (3677340457 / 1000000000000) (3677345405 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate263_chunkChecks2 :
    compactCertificate263.chunkChecks (2 : Fin 5) 0 9 = true :=
  compactCertificate263.chunkChecks_nine_of_three (2 : Fin 5) compactCertificate263_chunkChecks2_0
    compactCertificate263_chunkChecks2_1 compactCertificate263_chunkChecks2_2

theorem compactCertificate263_chunkChecks3_0 :
    compactCertificate263.chunkChecks (3 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 3) <| besselDerivativeNearFromState (275 / 2) 3 (IntervalRat.scale (275 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (3700584730 / 1000000000000) (3700584733 / 1000000000000), orderedInterval (67929888147 / 1000000000000) (67929888150 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 3) <| besselDerivativeNearFromState (16205100426911 / 160000000000) 3 (IntervalRat.scale (275 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (79230870949 / 1000000000000) (79230870968 / 1000000000000), orderedInterval (2440197056 / 1000000000000) (2440197075 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 3) <| besselDerivativeNearFromState (5240396523263 / 32000000000) 3 (IntervalRat.scale (275 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (57748025074 / 1000000000000) (57748025075 / 1000000000000), orderedInterval (23331402901 / 1000000000000) (23331402902 / 1000000000000)))) (orderedInterval (-29195545300 / 1000000000000) (-29195545284 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 3) <| besselDerivativeNearFromState (4728607888477 / 160000000000) 3 (IntervalRat.scale (275 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-129500623852 / 1000000000000) (-129500614709 / 1000000000000), orderedInterval (71247679566 / 1000000000000) (71247688708 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 3) <| besselDerivativeNearFromState (12701705922169 / 160000000000) 3 (IntervalRat.scale (275 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-89394674006 / 1000000000000) (-89394673938 / 1000000000000), orderedInterval (5832148508 / 1000000000000) (5832148575 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 3) <| besselDerivativeNearFromState (34487602412373 / 160000000000) 3 (IntervalRat.scale (275 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (23028071718 / 1000000000000) (23028073003 / 1000000000000), orderedInterval (-49279567923 / 1000000000000) (-49279566638 / 1000000000000)))) (orderedInterval (-13565088844 / 1000000000000) (-13565088450 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 3) <| besselDerivativeNearFromState (25403411844349 / 160000000000) 3 (IntervalRat.scale (275 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (39087727790 / 1000000000000) (39087746787 / 1000000000000), orderedInterval (-49940952387 / 1000000000000) (-49940933390 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 3) <| besselDerivativeNearFromState (43529179182577 / 160000000000) 3 (IntervalRat.scale (275 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (22177012367 / 1000000000000) (22177013813 / 1000000000000), orderedInterval (-43031486546 / 1000000000000) (-43031485100 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 3) <| besselDerivativeNearFromState (32063396370643 / 160000000000) 3 (IntervalRat.scale (275 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (6695409514 / 1000000000000) (6695409515 / 1000000000000), orderedInterval (55947446390 / 1000000000000) (55947446391 / 1000000000000)))) (orderedInterval (-14483207162 / 1000000000000) (-14483206771 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate263_chunkChecks3_1 :
    compactCertificate263.chunkChecks (3 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 3) <| besselDerivativeNearFromState (49193495504989 / 160000000000) 3 (IntervalRat.scale (275 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (16380901921 / 1000000000000) (16380901922 / 1000000000000), orderedInterval (42426276324 / 1000000000000) (42426276325 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 3) <| besselDerivativeNearFromState (28401877872181 / 160000000000) 3 (IntervalRat.scale (275 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (41875412092 / 1000000000000) (41875459430 / 1000000000000), orderedInterval (-42929200912 / 1000000000000) (-42929153574 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 3) <| besselDerivativeNearFromState (50399630689529 / 160000000000) 3 (IntervalRat.scale (275 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (44893587267 / 1000000000000) (44893587580 / 1000000000000), orderedInterval (-2436262372 / 1000000000000) (-2436262059 / 1000000000000)))) (orderedInterval (95465270201 / 1000000000000) (95465278860 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 3) <| besselDerivativeNearFromState (47089872658301 / 160000000000) 3 (IntervalRat.scale (275 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-9833105338 / 1000000000000) (-9833105299 / 1000000000000), orderedInterval (45474299945 / 1000000000000) (45474299984 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 3) <| besselDerivativeNearFromState (33605555096333 / 160000000000) 3 (IntervalRat.scale (275 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-17986595608 / 1000000000000) (-17986595607 / 1000000000000), orderedInterval (-51990928253 / 1000000000000) (-51990928252 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 3) <| besselDerivativeNearFromState (38105117766507 / 160000000000) 3 (IntervalRat.scale (275 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (9297788530 / 1000000000000) (9297788531 / 1000000000000), orderedInterval (50839760502 / 1000000000000) (50839760503 / 1000000000000)))) (orderedInterval (26885723273 / 1000000000000) (26885723356 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 3) <| besselDerivativeNearFromState (31768074535483 / 160000000000) 3 (IntervalRat.scale (275 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-55937717566 / 1000000000000) (-55937717560 / 1000000000000), orderedInterval (-8651144362 / 1000000000000) (-8651144356 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 3) <| besselDerivativeNearFromState (28068057281143 / 160000000000) 3 (IntervalRat.scale (275 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (16697467891 / 1000000000000) (16697467892 / 1000000000000), orderedInterval (57833438598 / 1000000000000) (57833438599 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 3) <| besselDerivativeNearFromState (8135217005157 / 32000000000) 3 (IntervalRat.scale (275 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-25789597991 / 1000000000000) (-25789597990 / 1000000000000), orderedInterval (-42833453445 / 1000000000000) (-42833453444 / 1000000000000)))) (orderedInterval (14067294736 / 1000000000000) (14067294780 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate263_chunkChecks3_2 :
    compactCertificate263.chunkChecks (3 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 3) <| besselDerivativeNearFromState (22502438369279 / 160000000000) 3 (IntervalRat.scale (275 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-3569514397 / 1000000000000) (-3569514394 / 1000000000000), orderedInterval (-67172653511 / 1000000000000) (-67172653508 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 3) <| besselDerivativeNearFromState (19075566213319 / 160000000000) 3 (IntervalRat.scale (275 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (42821268052 / 1000000000000) (42821268053 / 1000000000000), orderedInterval (59032959440 / 1000000000000) (59032959441 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 3) <| besselDerivativeNearFromState (11936603629357 / 160000000000) 3 (IntervalRat.scale (275 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-990999342 / 1000000000000) (-990999332 / 1000000000000), orderedInterval (92378471741 / 1000000000000) (92378471750 / 1000000000000)))) (orderedInterval (-9803428924 / 1000000000000) (-9803428893 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 3) <| besselDerivativeNearFromState (6419545131219 / 160000000000) 3 (IntervalRat.scale (275 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-8022755518 / 1000000000000) (-8022755514 / 1000000000000), orderedInterval (-125613575151 / 1000000000000) (-125613575147 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 3) <| besselDerivativeNearFromState (17430313810657 / 160000000000) 3 (IntervalRat.scale (275 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (17578701136 / 1000000000000) (17578701327 / 1000000000000), orderedInterval (-74477173416 / 1000000000000) (-74477173225 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 3) <| besselDerivativeNearFromState (23799603345089 / 160000000000) 3 (IntervalRat.scale (275 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-62373050050 / 1000000000000) (-62373047644 / 1000000000000), orderedInterval (19944172919 / 1000000000000) (19944175325 / 1000000000000)))) (orderedInterval (1076158335 / 1000000000000) (1076158588 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 3) <| besselDerivativeNearFromState (10063396370643 / 160000000000) 3 (IntervalRat.scale (275 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (75435559729 / 1000000000000) (75435559730 / 1000000000000), orderedInterval (65967499419 / 1000000000000) (65967499420 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 3) <| besselDerivativeNearFromState (40907147543603 / 160000000000) 3 (IntervalRat.scale (275 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-45668679804 / 1000000000000) (-45668666758 / 1000000000000), orderedInterval (20198456837 / 1000000000000) (20198469882 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 3) <| besselDerivativeNearFromState (27324078755677 / 160000000000) 3 (IntervalRat.scale (275 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (57491848335 / 1000000000000) (57491852396 / 1000000000000), orderedInterval (-20722929546 / 1000000000000) (-20722925485 / 1000000000000)))) (orderedInterval (3056184694 / 1000000000000) (3056193138 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate263_chunkChecks3 :
    compactCertificate263.chunkChecks (3 : Fin 5) 0 9 = true :=
  compactCertificate263.chunkChecks_nine_of_three (3 : Fin 5) compactCertificate263_chunkChecks3_0
    compactCertificate263_chunkChecks3_1 compactCertificate263_chunkChecks3_2

theorem compactCertificate263_chunkChecks4_0 :
    compactCertificate263.chunkChecks (4 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 4) <| besselDerivativeNearFromState (275 / 2) 4 (IntervalRat.scale (275 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (3700584730 / 1000000000000) (3700584733 / 1000000000000), orderedInterval (67929888147 / 1000000000000) (67929888150 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 4) <| besselDerivativeNearFromState (16205100426911 / 160000000000) 4 (IntervalRat.scale (275 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (79230870949 / 1000000000000) (79230870968 / 1000000000000), orderedInterval (2440197056 / 1000000000000) (2440197075 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 4) <| besselDerivativeNearFromState (5240396523263 / 32000000000) 4 (IntervalRat.scale (275 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (57748025074 / 1000000000000) (57748025075 / 1000000000000), orderedInterval (23331402901 / 1000000000000) (23331402902 / 1000000000000)))) (orderedInterval (8926793755 / 1000000000000) (8926793774 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 4) <| besselDerivativeNearFromState (4728607888477 / 160000000000) 4 (IntervalRat.scale (275 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-129500623852 / 1000000000000) (-129500614709 / 1000000000000), orderedInterval (71247679566 / 1000000000000) (71247688708 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 4) <| besselDerivativeNearFromState (12701705922169 / 160000000000) 4 (IntervalRat.scale (275 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-89394674006 / 1000000000000) (-89394673938 / 1000000000000), orderedInterval (5832148508 / 1000000000000) (5832148575 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 4) <| besselDerivativeNearFromState (34487602412373 / 160000000000) 4 (IntervalRat.scale (275 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (23028071718 / 1000000000000) (23028073003 / 1000000000000), orderedInterval (-49279567923 / 1000000000000) (-49279566638 / 1000000000000)))) (orderedInterval (-10048194857 / 1000000000000) (-10048194239 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 4) <| besselDerivativeNearFromState (25403411844349 / 160000000000) 4 (IntervalRat.scale (275 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (39087727790 / 1000000000000) (39087746787 / 1000000000000), orderedInterval (-49940952387 / 1000000000000) (-49940933390 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 4) <| besselDerivativeNearFromState (43529179182577 / 160000000000) 4 (IntervalRat.scale (275 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (22177012367 / 1000000000000) (22177013813 / 1000000000000), orderedInterval (-43031486546 / 1000000000000) (-43031485100 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 4) <| besselDerivativeNearFromState (32063396370643 / 160000000000) 4 (IntervalRat.scale (275 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (6695409514 / 1000000000000) (6695409515 / 1000000000000), orderedInterval (55947446390 / 1000000000000) (55947446391 / 1000000000000)))) (orderedInterval (-9542611008 / 1000000000000) (-9542610238 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate263_chunkChecks4_1 :
    compactCertificate263.chunkChecks (4 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 4) <| besselDerivativeNearFromState (49193495504989 / 160000000000) 4 (IntervalRat.scale (275 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (16380901921 / 1000000000000) (16380901922 / 1000000000000), orderedInterval (42426276324 / 1000000000000) (42426276325 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 4) <| besselDerivativeNearFromState (28401877872181 / 160000000000) 4 (IntervalRat.scale (275 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (41875412092 / 1000000000000) (41875459430 / 1000000000000), orderedInterval (-42929200912 / 1000000000000) (-42929153574 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 4) <| besselDerivativeNearFromState (50399630689529 / 160000000000) 4 (IntervalRat.scale (275 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (44893587267 / 1000000000000) (44893587580 / 1000000000000), orderedInterval (-2436262372 / 1000000000000) (-2436262059 / 1000000000000)))) (orderedInterval (110240696592 / 1000000000000) (110240708860 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 4) <| besselDerivativeNearFromState (47089872658301 / 160000000000) 4 (IntervalRat.scale (275 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-9833105338 / 1000000000000) (-9833105299 / 1000000000000), orderedInterval (45474299945 / 1000000000000) (45474299984 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 4) <| besselDerivativeNearFromState (33605555096333 / 160000000000) 4 (IntervalRat.scale (275 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-17986595608 / 1000000000000) (-17986595607 / 1000000000000), orderedInterval (-51990928253 / 1000000000000) (-51990928252 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 4) <| besselDerivativeNearFromState (38105117766507 / 160000000000) 4 (IntervalRat.scale (275 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (9297788530 / 1000000000000) (9297788531 / 1000000000000), orderedInterval (50839760502 / 1000000000000) (50839760503 / 1000000000000)))) (orderedInterval (-6348452659 / 1000000000000) (-6348452513 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 4) <| besselDerivativeNearFromState (31768074535483 / 160000000000) 4 (IntervalRat.scale (275 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-55937717566 / 1000000000000) (-55937717560 / 1000000000000), orderedInterval (-8651144362 / 1000000000000) (-8651144356 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 4) <| besselDerivativeNearFromState (28068057281143 / 160000000000) 4 (IntervalRat.scale (275 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (16697467891 / 1000000000000) (16697467892 / 1000000000000), orderedInterval (57833438598 / 1000000000000) (57833438599 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 4) <| besselDerivativeNearFromState (8135217005157 / 32000000000) 4 (IntervalRat.scale (275 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-25789597991 / 1000000000000) (-25789597990 / 1000000000000), orderedInterval (-42833453445 / 1000000000000) (-42833453444 / 1000000000000)))) (orderedInterval (-13260943246 / 1000000000000) (-13260943175 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate263_chunkChecks4_2 :
    compactCertificate263.chunkChecks (4 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 4) <| besselDerivativeNearFromState (22502438369279 / 160000000000) 4 (IntervalRat.scale (275 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-3569514397 / 1000000000000) (-3569514394 / 1000000000000), orderedInterval (-67172653511 / 1000000000000) (-67172653508 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 4) <| besselDerivativeNearFromState (19075566213319 / 160000000000) 4 (IntervalRat.scale (275 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (42821268052 / 1000000000000) (42821268053 / 1000000000000), orderedInterval (59032959440 / 1000000000000) (59032959441 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 4) <| besselDerivativeNearFromState (11936603629357 / 160000000000) 4 (IntervalRat.scale (275 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-990999342 / 1000000000000) (-990999332 / 1000000000000), orderedInterval (92378471741 / 1000000000000) (92378471750 / 1000000000000)))) (orderedInterval (-605370859 / 1000000000000) (-605370829 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 4) <| besselDerivativeNearFromState (6419545131219 / 160000000000) 4 (IntervalRat.scale (275 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-8022755518 / 1000000000000) (-8022755514 / 1000000000000), orderedInterval (-125613575151 / 1000000000000) (-125613575147 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 4) <| besselDerivativeNearFromState (17430313810657 / 160000000000) 4 (IntervalRat.scale (275 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (17578701136 / 1000000000000) (17578701327 / 1000000000000), orderedInterval (-74477173416 / 1000000000000) (-74477173225 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 4) <| besselDerivativeNearFromState (23799603345089 / 160000000000) 4 (IntervalRat.scale (275 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-62373050050 / 1000000000000) (-62373047644 / 1000000000000), orderedInterval (19944172919 / 1000000000000) (19944175325 / 1000000000000)))) (orderedInterval (6374872949 / 1000000000000) (6374873223 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 4) <| besselDerivativeNearFromState (10063396370643 / 160000000000) 4 (IntervalRat.scale (275 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (75435559729 / 1000000000000) (75435559730 / 1000000000000), orderedInterval (65967499419 / 1000000000000) (65967499420 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 4) <| besselDerivativeNearFromState (40907147543603 / 160000000000) 4 (IntervalRat.scale (275 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-45668679804 / 1000000000000) (-45668666758 / 1000000000000), orderedInterval (20198456837 / 1000000000000) (20198469882 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 4) <| besselDerivativeNearFromState (27324078755677 / 160000000000) 4 (IntervalRat.scale (275 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (57491848335 / 1000000000000) (57491852396 / 1000000000000), orderedInterval (-20722929546 / 1000000000000) (-20722925485 / 1000000000000)))) (orderedInterval (18746042007 / 1000000000000) (18746056831 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate263_chunkChecks4 :
    compactCertificate263.chunkChecks (4 : Fin 5) 0 9 = true :=
  compactCertificate263.chunkChecks_nine_of_three (4 : Fin 5) compactCertificate263_chunkChecks4_0
    compactCertificate263_chunkChecks4_1 compactCertificate263_chunkChecks4_2

theorem compactCertificate263_chunks :
    ∀ r : Fin 5, ∀ b, compactCertificate263.chunkCheck r b = true :=
  compactCertificate263.chunkChecks_all (by
    intro r
    fin_cases r
    · exact compactCertificate263_chunkChecks0
    · exact compactCertificate263_chunkChecks1
    · exact compactCertificate263_chunkChecks2
    · exact compactCertificate263_chunkChecks3
    · exact compactCertificate263_chunkChecks4)

theorem compactCertificate263_coefficient0 :
    compactCertificate263.coefficientCheck (0 : Fin 5) = true := by
  norm_num [CompactCertificate.coefficientCheck, intervalFinSumHull,
    compactCertificate263, rationalIntervalSubset, orderedInterval, Fin.sum_univ_succ]

theorem compactCertificate263_coefficient1 :
    compactCertificate263.coefficientCheck (1 : Fin 5) = true := by
  norm_num [CompactCertificate.coefficientCheck, intervalFinSumHull,
    compactCertificate263, rationalIntervalSubset, orderedInterval, Fin.sum_univ_succ]

theorem compactCertificate263_coefficient2 :
    compactCertificate263.coefficientCheck (2 : Fin 5) = true := by
  norm_num [CompactCertificate.coefficientCheck, intervalFinSumHull,
    compactCertificate263, rationalIntervalSubset, orderedInterval, Fin.sum_univ_succ]

theorem compactCertificate263_coefficient3 :
    compactCertificate263.coefficientCheck (3 : Fin 5) = true := by
  norm_num [CompactCertificate.coefficientCheck, intervalFinSumHull,
    compactCertificate263, rationalIntervalSubset, orderedInterval, Fin.sum_univ_succ]

theorem compactCertificate263_coefficient4 :
    compactCertificate263.coefficientCheck (4 : Fin 5) = true := by
  norm_num [CompactCertificate.coefficientCheck, intervalFinSumHull,
    compactCertificate263, rationalIntervalSubset, orderedInterval, Fin.sum_univ_succ]

theorem compactCertificate263_coefficients : ∀ r : Fin 5,
    compactCertificate263.coefficientCheck r = true := by
  intro r
  fin_cases r
  · exact compactCertificate263_coefficient0
  · exact compactCertificate263_coefficient1
  · exact compactCertificate263_coefficient2
  · exact compactCertificate263_coefficient3
  · exact compactCertificate263_coefficient4

theorem compactCertificate263_lower : (1 : ℚ) ≤ compactCertificate263.output.lo := by
  norm_num [CompactCertificate.output, CompactCertificate.interval,
    CompactCertificate.coefficientTargetNat, compactCertificate263, dualConstant,
    intervalTaylorSum, intervalPow, intervalSub, intervalMaxAbs, widenInterval,
    rationalErrorInterval, orderedInterval, IntervalRat.add, IntervalRat.mul, IntervalRat.scale,
    IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4]

theorem compactCertificate263_proves {t : ℝ} (ht : t ∈ compactCertificate263.interval) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t :=
  compactCertificate263.proves compactCertificate263_states compactCertificate263_chunks
    compactCertificate263_coefficients compactCertificate263_lower ht

end Erdos232
