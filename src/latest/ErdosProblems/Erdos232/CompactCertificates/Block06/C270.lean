/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, OpenAI Codex
-/
import ErdosProblems.Erdos232.CompactBase

open LeanCert.Core
namespace Erdos232

def compactCertificate270 : CompactCertificate where
  left := 144
  right := 145
  center := 289 / 2
  grid := fun i =>
    match i.val with
    | 0 => 46
    | 1 => 34
    | 2 => 55
    | 3 => 10
    | 4 => 27
    | 5 => 72
    | 6 => 53
    | 7 => 91
    | 8 => 67
    | 9 => 103
    | 10 => 59
    | 11 => 105
    | 12 => 99
    | 13 => 70
    | 14 => 80
    | 15 => 66
    | 16 => 59
    | 17 => 85
    | 18 => 47
    | 19 => 40
    | 20 => 25
    | 21 => 13
    | 22 => 36
    | 23 => 50
    | 24 => 21
    | 25 => 86
    | _ => 57
  point := fun i =>
    match i.val with
    | 0 => 289 / 2
    | 1 => 425752183943389 / 4000000000000
    | 2 => 137679508656637 / 800000000000
    | 3 => 124233425433623 / 4000000000000
    | 4 => 333708455591531 / 4000000000000
    | 5 => 906083372470527 / 4000000000000
    | 6 => 667416911183351 / 4000000000000
    | 7 => 1143630253069523 / 4000000000000
    | 8 => 842392868283257 / 4000000000000
    | 9 => 1292447290994711 / 4000000000000
    | 10 => 746194791369119 / 4000000000000
    | 11 => 1324135751752171 / 4000000000000
    | 12 => 1237179381658999 / 4000000000000
    | 13 => 882909583894567 / 4000000000000
    | 14 => 1001125366774593 / 4000000000000
    | 15 => 834633958250417 / 4000000000000
    | 16 => 737424414022757 / 4000000000000
    | 17 => 213734337680943 / 800000000000
    | 18 => 591200426247421 / 4000000000000
    | 19 => 501167148695381 / 4000000000000
    | 20 => 313607131716743 / 4000000000000
    | 21 => 168658958447481 / 4000000000000
    | 22 => 457941881025443 / 4000000000000
    | 23 => 625280487884611 / 4000000000000
    | 24 => 264392868283257 / 4000000000000
    | 25 => 1074742330918297 / 4000000000000
    | _ => 717878069126423 / 4000000000000
  state := fun i =>
    match i.val with
    | 0 => (orderedInterval (46266539573 / 1000000000000) (46266539574 / 1000000000000), orderedInterval (47432779573 / 1000000000000) (47432779574 / 1000000000000))
    | 1 => (orderedInterval (30693956719 / 1000000000000) (30693956720 / 1000000000000), orderedInterval (70842125127 / 1000000000000) (70842125128 / 1000000000000))
    | 2 => (orderedInterval (-5857749444 / 1000000000000) (-5857749443 / 1000000000000), orderedInterval (-60520923335 / 1000000000000) (-60520923334 / 1000000000000))
    | 3 => (orderedInterval (58872147044 / 1000000000000) (58872147045 / 1000000000000), orderedInterval (129564397746 / 1000000000000) (129564397747 / 1000000000000))
    | 4 => (orderedInterval (50184452938 / 1000000000000) (50184469275 / 1000000000000), orderedInterval (-71801927064 / 1000000000000) (-71801910727 / 1000000000000))
    | 5 => (orderedInterval (47507991852 / 1000000000000) (47507991853 / 1000000000000), orderedInterval (23419830676 / 1000000000000) (23419830677 / 1000000000000))
    | 6 => (orderedInterval (-55981770339 / 1000000000000) (-55981770338 / 1000000000000), orderedInterval (-25936943041 / 1000000000000) (-25936943040 / 1000000000000))
    | 7 => (orderedInterval (-34098875758 / 1000000000000) (-34098875757 / 1000000000000), orderedInterval (-32558298914 / 1000000000000) (-32558298913 / 1000000000000))
    | 8 => (orderedInterval (-42941773340 / 1000000000000) (-42941773339 / 1000000000000), orderedInterval (-34233361825 / 1000000000000) (-34233361824 / 1000000000000))
    | 9 => (orderedInterval (-13658790967 / 1000000000000) (-13658790966 / 1000000000000), orderedInterval (-42212929107 / 1000000000000) (-42212929106 / 1000000000000))
    | 10 => (orderedInterval (-53607018694 / 1000000000000) (-53607010010 / 1000000000000), orderedInterval (23357881610 / 1000000000000) (23357890295 / 1000000000000))
    | 11 => (orderedInterval (-40709931966 / 1000000000000) (-40709918366 / 1000000000000), orderedInterval (16365646468 / 1000000000000) (16365660068 / 1000000000000))
    | 12 => (orderedInterval (36579497501 / 1000000000000) (36579606143 / 1000000000000), orderedInterval (-26896280105 / 1000000000000) (-26896171463 / 1000000000000))
    | 13 => (orderedInterval (53680509408 / 1000000000000) (53680509530 / 1000000000000), orderedInterval (-1729586768 / 1000000000000) (-1729586646 / 1000000000000))
    | 14 => (orderedInterval (-13022766341 / 1000000000000) (-13022766233 / 1000000000000), orderedInterval (48750019881 / 1000000000000) (48750019989 / 1000000000000))
    | 15 => (orderedInterval (47730980351 / 1000000000000) (47731010585 / 1000000000000), orderedInterval (-27912964046 / 1000000000000) (-27912933811 / 1000000000000))
    | 16 => (orderedInterval (12430485404 / 1000000000000) (12430485491 / 1000000000000), orderedInterval (-57468036531 / 1000000000000) (-57468036443 / 1000000000000))
    | 17 => (orderedInterval (-38762037029 / 1000000000000) (-38762037028 / 1000000000000), orderedInterval (-29598124952 / 1000000000000) (-29598124951 / 1000000000000))
    | 18 => (orderedInterval (-52602520725 / 1000000000000) (-52602520724 / 1000000000000), orderedInterval (-39068328262 / 1000000000000) (-39068328261 / 1000000000000))
    | 19 => (orderedInterval (28575624935 / 1000000000000) (28575624936 / 1000000000000), orderedInterval (65189552691 / 1000000000000) (65189552692 / 1000000000000))
    | 20 => (orderedInterval (-54229420118 / 1000000000000) (-54229420117 / 1000000000000), orderedInterval (-71620697946 / 1000000000000) (-71620697945 / 1000000000000))
    | 21 => (orderedInterval (-105660045159 / 1000000000000) (-105660030056 / 1000000000000), orderedInterval (63973094897 / 1000000000000) (63973110000 / 1000000000000))
    | 22 => (orderedInterval (61475730412 / 1000000000000) (61475769038 / 1000000000000), orderedInterval (-42475332391 / 1000000000000) (-42475293765 / 1000000000000))
    | 23 => (orderedInterval (1600844190 / 1000000000000) (1600844193 / 1000000000000), orderedInterval (63791407528 / 1000000000000) (63791407531 / 1000000000000))
    | 24 => (orderedInterval (-77376837147 / 1000000000000) (-77376837146 / 1000000000000), orderedInterval (-59781754593 / 1000000000000) (-59781754592 / 1000000000000))
    | 25 => (orderedInterval (-31597708929 / 1000000000000) (-31597692350 / 1000000000000), orderedInterval (37085425716 / 1000000000000) (37085442295 / 1000000000000))
    | _ => (orderedInterval (-55145829166 / 1000000000000) (-55145829165 / 1000000000000), orderedInterval (-22344328527 / 1000000000000) (-22344328526 / 1000000000000))
  chunkTarget := fun r b =>
    match r.val with
    | 0 =>
      match b.val with
      | 0 => orderedInterval (18280705344 / 1000000000000) (18280705355 / 1000000000000)
      | 1 => orderedInterval (-2183725151 / 1000000000000) (-2183724536 / 1000000000000)
      | 2 => orderedInterval (13927816 / 1000000000000) (13927825 / 1000000000000)
      | 3 => orderedInterval (-7331993436 / 1000000000000) (-7331990801 / 1000000000000)
      | 4 => orderedInterval (4481710732 / 1000000000000) (4481712723 / 1000000000000)
      | 5 => orderedInterval (-1152635034 / 1000000000000) (-1152634665 / 1000000000000)
      | 6 => orderedInterval (5027912893 / 1000000000000) (5027912930 / 1000000000000)
      | 7 => orderedInterval (433645630 / 1000000000000) (433646803 / 1000000000000)
      | _ => orderedInterval (12452475737 / 1000000000000) (12452477127 / 1000000000000)
    | 1 =>
      match b.val with
      | 0 => orderedInterval (15057169846 / 1000000000000) (15057169859 / 1000000000000)
      | 1 => orderedInterval (-4425661273 / 1000000000000) (-4425660908 / 1000000000000)
      | 2 => orderedInterval (781158550 / 1000000000000) (781158565 / 1000000000000)
      | 3 => orderedInterval (24336066101 / 1000000000000) (24336071481 / 1000000000000)
      | 4 => orderedInterval (362177575 / 1000000000000) (362181820 / 1000000000000)
      | 5 => orderedInterval (2329193011 / 1000000000000) (2329193543 / 1000000000000)
      | 6 => orderedInterval (1925059037 / 1000000000000) (1925059071 / 1000000000000)
      | 7 => orderedInterval (-4870033787 / 1000000000000) (-4870032995 / 1000000000000)
      | _ => orderedInterval (-571130881 / 1000000000000) (-571128315 / 1000000000000)
    | 2 =>
      match b.val with
      | 0 => orderedInterval (-18110231585 / 1000000000000) (-18110231571 / 1000000000000)
      | 1 => orderedInterval (7748893377 / 1000000000000) (7748893606 / 1000000000000)
      | 2 => orderedInterval (-1918414649 / 1000000000000) (-1918414623 / 1000000000000)
      | 3 => orderedInterval (24688377024 / 1000000000000) (24688388535 / 1000000000000)
      | 4 => orderedInterval (-9019129332 / 1000000000000) (-9019120242 / 1000000000000)
      | 5 => orderedInterval (3385180772 / 1000000000000) (3385181543 / 1000000000000)
      | 6 => orderedInterval (-7076936229 / 1000000000000) (-7076936196 / 1000000000000)
      | 7 => orderedInterval (886634360 / 1000000000000) (886634956 / 1000000000000)
      | _ => orderedInterval (-24752053512 / 1000000000000) (-24752048745 / 1000000000000)
    | 3 =>
      match b.val with
      | 0 => orderedInterval (-12938635833 / 1000000000000) (-12938635816 / 1000000000000)
      | 1 => orderedInterval (6878385404 / 1000000000000) (6878385562 / 1000000000000)
      | 2 => orderedInterval (-5204118689 / 1000000000000) (-5204118643 / 1000000000000)
      | 3 => orderedInterval (-115725377062 / 1000000000000) (-115725351796 / 1000000000000)
      | 4 => orderedInterval (-2834371311 / 1000000000000) (-2834351892 / 1000000000000)
      | 5 => orderedInterval (-1092538791 / 1000000000000) (-1092537677 / 1000000000000)
      | 6 => orderedInterval (-3857841611 / 1000000000000) (-3857841579 / 1000000000000)
      | 7 => orderedInterval (5733188350 / 1000000000000) (5733188814 / 1000000000000)
      | _ => orderedInterval (11581012657 / 1000000000000) (11581021495 / 1000000000000)
    | _ =>
      match b.val with
      | 0 => orderedInterval (17909210126 / 1000000000000) (17909210145 / 1000000000000)
      | 1 => orderedInterval (-20288098445 / 1000000000000) (-20288098314 / 1000000000000)
      | 2 => orderedInterval (11508680119 / 1000000000000) (11508680205 / 1000000000000)
      | 3 => orderedInterval (-108153312821 / 1000000000000) (-108153256201 / 1000000000000)
      | 4 => orderedInterval (14407430443 / 1000000000000) (14407472082 / 1000000000000)
      | 5 => orderedInterval (-11070886614 / 1000000000000) (-11070884995 / 1000000000000)
      | 6 => orderedInterval (8191690731 / 1000000000000) (8191690762 / 1000000000000)
      | 7 => orderedInterval (-782744908 / 1000000000000) (-782744536 / 1000000000000)
      | _ => orderedInterval (55185157010 / 1000000000000) (55185173469 / 1000000000000)
  coefficientTarget := fun i =>
    match i.val with
    | 0 => orderedInterval (30022024531 / 1000000000000) (30022032761 / 1000000000000)
    | 1 => orderedInterval (34923998179 / 1000000000000) (34924012121 / 1000000000000)
    | 2 => orderedInterval (-24167679774 / 1000000000000) (-24167652737 / 1000000000000)
    | 3 => orderedInterval (-117460296886 / 1000000000000) (-117460241532 / 1000000000000)
    | _ => orderedInterval (-33092874359 / 1000000000000) (-33092757383 / 1000000000000)

theorem compactCertificate270_stateChecks0 :
    compactCertificate270.stateChecks 0 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 46 12 (289 / 2)) (orderedInterval (46266539573 / 1000000000000) (46266539574 / 1000000000000), orderedInterval (47432779573 / 1000000000000) (47432779574 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 34 12 (425752183943389 / 4000000000000)) (orderedInterval (30693956719 / 1000000000000) (30693956720 / 1000000000000), orderedInterval (70842125127 / 1000000000000) (70842125128 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 55 12 (137679508656637 / 800000000000)) (orderedInterval (-5857749444 / 1000000000000) (-5857749443 / 1000000000000), orderedInterval (-60520923335 / 1000000000000) (-60520923334 / 1000000000000))) = true
  norm_num [besselStateAtRationalPoint, besselIntervalStepZero,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, besselZeroTransition,
    besselInitial, besselGridStateAt, besselGridStateBlock00, besselGridStateBlock01,
    besselGridStateBlock02, besselGridStateBlock03, besselGridStateBlock04,
    besselGridStateBlock05, besselGridStateBlock06, besselGridStateBlock07,
    besselGridStateBlock08, besselGridStateBlock09, besselGridStateBlock10,
    besselGridStateBlock11, besselGridStateBlock12, besselGridStateBlock13,
    besselGridStateBlock14, besselGridState010, besselGridState013, besselGridState021, besselGridState025, besselGridState027, besselGridState034, besselGridState036, besselGridState040, besselGridState046, besselGridState047, besselGridState050, besselGridState053, besselGridState055, besselGridState057, besselGridState059, besselGridState066, besselGridState067, besselGridState070, besselGridState072, besselGridState080, besselGridState085, besselGridState086, besselGridState091, besselGridState099, besselGridState103, besselGridState105, besselStateSubset, linearInterval, widenInterval,
    rationalErrorInterval, rationalIntervalSubset, orderedInterval, Finset.sum_range_succ,
    IntervalRat.add, IntervalRat.mul, IntervalRat.scale, IntervalRat.singleton]

theorem compactCertificate270_stateChecks1 :
    compactCertificate270.stateChecks 3 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 10 12 (124233425433623 / 4000000000000)) (orderedInterval (58872147044 / 1000000000000) (58872147045 / 1000000000000), orderedInterval (129564397746 / 1000000000000) (129564397747 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 27 12 (333708455591531 / 4000000000000)) (orderedInterval (50184452938 / 1000000000000) (50184469275 / 1000000000000), orderedInterval (-71801927064 / 1000000000000) (-71801910727 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 72 12 (906083372470527 / 4000000000000)) (orderedInterval (47507991852 / 1000000000000) (47507991853 / 1000000000000), orderedInterval (23419830676 / 1000000000000) (23419830677 / 1000000000000))) = true
  norm_num [besselStateAtRationalPoint, besselIntervalStepZero,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, besselZeroTransition,
    besselInitial, besselGridStateAt, besselGridStateBlock00, besselGridStateBlock01,
    besselGridStateBlock02, besselGridStateBlock03, besselGridStateBlock04,
    besselGridStateBlock05, besselGridStateBlock06, besselGridStateBlock07,
    besselGridStateBlock08, besselGridStateBlock09, besselGridStateBlock10,
    besselGridStateBlock11, besselGridStateBlock12, besselGridStateBlock13,
    besselGridStateBlock14, besselGridState010, besselGridState013, besselGridState021, besselGridState025, besselGridState027, besselGridState034, besselGridState036, besselGridState040, besselGridState046, besselGridState047, besselGridState050, besselGridState053, besselGridState055, besselGridState057, besselGridState059, besselGridState066, besselGridState067, besselGridState070, besselGridState072, besselGridState080, besselGridState085, besselGridState086, besselGridState091, besselGridState099, besselGridState103, besselGridState105, besselStateSubset, linearInterval, widenInterval,
    rationalErrorInterval, rationalIntervalSubset, orderedInterval, Finset.sum_range_succ,
    IntervalRat.add, IntervalRat.mul, IntervalRat.scale, IntervalRat.singleton]

theorem compactCertificate270_stateChecks2 :
    compactCertificate270.stateChecks 6 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 53 12 (667416911183351 / 4000000000000)) (orderedInterval (-55981770339 / 1000000000000) (-55981770338 / 1000000000000), orderedInterval (-25936943041 / 1000000000000) (-25936943040 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 91 12 (1143630253069523 / 4000000000000)) (orderedInterval (-34098875758 / 1000000000000) (-34098875757 / 1000000000000), orderedInterval (-32558298914 / 1000000000000) (-32558298913 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 67 12 (842392868283257 / 4000000000000)) (orderedInterval (-42941773340 / 1000000000000) (-42941773339 / 1000000000000), orderedInterval (-34233361825 / 1000000000000) (-34233361824 / 1000000000000))) = true
  norm_num [besselStateAtRationalPoint, besselIntervalStepZero,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, besselZeroTransition,
    besselInitial, besselGridStateAt, besselGridStateBlock00, besselGridStateBlock01,
    besselGridStateBlock02, besselGridStateBlock03, besselGridStateBlock04,
    besselGridStateBlock05, besselGridStateBlock06, besselGridStateBlock07,
    besselGridStateBlock08, besselGridStateBlock09, besselGridStateBlock10,
    besselGridStateBlock11, besselGridStateBlock12, besselGridStateBlock13,
    besselGridStateBlock14, besselGridState010, besselGridState013, besselGridState021, besselGridState025, besselGridState027, besselGridState034, besselGridState036, besselGridState040, besselGridState046, besselGridState047, besselGridState050, besselGridState053, besselGridState055, besselGridState057, besselGridState059, besselGridState066, besselGridState067, besselGridState070, besselGridState072, besselGridState080, besselGridState085, besselGridState086, besselGridState091, besselGridState099, besselGridState103, besselGridState105, besselStateSubset, linearInterval, widenInterval,
    rationalErrorInterval, rationalIntervalSubset, orderedInterval, Finset.sum_range_succ,
    IntervalRat.add, IntervalRat.mul, IntervalRat.scale, IntervalRat.singleton]

theorem compactCertificate270_stateChecks3 :
    compactCertificate270.stateChecks 9 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 103 12 (1292447290994711 / 4000000000000)) (orderedInterval (-13658790967 / 1000000000000) (-13658790966 / 1000000000000), orderedInterval (-42212929107 / 1000000000000) (-42212929106 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 59 12 (746194791369119 / 4000000000000)) (orderedInterval (-53607018694 / 1000000000000) (-53607010010 / 1000000000000), orderedInterval (23357881610 / 1000000000000) (23357890295 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 105 12 (1324135751752171 / 4000000000000)) (orderedInterval (-40709931966 / 1000000000000) (-40709918366 / 1000000000000), orderedInterval (16365646468 / 1000000000000) (16365660068 / 1000000000000))) = true
  norm_num [besselStateAtRationalPoint, besselIntervalStepZero,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, besselZeroTransition,
    besselInitial, besselGridStateAt, besselGridStateBlock00, besselGridStateBlock01,
    besselGridStateBlock02, besselGridStateBlock03, besselGridStateBlock04,
    besselGridStateBlock05, besselGridStateBlock06, besselGridStateBlock07,
    besselGridStateBlock08, besselGridStateBlock09, besselGridStateBlock10,
    besselGridStateBlock11, besselGridStateBlock12, besselGridStateBlock13,
    besselGridStateBlock14, besselGridState010, besselGridState013, besselGridState021, besselGridState025, besselGridState027, besselGridState034, besselGridState036, besselGridState040, besselGridState046, besselGridState047, besselGridState050, besselGridState053, besselGridState055, besselGridState057, besselGridState059, besselGridState066, besselGridState067, besselGridState070, besselGridState072, besselGridState080, besselGridState085, besselGridState086, besselGridState091, besselGridState099, besselGridState103, besselGridState105, besselStateSubset, linearInterval, widenInterval,
    rationalErrorInterval, rationalIntervalSubset, orderedInterval, Finset.sum_range_succ,
    IntervalRat.add, IntervalRat.mul, IntervalRat.scale, IntervalRat.singleton]

theorem compactCertificate270_stateChecks4 :
    compactCertificate270.stateChecks 12 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 99 12 (1237179381658999 / 4000000000000)) (orderedInterval (36579497501 / 1000000000000) (36579606143 / 1000000000000), orderedInterval (-26896280105 / 1000000000000) (-26896171463 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 70 12 (882909583894567 / 4000000000000)) (orderedInterval (53680509408 / 1000000000000) (53680509530 / 1000000000000), orderedInterval (-1729586768 / 1000000000000) (-1729586646 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 80 12 (1001125366774593 / 4000000000000)) (orderedInterval (-13022766341 / 1000000000000) (-13022766233 / 1000000000000), orderedInterval (48750019881 / 1000000000000) (48750019989 / 1000000000000))) = true
  norm_num [besselStateAtRationalPoint, besselIntervalStepZero,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, besselZeroTransition,
    besselInitial, besselGridStateAt, besselGridStateBlock00, besselGridStateBlock01,
    besselGridStateBlock02, besselGridStateBlock03, besselGridStateBlock04,
    besselGridStateBlock05, besselGridStateBlock06, besselGridStateBlock07,
    besselGridStateBlock08, besselGridStateBlock09, besselGridStateBlock10,
    besselGridStateBlock11, besselGridStateBlock12, besselGridStateBlock13,
    besselGridStateBlock14, besselGridState010, besselGridState013, besselGridState021, besselGridState025, besselGridState027, besselGridState034, besselGridState036, besselGridState040, besselGridState046, besselGridState047, besselGridState050, besselGridState053, besselGridState055, besselGridState057, besselGridState059, besselGridState066, besselGridState067, besselGridState070, besselGridState072, besselGridState080, besselGridState085, besselGridState086, besselGridState091, besselGridState099, besselGridState103, besselGridState105, besselStateSubset, linearInterval, widenInterval,
    rationalErrorInterval, rationalIntervalSubset, orderedInterval, Finset.sum_range_succ,
    IntervalRat.add, IntervalRat.mul, IntervalRat.scale, IntervalRat.singleton]

theorem compactCertificate270_stateChecks5 :
    compactCertificate270.stateChecks 15 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 66 12 (834633958250417 / 4000000000000)) (orderedInterval (47730980351 / 1000000000000) (47731010585 / 1000000000000), orderedInterval (-27912964046 / 1000000000000) (-27912933811 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 59 12 (737424414022757 / 4000000000000)) (orderedInterval (12430485404 / 1000000000000) (12430485491 / 1000000000000), orderedInterval (-57468036531 / 1000000000000) (-57468036443 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 85 12 (213734337680943 / 800000000000)) (orderedInterval (-38762037029 / 1000000000000) (-38762037028 / 1000000000000), orderedInterval (-29598124952 / 1000000000000) (-29598124951 / 1000000000000))) = true
  norm_num [besselStateAtRationalPoint, besselIntervalStepZero,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, besselZeroTransition,
    besselInitial, besselGridStateAt, besselGridStateBlock00, besselGridStateBlock01,
    besselGridStateBlock02, besselGridStateBlock03, besselGridStateBlock04,
    besselGridStateBlock05, besselGridStateBlock06, besselGridStateBlock07,
    besselGridStateBlock08, besselGridStateBlock09, besselGridStateBlock10,
    besselGridStateBlock11, besselGridStateBlock12, besselGridStateBlock13,
    besselGridStateBlock14, besselGridState010, besselGridState013, besselGridState021, besselGridState025, besselGridState027, besselGridState034, besselGridState036, besselGridState040, besselGridState046, besselGridState047, besselGridState050, besselGridState053, besselGridState055, besselGridState057, besselGridState059, besselGridState066, besselGridState067, besselGridState070, besselGridState072, besselGridState080, besselGridState085, besselGridState086, besselGridState091, besselGridState099, besselGridState103, besselGridState105, besselStateSubset, linearInterval, widenInterval,
    rationalErrorInterval, rationalIntervalSubset, orderedInterval, Finset.sum_range_succ,
    IntervalRat.add, IntervalRat.mul, IntervalRat.scale, IntervalRat.singleton]

theorem compactCertificate270_stateChecks6 :
    compactCertificate270.stateChecks 18 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 47 12 (591200426247421 / 4000000000000)) (orderedInterval (-52602520725 / 1000000000000) (-52602520724 / 1000000000000), orderedInterval (-39068328262 / 1000000000000) (-39068328261 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 40 12 (501167148695381 / 4000000000000)) (orderedInterval (28575624935 / 1000000000000) (28575624936 / 1000000000000), orderedInterval (65189552691 / 1000000000000) (65189552692 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 25 12 (313607131716743 / 4000000000000)) (orderedInterval (-54229420118 / 1000000000000) (-54229420117 / 1000000000000), orderedInterval (-71620697946 / 1000000000000) (-71620697945 / 1000000000000))) = true
  norm_num [besselStateAtRationalPoint, besselIntervalStepZero,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, besselZeroTransition,
    besselInitial, besselGridStateAt, besselGridStateBlock00, besselGridStateBlock01,
    besselGridStateBlock02, besselGridStateBlock03, besselGridStateBlock04,
    besselGridStateBlock05, besselGridStateBlock06, besselGridStateBlock07,
    besselGridStateBlock08, besselGridStateBlock09, besselGridStateBlock10,
    besselGridStateBlock11, besselGridStateBlock12, besselGridStateBlock13,
    besselGridStateBlock14, besselGridState010, besselGridState013, besselGridState021, besselGridState025, besselGridState027, besselGridState034, besselGridState036, besselGridState040, besselGridState046, besselGridState047, besselGridState050, besselGridState053, besselGridState055, besselGridState057, besselGridState059, besselGridState066, besselGridState067, besselGridState070, besselGridState072, besselGridState080, besselGridState085, besselGridState086, besselGridState091, besselGridState099, besselGridState103, besselGridState105, besselStateSubset, linearInterval, widenInterval,
    rationalErrorInterval, rationalIntervalSubset, orderedInterval, Finset.sum_range_succ,
    IntervalRat.add, IntervalRat.mul, IntervalRat.scale, IntervalRat.singleton]

theorem compactCertificate270_stateChecks7 :
    compactCertificate270.stateChecks 21 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 13 12 (168658958447481 / 4000000000000)) (orderedInterval (-105660045159 / 1000000000000) (-105660030056 / 1000000000000), orderedInterval (63973094897 / 1000000000000) (63973110000 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 36 12 (457941881025443 / 4000000000000)) (orderedInterval (61475730412 / 1000000000000) (61475769038 / 1000000000000), orderedInterval (-42475332391 / 1000000000000) (-42475293765 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 50 12 (625280487884611 / 4000000000000)) (orderedInterval (1600844190 / 1000000000000) (1600844193 / 1000000000000), orderedInterval (63791407528 / 1000000000000) (63791407531 / 1000000000000))) = true
  norm_num [besselStateAtRationalPoint, besselIntervalStepZero,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, besselZeroTransition,
    besselInitial, besselGridStateAt, besselGridStateBlock00, besselGridStateBlock01,
    besselGridStateBlock02, besselGridStateBlock03, besselGridStateBlock04,
    besselGridStateBlock05, besselGridStateBlock06, besselGridStateBlock07,
    besselGridStateBlock08, besselGridStateBlock09, besselGridStateBlock10,
    besselGridStateBlock11, besselGridStateBlock12, besselGridStateBlock13,
    besselGridStateBlock14, besselGridState010, besselGridState013, besselGridState021, besselGridState025, besselGridState027, besselGridState034, besselGridState036, besselGridState040, besselGridState046, besselGridState047, besselGridState050, besselGridState053, besselGridState055, besselGridState057, besselGridState059, besselGridState066, besselGridState067, besselGridState070, besselGridState072, besselGridState080, besselGridState085, besselGridState086, besselGridState091, besselGridState099, besselGridState103, besselGridState105, besselStateSubset, linearInterval, widenInterval,
    rationalErrorInterval, rationalIntervalSubset, orderedInterval, Finset.sum_range_succ,
    IntervalRat.add, IntervalRat.mul, IntervalRat.scale, IntervalRat.singleton]

theorem compactCertificate270_stateChecks8 :
    compactCertificate270.stateChecks 24 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 21 12 (264392868283257 / 4000000000000)) (orderedInterval (-77376837147 / 1000000000000) (-77376837146 / 1000000000000), orderedInterval (-59781754593 / 1000000000000) (-59781754592 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 86 12 (1074742330918297 / 4000000000000)) (orderedInterval (-31597708929 / 1000000000000) (-31597692350 / 1000000000000), orderedInterval (37085425716 / 1000000000000) (37085442295 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 57 12 (717878069126423 / 4000000000000)) (orderedInterval (-55145829166 / 1000000000000) (-55145829165 / 1000000000000), orderedInterval (-22344328527 / 1000000000000) (-22344328526 / 1000000000000))) = true
  norm_num [besselStateAtRationalPoint, besselIntervalStepZero,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, besselZeroTransition,
    besselInitial, besselGridStateAt, besselGridStateBlock00, besselGridStateBlock01,
    besselGridStateBlock02, besselGridStateBlock03, besselGridStateBlock04,
    besselGridStateBlock05, besselGridStateBlock06, besselGridStateBlock07,
    besselGridStateBlock08, besselGridStateBlock09, besselGridStateBlock10,
    besselGridStateBlock11, besselGridStateBlock12, besselGridStateBlock13,
    besselGridStateBlock14, besselGridState010, besselGridState013, besselGridState021, besselGridState025, besselGridState027, besselGridState034, besselGridState036, besselGridState040, besselGridState046, besselGridState047, besselGridState050, besselGridState053, besselGridState055, besselGridState057, besselGridState059, besselGridState066, besselGridState067, besselGridState070, besselGridState072, besselGridState080, besselGridState085, besselGridState086, besselGridState091, besselGridState099, besselGridState103, besselGridState105, besselStateSubset, linearInterval, widenInterval,
    rationalErrorInterval, rationalIntervalSubset, orderedInterval, Finset.sum_range_succ,
    IntervalRat.add, IntervalRat.mul, IntervalRat.scale, IntervalRat.singleton]

theorem compactCertificate270_states : ∀ j,
    BesselStateValid (compactCertificate270.point j) (compactCertificate270.state j) :=
  compactCertificate270.statesValid_of_checks3 compactCertificate270_stateChecks0
    compactCertificate270_stateChecks1 compactCertificate270_stateChecks2
    compactCertificate270_stateChecks3 compactCertificate270_stateChecks4
    compactCertificate270_stateChecks5 compactCertificate270_stateChecks6
    compactCertificate270_stateChecks7 compactCertificate270_stateChecks8

theorem compactCertificate270_chunkChecks0_0 :
    compactCertificate270.chunkChecks (0 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 0) <| besselDerivativeNearFromState (289 / 2) 0 (IntervalRat.scale (289 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (46266539573 / 1000000000000) (46266539574 / 1000000000000), orderedInterval (47432779573 / 1000000000000) (47432779574 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 0) <| besselDerivativeNearFromState (425752183943389 / 4000000000000) 0 (IntervalRat.scale (289 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (30693956719 / 1000000000000) (30693956720 / 1000000000000), orderedInterval (70842125127 / 1000000000000) (70842125128 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 0) <| besselDerivativeNearFromState (137679508656637 / 800000000000) 0 (IntervalRat.scale (289 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-5857749444 / 1000000000000) (-5857749443 / 1000000000000), orderedInterval (-60520923335 / 1000000000000) (-60520923334 / 1000000000000)))) (orderedInterval (18280705344 / 1000000000000) (18280705355 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 0) <| besselDerivativeNearFromState (124233425433623 / 4000000000000) 0 (IntervalRat.scale (289 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (58872147044 / 1000000000000) (58872147045 / 1000000000000), orderedInterval (129564397746 / 1000000000000) (129564397747 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 0) <| besselDerivativeNearFromState (333708455591531 / 4000000000000) 0 (IntervalRat.scale (289 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (50184452938 / 1000000000000) (50184469275 / 1000000000000), orderedInterval (-71801927064 / 1000000000000) (-71801910727 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 0) <| besselDerivativeNearFromState (906083372470527 / 4000000000000) 0 (IntervalRat.scale (289 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (47507991852 / 1000000000000) (47507991853 / 1000000000000), orderedInterval (23419830676 / 1000000000000) (23419830677 / 1000000000000)))) (orderedInterval (-2183725151 / 1000000000000) (-2183724536 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 0) <| besselDerivativeNearFromState (667416911183351 / 4000000000000) 0 (IntervalRat.scale (289 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-55981770339 / 1000000000000) (-55981770338 / 1000000000000), orderedInterval (-25936943041 / 1000000000000) (-25936943040 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 0) <| besselDerivativeNearFromState (1143630253069523 / 4000000000000) 0 (IntervalRat.scale (289 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-34098875758 / 1000000000000) (-34098875757 / 1000000000000), orderedInterval (-32558298914 / 1000000000000) (-32558298913 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 0) <| besselDerivativeNearFromState (842392868283257 / 4000000000000) 0 (IntervalRat.scale (289 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-42941773340 / 1000000000000) (-42941773339 / 1000000000000), orderedInterval (-34233361825 / 1000000000000) (-34233361824 / 1000000000000)))) (orderedInterval (13927816 / 1000000000000) (13927825 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate270_chunkChecks0_1 :
    compactCertificate270.chunkChecks (0 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 0) <| besselDerivativeNearFromState (1292447290994711 / 4000000000000) 0 (IntervalRat.scale (289 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-13658790967 / 1000000000000) (-13658790966 / 1000000000000), orderedInterval (-42212929107 / 1000000000000) (-42212929106 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 0) <| besselDerivativeNearFromState (746194791369119 / 4000000000000) 0 (IntervalRat.scale (289 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-53607018694 / 1000000000000) (-53607010010 / 1000000000000), orderedInterval (23357881610 / 1000000000000) (23357890295 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 0) <| besselDerivativeNearFromState (1324135751752171 / 4000000000000) 0 (IntervalRat.scale (289 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-40709931966 / 1000000000000) (-40709918366 / 1000000000000), orderedInterval (16365646468 / 1000000000000) (16365660068 / 1000000000000)))) (orderedInterval (-7331993436 / 1000000000000) (-7331990801 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 0) <| besselDerivativeNearFromState (1237179381658999 / 4000000000000) 0 (IntervalRat.scale (289 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (36579497501 / 1000000000000) (36579606143 / 1000000000000), orderedInterval (-26896280105 / 1000000000000) (-26896171463 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 0) <| besselDerivativeNearFromState (882909583894567 / 4000000000000) 0 (IntervalRat.scale (289 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (53680509408 / 1000000000000) (53680509530 / 1000000000000), orderedInterval (-1729586768 / 1000000000000) (-1729586646 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 0) <| besselDerivativeNearFromState (1001125366774593 / 4000000000000) 0 (IntervalRat.scale (289 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-13022766341 / 1000000000000) (-13022766233 / 1000000000000), orderedInterval (48750019881 / 1000000000000) (48750019989 / 1000000000000)))) (orderedInterval (4481710732 / 1000000000000) (4481712723 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 0) <| besselDerivativeNearFromState (834633958250417 / 4000000000000) 0 (IntervalRat.scale (289 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (47730980351 / 1000000000000) (47731010585 / 1000000000000), orderedInterval (-27912964046 / 1000000000000) (-27912933811 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 0) <| besselDerivativeNearFromState (737424414022757 / 4000000000000) 0 (IntervalRat.scale (289 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (12430485404 / 1000000000000) (12430485491 / 1000000000000), orderedInterval (-57468036531 / 1000000000000) (-57468036443 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 0) <| besselDerivativeNearFromState (213734337680943 / 800000000000) 0 (IntervalRat.scale (289 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-38762037029 / 1000000000000) (-38762037028 / 1000000000000), orderedInterval (-29598124952 / 1000000000000) (-29598124951 / 1000000000000)))) (orderedInterval (-1152635034 / 1000000000000) (-1152634665 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate270_chunkChecks0_2 :
    compactCertificate270.chunkChecks (0 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 0) <| besselDerivativeNearFromState (591200426247421 / 4000000000000) 0 (IntervalRat.scale (289 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-52602520725 / 1000000000000) (-52602520724 / 1000000000000), orderedInterval (-39068328262 / 1000000000000) (-39068328261 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 0) <| besselDerivativeNearFromState (501167148695381 / 4000000000000) 0 (IntervalRat.scale (289 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (28575624935 / 1000000000000) (28575624936 / 1000000000000), orderedInterval (65189552691 / 1000000000000) (65189552692 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 0) <| besselDerivativeNearFromState (313607131716743 / 4000000000000) 0 (IntervalRat.scale (289 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-54229420118 / 1000000000000) (-54229420117 / 1000000000000), orderedInterval (-71620697946 / 1000000000000) (-71620697945 / 1000000000000)))) (orderedInterval (5027912893 / 1000000000000) (5027912930 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 0) <| besselDerivativeNearFromState (168658958447481 / 4000000000000) 0 (IntervalRat.scale (289 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-105660045159 / 1000000000000) (-105660030056 / 1000000000000), orderedInterval (63973094897 / 1000000000000) (63973110000 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 0) <| besselDerivativeNearFromState (457941881025443 / 4000000000000) 0 (IntervalRat.scale (289 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (61475730412 / 1000000000000) (61475769038 / 1000000000000), orderedInterval (-42475332391 / 1000000000000) (-42475293765 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 0) <| besselDerivativeNearFromState (625280487884611 / 4000000000000) 0 (IntervalRat.scale (289 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (1600844190 / 1000000000000) (1600844193 / 1000000000000), orderedInterval (63791407528 / 1000000000000) (63791407531 / 1000000000000)))) (orderedInterval (433645630 / 1000000000000) (433646803 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 0) <| besselDerivativeNearFromState (264392868283257 / 4000000000000) 0 (IntervalRat.scale (289 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-77376837147 / 1000000000000) (-77376837146 / 1000000000000), orderedInterval (-59781754593 / 1000000000000) (-59781754592 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 0) <| besselDerivativeNearFromState (1074742330918297 / 4000000000000) 0 (IntervalRat.scale (289 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-31597708929 / 1000000000000) (-31597692350 / 1000000000000), orderedInterval (37085425716 / 1000000000000) (37085442295 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 0) <| besselDerivativeNearFromState (717878069126423 / 4000000000000) 0 (IntervalRat.scale (289 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-55145829166 / 1000000000000) (-55145829165 / 1000000000000), orderedInterval (-22344328527 / 1000000000000) (-22344328526 / 1000000000000)))) (orderedInterval (12452475737 / 1000000000000) (12452477127 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate270_chunkChecks0 :
    compactCertificate270.chunkChecks (0 : Fin 5) 0 9 = true :=
  compactCertificate270.chunkChecks_nine_of_three (0 : Fin 5) compactCertificate270_chunkChecks0_0
    compactCertificate270_chunkChecks0_1 compactCertificate270_chunkChecks0_2

theorem compactCertificate270_chunkChecks1_0 :
    compactCertificate270.chunkChecks (1 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 1) <| besselDerivativeNearFromState (289 / 2) 1 (IntervalRat.scale (289 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (46266539573 / 1000000000000) (46266539574 / 1000000000000), orderedInterval (47432779573 / 1000000000000) (47432779574 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 1) <| besselDerivativeNearFromState (425752183943389 / 4000000000000) 1 (IntervalRat.scale (289 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (30693956719 / 1000000000000) (30693956720 / 1000000000000), orderedInterval (70842125127 / 1000000000000) (70842125128 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 1) <| besselDerivativeNearFromState (137679508656637 / 800000000000) 1 (IntervalRat.scale (289 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-5857749444 / 1000000000000) (-5857749443 / 1000000000000), orderedInterval (-60520923335 / 1000000000000) (-60520923334 / 1000000000000)))) (orderedInterval (15057169846 / 1000000000000) (15057169859 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 1) <| besselDerivativeNearFromState (124233425433623 / 4000000000000) 1 (IntervalRat.scale (289 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (58872147044 / 1000000000000) (58872147045 / 1000000000000), orderedInterval (129564397746 / 1000000000000) (129564397747 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 1) <| besselDerivativeNearFromState (333708455591531 / 4000000000000) 1 (IntervalRat.scale (289 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (50184452938 / 1000000000000) (50184469275 / 1000000000000), orderedInterval (-71801927064 / 1000000000000) (-71801910727 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 1) <| besselDerivativeNearFromState (906083372470527 / 4000000000000) 1 (IntervalRat.scale (289 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (47507991852 / 1000000000000) (47507991853 / 1000000000000), orderedInterval (23419830676 / 1000000000000) (23419830677 / 1000000000000)))) (orderedInterval (-4425661273 / 1000000000000) (-4425660908 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 1) <| besselDerivativeNearFromState (667416911183351 / 4000000000000) 1 (IntervalRat.scale (289 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-55981770339 / 1000000000000) (-55981770338 / 1000000000000), orderedInterval (-25936943041 / 1000000000000) (-25936943040 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 1) <| besselDerivativeNearFromState (1143630253069523 / 4000000000000) 1 (IntervalRat.scale (289 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-34098875758 / 1000000000000) (-34098875757 / 1000000000000), orderedInterval (-32558298914 / 1000000000000) (-32558298913 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 1) <| besselDerivativeNearFromState (842392868283257 / 4000000000000) 1 (IntervalRat.scale (289 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-42941773340 / 1000000000000) (-42941773339 / 1000000000000), orderedInterval (-34233361825 / 1000000000000) (-34233361824 / 1000000000000)))) (orderedInterval (781158550 / 1000000000000) (781158565 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate270_chunkChecks1_1 :
    compactCertificate270.chunkChecks (1 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 1) <| besselDerivativeNearFromState (1292447290994711 / 4000000000000) 1 (IntervalRat.scale (289 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-13658790967 / 1000000000000) (-13658790966 / 1000000000000), orderedInterval (-42212929107 / 1000000000000) (-42212929106 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 1) <| besselDerivativeNearFromState (746194791369119 / 4000000000000) 1 (IntervalRat.scale (289 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-53607018694 / 1000000000000) (-53607010010 / 1000000000000), orderedInterval (23357881610 / 1000000000000) (23357890295 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 1) <| besselDerivativeNearFromState (1324135751752171 / 4000000000000) 1 (IntervalRat.scale (289 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-40709931966 / 1000000000000) (-40709918366 / 1000000000000), orderedInterval (16365646468 / 1000000000000) (16365660068 / 1000000000000)))) (orderedInterval (24336066101 / 1000000000000) (24336071481 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 1) <| besselDerivativeNearFromState (1237179381658999 / 4000000000000) 1 (IntervalRat.scale (289 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (36579497501 / 1000000000000) (36579606143 / 1000000000000), orderedInterval (-26896280105 / 1000000000000) (-26896171463 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 1) <| besselDerivativeNearFromState (882909583894567 / 4000000000000) 1 (IntervalRat.scale (289 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (53680509408 / 1000000000000) (53680509530 / 1000000000000), orderedInterval (-1729586768 / 1000000000000) (-1729586646 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 1) <| besselDerivativeNearFromState (1001125366774593 / 4000000000000) 1 (IntervalRat.scale (289 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-13022766341 / 1000000000000) (-13022766233 / 1000000000000), orderedInterval (48750019881 / 1000000000000) (48750019989 / 1000000000000)))) (orderedInterval (362177575 / 1000000000000) (362181820 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 1) <| besselDerivativeNearFromState (834633958250417 / 4000000000000) 1 (IntervalRat.scale (289 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (47730980351 / 1000000000000) (47731010585 / 1000000000000), orderedInterval (-27912964046 / 1000000000000) (-27912933811 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 1) <| besselDerivativeNearFromState (737424414022757 / 4000000000000) 1 (IntervalRat.scale (289 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (12430485404 / 1000000000000) (12430485491 / 1000000000000), orderedInterval (-57468036531 / 1000000000000) (-57468036443 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 1) <| besselDerivativeNearFromState (213734337680943 / 800000000000) 1 (IntervalRat.scale (289 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-38762037029 / 1000000000000) (-38762037028 / 1000000000000), orderedInterval (-29598124952 / 1000000000000) (-29598124951 / 1000000000000)))) (orderedInterval (2329193011 / 1000000000000) (2329193543 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate270_chunkChecks1_2 :
    compactCertificate270.chunkChecks (1 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 1) <| besselDerivativeNearFromState (591200426247421 / 4000000000000) 1 (IntervalRat.scale (289 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-52602520725 / 1000000000000) (-52602520724 / 1000000000000), orderedInterval (-39068328262 / 1000000000000) (-39068328261 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 1) <| besselDerivativeNearFromState (501167148695381 / 4000000000000) 1 (IntervalRat.scale (289 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (28575624935 / 1000000000000) (28575624936 / 1000000000000), orderedInterval (65189552691 / 1000000000000) (65189552692 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 1) <| besselDerivativeNearFromState (313607131716743 / 4000000000000) 1 (IntervalRat.scale (289 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-54229420118 / 1000000000000) (-54229420117 / 1000000000000), orderedInterval (-71620697946 / 1000000000000) (-71620697945 / 1000000000000)))) (orderedInterval (1925059037 / 1000000000000) (1925059071 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 1) <| besselDerivativeNearFromState (168658958447481 / 4000000000000) 1 (IntervalRat.scale (289 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-105660045159 / 1000000000000) (-105660030056 / 1000000000000), orderedInterval (63973094897 / 1000000000000) (63973110000 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 1) <| besselDerivativeNearFromState (457941881025443 / 4000000000000) 1 (IntervalRat.scale (289 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (61475730412 / 1000000000000) (61475769038 / 1000000000000), orderedInterval (-42475332391 / 1000000000000) (-42475293765 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 1) <| besselDerivativeNearFromState (625280487884611 / 4000000000000) 1 (IntervalRat.scale (289 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (1600844190 / 1000000000000) (1600844193 / 1000000000000), orderedInterval (63791407528 / 1000000000000) (63791407531 / 1000000000000)))) (orderedInterval (-4870033787 / 1000000000000) (-4870032995 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 1) <| besselDerivativeNearFromState (264392868283257 / 4000000000000) 1 (IntervalRat.scale (289 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-77376837147 / 1000000000000) (-77376837146 / 1000000000000), orderedInterval (-59781754593 / 1000000000000) (-59781754592 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 1) <| besselDerivativeNearFromState (1074742330918297 / 4000000000000) 1 (IntervalRat.scale (289 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-31597708929 / 1000000000000) (-31597692350 / 1000000000000), orderedInterval (37085425716 / 1000000000000) (37085442295 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 1) <| besselDerivativeNearFromState (717878069126423 / 4000000000000) 1 (IntervalRat.scale (289 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-55145829166 / 1000000000000) (-55145829165 / 1000000000000), orderedInterval (-22344328527 / 1000000000000) (-22344328526 / 1000000000000)))) (orderedInterval (-571130881 / 1000000000000) (-571128315 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate270_chunkChecks1 :
    compactCertificate270.chunkChecks (1 : Fin 5) 0 9 = true :=
  compactCertificate270.chunkChecks_nine_of_three (1 : Fin 5) compactCertificate270_chunkChecks1_0
    compactCertificate270_chunkChecks1_1 compactCertificate270_chunkChecks1_2

theorem compactCertificate270_chunkChecks2_0 :
    compactCertificate270.chunkChecks (2 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 2) <| besselDerivativeNearFromState (289 / 2) 2 (IntervalRat.scale (289 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (46266539573 / 1000000000000) (46266539574 / 1000000000000), orderedInterval (47432779573 / 1000000000000) (47432779574 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 2) <| besselDerivativeNearFromState (425752183943389 / 4000000000000) 2 (IntervalRat.scale (289 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (30693956719 / 1000000000000) (30693956720 / 1000000000000), orderedInterval (70842125127 / 1000000000000) (70842125128 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 2) <| besselDerivativeNearFromState (137679508656637 / 800000000000) 2 (IntervalRat.scale (289 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-5857749444 / 1000000000000) (-5857749443 / 1000000000000), orderedInterval (-60520923335 / 1000000000000) (-60520923334 / 1000000000000)))) (orderedInterval (-18110231585 / 1000000000000) (-18110231571 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 2) <| besselDerivativeNearFromState (124233425433623 / 4000000000000) 2 (IntervalRat.scale (289 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (58872147044 / 1000000000000) (58872147045 / 1000000000000), orderedInterval (129564397746 / 1000000000000) (129564397747 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 2) <| besselDerivativeNearFromState (333708455591531 / 4000000000000) 2 (IntervalRat.scale (289 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (50184452938 / 1000000000000) (50184469275 / 1000000000000), orderedInterval (-71801927064 / 1000000000000) (-71801910727 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 2) <| besselDerivativeNearFromState (906083372470527 / 4000000000000) 2 (IntervalRat.scale (289 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (47507991852 / 1000000000000) (47507991853 / 1000000000000), orderedInterval (23419830676 / 1000000000000) (23419830677 / 1000000000000)))) (orderedInterval (7748893377 / 1000000000000) (7748893606 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 2) <| besselDerivativeNearFromState (667416911183351 / 4000000000000) 2 (IntervalRat.scale (289 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-55981770339 / 1000000000000) (-55981770338 / 1000000000000), orderedInterval (-25936943041 / 1000000000000) (-25936943040 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 2) <| besselDerivativeNearFromState (1143630253069523 / 4000000000000) 2 (IntervalRat.scale (289 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-34098875758 / 1000000000000) (-34098875757 / 1000000000000), orderedInterval (-32558298914 / 1000000000000) (-32558298913 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 2) <| besselDerivativeNearFromState (842392868283257 / 4000000000000) 2 (IntervalRat.scale (289 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-42941773340 / 1000000000000) (-42941773339 / 1000000000000), orderedInterval (-34233361825 / 1000000000000) (-34233361824 / 1000000000000)))) (orderedInterval (-1918414649 / 1000000000000) (-1918414623 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate270_chunkChecks2_1 :
    compactCertificate270.chunkChecks (2 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 2) <| besselDerivativeNearFromState (1292447290994711 / 4000000000000) 2 (IntervalRat.scale (289 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-13658790967 / 1000000000000) (-13658790966 / 1000000000000), orderedInterval (-42212929107 / 1000000000000) (-42212929106 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 2) <| besselDerivativeNearFromState (746194791369119 / 4000000000000) 2 (IntervalRat.scale (289 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-53607018694 / 1000000000000) (-53607010010 / 1000000000000), orderedInterval (23357881610 / 1000000000000) (23357890295 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 2) <| besselDerivativeNearFromState (1324135751752171 / 4000000000000) 2 (IntervalRat.scale (289 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-40709931966 / 1000000000000) (-40709918366 / 1000000000000), orderedInterval (16365646468 / 1000000000000) (16365660068 / 1000000000000)))) (orderedInterval (24688377024 / 1000000000000) (24688388535 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 2) <| besselDerivativeNearFromState (1237179381658999 / 4000000000000) 2 (IntervalRat.scale (289 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (36579497501 / 1000000000000) (36579606143 / 1000000000000), orderedInterval (-26896280105 / 1000000000000) (-26896171463 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 2) <| besselDerivativeNearFromState (882909583894567 / 4000000000000) 2 (IntervalRat.scale (289 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (53680509408 / 1000000000000) (53680509530 / 1000000000000), orderedInterval (-1729586768 / 1000000000000) (-1729586646 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 2) <| besselDerivativeNearFromState (1001125366774593 / 4000000000000) 2 (IntervalRat.scale (289 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-13022766341 / 1000000000000) (-13022766233 / 1000000000000), orderedInterval (48750019881 / 1000000000000) (48750019989 / 1000000000000)))) (orderedInterval (-9019129332 / 1000000000000) (-9019120242 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 2) <| besselDerivativeNearFromState (834633958250417 / 4000000000000) 2 (IntervalRat.scale (289 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (47730980351 / 1000000000000) (47731010585 / 1000000000000), orderedInterval (-27912964046 / 1000000000000) (-27912933811 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 2) <| besselDerivativeNearFromState (737424414022757 / 4000000000000) 2 (IntervalRat.scale (289 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (12430485404 / 1000000000000) (12430485491 / 1000000000000), orderedInterval (-57468036531 / 1000000000000) (-57468036443 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 2) <| besselDerivativeNearFromState (213734337680943 / 800000000000) 2 (IntervalRat.scale (289 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-38762037029 / 1000000000000) (-38762037028 / 1000000000000), orderedInterval (-29598124952 / 1000000000000) (-29598124951 / 1000000000000)))) (orderedInterval (3385180772 / 1000000000000) (3385181543 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate270_chunkChecks2_2 :
    compactCertificate270.chunkChecks (2 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 2) <| besselDerivativeNearFromState (591200426247421 / 4000000000000) 2 (IntervalRat.scale (289 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-52602520725 / 1000000000000) (-52602520724 / 1000000000000), orderedInterval (-39068328262 / 1000000000000) (-39068328261 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 2) <| besselDerivativeNearFromState (501167148695381 / 4000000000000) 2 (IntervalRat.scale (289 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (28575624935 / 1000000000000) (28575624936 / 1000000000000), orderedInterval (65189552691 / 1000000000000) (65189552692 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 2) <| besselDerivativeNearFromState (313607131716743 / 4000000000000) 2 (IntervalRat.scale (289 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-54229420118 / 1000000000000) (-54229420117 / 1000000000000), orderedInterval (-71620697946 / 1000000000000) (-71620697945 / 1000000000000)))) (orderedInterval (-7076936229 / 1000000000000) (-7076936196 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 2) <| besselDerivativeNearFromState (168658958447481 / 4000000000000) 2 (IntervalRat.scale (289 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-105660045159 / 1000000000000) (-105660030056 / 1000000000000), orderedInterval (63973094897 / 1000000000000) (63973110000 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 2) <| besselDerivativeNearFromState (457941881025443 / 4000000000000) 2 (IntervalRat.scale (289 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (61475730412 / 1000000000000) (61475769038 / 1000000000000), orderedInterval (-42475332391 / 1000000000000) (-42475293765 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 2) <| besselDerivativeNearFromState (625280487884611 / 4000000000000) 2 (IntervalRat.scale (289 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (1600844190 / 1000000000000) (1600844193 / 1000000000000), orderedInterval (63791407528 / 1000000000000) (63791407531 / 1000000000000)))) (orderedInterval (886634360 / 1000000000000) (886634956 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 2) <| besselDerivativeNearFromState (264392868283257 / 4000000000000) 2 (IntervalRat.scale (289 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-77376837147 / 1000000000000) (-77376837146 / 1000000000000), orderedInterval (-59781754593 / 1000000000000) (-59781754592 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 2) <| besselDerivativeNearFromState (1074742330918297 / 4000000000000) 2 (IntervalRat.scale (289 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-31597708929 / 1000000000000) (-31597692350 / 1000000000000), orderedInterval (37085425716 / 1000000000000) (37085442295 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 2) <| besselDerivativeNearFromState (717878069126423 / 4000000000000) 2 (IntervalRat.scale (289 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-55145829166 / 1000000000000) (-55145829165 / 1000000000000), orderedInterval (-22344328527 / 1000000000000) (-22344328526 / 1000000000000)))) (orderedInterval (-24752053512 / 1000000000000) (-24752048745 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate270_chunkChecks2 :
    compactCertificate270.chunkChecks (2 : Fin 5) 0 9 = true :=
  compactCertificate270.chunkChecks_nine_of_three (2 : Fin 5) compactCertificate270_chunkChecks2_0
    compactCertificate270_chunkChecks2_1 compactCertificate270_chunkChecks2_2

theorem compactCertificate270_chunkChecks3_0 :
    compactCertificate270.chunkChecks (3 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 3) <| besselDerivativeNearFromState (289 / 2) 3 (IntervalRat.scale (289 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (46266539573 / 1000000000000) (46266539574 / 1000000000000), orderedInterval (47432779573 / 1000000000000) (47432779574 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 3) <| besselDerivativeNearFromState (425752183943389 / 4000000000000) 3 (IntervalRat.scale (289 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (30693956719 / 1000000000000) (30693956720 / 1000000000000), orderedInterval (70842125127 / 1000000000000) (70842125128 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 3) <| besselDerivativeNearFromState (137679508656637 / 800000000000) 3 (IntervalRat.scale (289 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-5857749444 / 1000000000000) (-5857749443 / 1000000000000), orderedInterval (-60520923335 / 1000000000000) (-60520923334 / 1000000000000)))) (orderedInterval (-12938635833 / 1000000000000) (-12938635816 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 3) <| besselDerivativeNearFromState (124233425433623 / 4000000000000) 3 (IntervalRat.scale (289 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (58872147044 / 1000000000000) (58872147045 / 1000000000000), orderedInterval (129564397746 / 1000000000000) (129564397747 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 3) <| besselDerivativeNearFromState (333708455591531 / 4000000000000) 3 (IntervalRat.scale (289 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (50184452938 / 1000000000000) (50184469275 / 1000000000000), orderedInterval (-71801927064 / 1000000000000) (-71801910727 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 3) <| besselDerivativeNearFromState (906083372470527 / 4000000000000) 3 (IntervalRat.scale (289 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (47507991852 / 1000000000000) (47507991853 / 1000000000000), orderedInterval (23419830676 / 1000000000000) (23419830677 / 1000000000000)))) (orderedInterval (6878385404 / 1000000000000) (6878385562 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 3) <| besselDerivativeNearFromState (667416911183351 / 4000000000000) 3 (IntervalRat.scale (289 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-55981770339 / 1000000000000) (-55981770338 / 1000000000000), orderedInterval (-25936943041 / 1000000000000) (-25936943040 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 3) <| besselDerivativeNearFromState (1143630253069523 / 4000000000000) 3 (IntervalRat.scale (289 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-34098875758 / 1000000000000) (-34098875757 / 1000000000000), orderedInterval (-32558298914 / 1000000000000) (-32558298913 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 3) <| besselDerivativeNearFromState (842392868283257 / 4000000000000) 3 (IntervalRat.scale (289 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-42941773340 / 1000000000000) (-42941773339 / 1000000000000), orderedInterval (-34233361825 / 1000000000000) (-34233361824 / 1000000000000)))) (orderedInterval (-5204118689 / 1000000000000) (-5204118643 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate270_chunkChecks3_1 :
    compactCertificate270.chunkChecks (3 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 3) <| besselDerivativeNearFromState (1292447290994711 / 4000000000000) 3 (IntervalRat.scale (289 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-13658790967 / 1000000000000) (-13658790966 / 1000000000000), orderedInterval (-42212929107 / 1000000000000) (-42212929106 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 3) <| besselDerivativeNearFromState (746194791369119 / 4000000000000) 3 (IntervalRat.scale (289 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-53607018694 / 1000000000000) (-53607010010 / 1000000000000), orderedInterval (23357881610 / 1000000000000) (23357890295 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 3) <| besselDerivativeNearFromState (1324135751752171 / 4000000000000) 3 (IntervalRat.scale (289 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-40709931966 / 1000000000000) (-40709918366 / 1000000000000), orderedInterval (16365646468 / 1000000000000) (16365660068 / 1000000000000)))) (orderedInterval (-115725377062 / 1000000000000) (-115725351796 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 3) <| besselDerivativeNearFromState (1237179381658999 / 4000000000000) 3 (IntervalRat.scale (289 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (36579497501 / 1000000000000) (36579606143 / 1000000000000), orderedInterval (-26896280105 / 1000000000000) (-26896171463 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 3) <| besselDerivativeNearFromState (882909583894567 / 4000000000000) 3 (IntervalRat.scale (289 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (53680509408 / 1000000000000) (53680509530 / 1000000000000), orderedInterval (-1729586768 / 1000000000000) (-1729586646 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 3) <| besselDerivativeNearFromState (1001125366774593 / 4000000000000) 3 (IntervalRat.scale (289 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-13022766341 / 1000000000000) (-13022766233 / 1000000000000), orderedInterval (48750019881 / 1000000000000) (48750019989 / 1000000000000)))) (orderedInterval (-2834371311 / 1000000000000) (-2834351892 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 3) <| besselDerivativeNearFromState (834633958250417 / 4000000000000) 3 (IntervalRat.scale (289 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (47730980351 / 1000000000000) (47731010585 / 1000000000000), orderedInterval (-27912964046 / 1000000000000) (-27912933811 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 3) <| besselDerivativeNearFromState (737424414022757 / 4000000000000) 3 (IntervalRat.scale (289 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (12430485404 / 1000000000000) (12430485491 / 1000000000000), orderedInterval (-57468036531 / 1000000000000) (-57468036443 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 3) <| besselDerivativeNearFromState (213734337680943 / 800000000000) 3 (IntervalRat.scale (289 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-38762037029 / 1000000000000) (-38762037028 / 1000000000000), orderedInterval (-29598124952 / 1000000000000) (-29598124951 / 1000000000000)))) (orderedInterval (-1092538791 / 1000000000000) (-1092537677 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate270_chunkChecks3_2 :
    compactCertificate270.chunkChecks (3 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 3) <| besselDerivativeNearFromState (591200426247421 / 4000000000000) 3 (IntervalRat.scale (289 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-52602520725 / 1000000000000) (-52602520724 / 1000000000000), orderedInterval (-39068328262 / 1000000000000) (-39068328261 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 3) <| besselDerivativeNearFromState (501167148695381 / 4000000000000) 3 (IntervalRat.scale (289 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (28575624935 / 1000000000000) (28575624936 / 1000000000000), orderedInterval (65189552691 / 1000000000000) (65189552692 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 3) <| besselDerivativeNearFromState (313607131716743 / 4000000000000) 3 (IntervalRat.scale (289 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-54229420118 / 1000000000000) (-54229420117 / 1000000000000), orderedInterval (-71620697946 / 1000000000000) (-71620697945 / 1000000000000)))) (orderedInterval (-3857841611 / 1000000000000) (-3857841579 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 3) <| besselDerivativeNearFromState (168658958447481 / 4000000000000) 3 (IntervalRat.scale (289 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-105660045159 / 1000000000000) (-105660030056 / 1000000000000), orderedInterval (63973094897 / 1000000000000) (63973110000 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 3) <| besselDerivativeNearFromState (457941881025443 / 4000000000000) 3 (IntervalRat.scale (289 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (61475730412 / 1000000000000) (61475769038 / 1000000000000), orderedInterval (-42475332391 / 1000000000000) (-42475293765 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 3) <| besselDerivativeNearFromState (625280487884611 / 4000000000000) 3 (IntervalRat.scale (289 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (1600844190 / 1000000000000) (1600844193 / 1000000000000), orderedInterval (63791407528 / 1000000000000) (63791407531 / 1000000000000)))) (orderedInterval (5733188350 / 1000000000000) (5733188814 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 3) <| besselDerivativeNearFromState (264392868283257 / 4000000000000) 3 (IntervalRat.scale (289 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-77376837147 / 1000000000000) (-77376837146 / 1000000000000), orderedInterval (-59781754593 / 1000000000000) (-59781754592 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 3) <| besselDerivativeNearFromState (1074742330918297 / 4000000000000) 3 (IntervalRat.scale (289 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-31597708929 / 1000000000000) (-31597692350 / 1000000000000), orderedInterval (37085425716 / 1000000000000) (37085442295 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 3) <| besselDerivativeNearFromState (717878069126423 / 4000000000000) 3 (IntervalRat.scale (289 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-55145829166 / 1000000000000) (-55145829165 / 1000000000000), orderedInterval (-22344328527 / 1000000000000) (-22344328526 / 1000000000000)))) (orderedInterval (11581012657 / 1000000000000) (11581021495 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate270_chunkChecks3 :
    compactCertificate270.chunkChecks (3 : Fin 5) 0 9 = true :=
  compactCertificate270.chunkChecks_nine_of_three (3 : Fin 5) compactCertificate270_chunkChecks3_0
    compactCertificate270_chunkChecks3_1 compactCertificate270_chunkChecks3_2

theorem compactCertificate270_chunkChecks4_0 :
    compactCertificate270.chunkChecks (4 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 4) <| besselDerivativeNearFromState (289 / 2) 4 (IntervalRat.scale (289 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (46266539573 / 1000000000000) (46266539574 / 1000000000000), orderedInterval (47432779573 / 1000000000000) (47432779574 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 4) <| besselDerivativeNearFromState (425752183943389 / 4000000000000) 4 (IntervalRat.scale (289 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (30693956719 / 1000000000000) (30693956720 / 1000000000000), orderedInterval (70842125127 / 1000000000000) (70842125128 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 4) <| besselDerivativeNearFromState (137679508656637 / 800000000000) 4 (IntervalRat.scale (289 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-5857749444 / 1000000000000) (-5857749443 / 1000000000000), orderedInterval (-60520923335 / 1000000000000) (-60520923334 / 1000000000000)))) (orderedInterval (17909210126 / 1000000000000) (17909210145 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 4) <| besselDerivativeNearFromState (124233425433623 / 4000000000000) 4 (IntervalRat.scale (289 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (58872147044 / 1000000000000) (58872147045 / 1000000000000), orderedInterval (129564397746 / 1000000000000) (129564397747 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 4) <| besselDerivativeNearFromState (333708455591531 / 4000000000000) 4 (IntervalRat.scale (289 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (50184452938 / 1000000000000) (50184469275 / 1000000000000), orderedInterval (-71801927064 / 1000000000000) (-71801910727 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 4) <| besselDerivativeNearFromState (906083372470527 / 4000000000000) 4 (IntervalRat.scale (289 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (47507991852 / 1000000000000) (47507991853 / 1000000000000), orderedInterval (23419830676 / 1000000000000) (23419830677 / 1000000000000)))) (orderedInterval (-20288098445 / 1000000000000) (-20288098314 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 4) <| besselDerivativeNearFromState (667416911183351 / 4000000000000) 4 (IntervalRat.scale (289 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-55981770339 / 1000000000000) (-55981770338 / 1000000000000), orderedInterval (-25936943041 / 1000000000000) (-25936943040 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 4) <| besselDerivativeNearFromState (1143630253069523 / 4000000000000) 4 (IntervalRat.scale (289 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-34098875758 / 1000000000000) (-34098875757 / 1000000000000), orderedInterval (-32558298914 / 1000000000000) (-32558298913 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 4) <| besselDerivativeNearFromState (842392868283257 / 4000000000000) 4 (IntervalRat.scale (289 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-42941773340 / 1000000000000) (-42941773339 / 1000000000000), orderedInterval (-34233361825 / 1000000000000) (-34233361824 / 1000000000000)))) (orderedInterval (11508680119 / 1000000000000) (11508680205 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate270_chunkChecks4_1 :
    compactCertificate270.chunkChecks (4 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 4) <| besselDerivativeNearFromState (1292447290994711 / 4000000000000) 4 (IntervalRat.scale (289 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-13658790967 / 1000000000000) (-13658790966 / 1000000000000), orderedInterval (-42212929107 / 1000000000000) (-42212929106 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 4) <| besselDerivativeNearFromState (746194791369119 / 4000000000000) 4 (IntervalRat.scale (289 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-53607018694 / 1000000000000) (-53607010010 / 1000000000000), orderedInterval (23357881610 / 1000000000000) (23357890295 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 4) <| besselDerivativeNearFromState (1324135751752171 / 4000000000000) 4 (IntervalRat.scale (289 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-40709931966 / 1000000000000) (-40709918366 / 1000000000000), orderedInterval (16365646468 / 1000000000000) (16365660068 / 1000000000000)))) (orderedInterval (-108153312821 / 1000000000000) (-108153256201 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 4) <| besselDerivativeNearFromState (1237179381658999 / 4000000000000) 4 (IntervalRat.scale (289 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (36579497501 / 1000000000000) (36579606143 / 1000000000000), orderedInterval (-26896280105 / 1000000000000) (-26896171463 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 4) <| besselDerivativeNearFromState (882909583894567 / 4000000000000) 4 (IntervalRat.scale (289 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (53680509408 / 1000000000000) (53680509530 / 1000000000000), orderedInterval (-1729586768 / 1000000000000) (-1729586646 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 4) <| besselDerivativeNearFromState (1001125366774593 / 4000000000000) 4 (IntervalRat.scale (289 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-13022766341 / 1000000000000) (-13022766233 / 1000000000000), orderedInterval (48750019881 / 1000000000000) (48750019989 / 1000000000000)))) (orderedInterval (14407430443 / 1000000000000) (14407472082 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 4) <| besselDerivativeNearFromState (834633958250417 / 4000000000000) 4 (IntervalRat.scale (289 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (47730980351 / 1000000000000) (47731010585 / 1000000000000), orderedInterval (-27912964046 / 1000000000000) (-27912933811 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 4) <| besselDerivativeNearFromState (737424414022757 / 4000000000000) 4 (IntervalRat.scale (289 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (12430485404 / 1000000000000) (12430485491 / 1000000000000), orderedInterval (-57468036531 / 1000000000000) (-57468036443 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 4) <| besselDerivativeNearFromState (213734337680943 / 800000000000) 4 (IntervalRat.scale (289 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-38762037029 / 1000000000000) (-38762037028 / 1000000000000), orderedInterval (-29598124952 / 1000000000000) (-29598124951 / 1000000000000)))) (orderedInterval (-11070886614 / 1000000000000) (-11070884995 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate270_chunkChecks4_2 :
    compactCertificate270.chunkChecks (4 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 4) <| besselDerivativeNearFromState (591200426247421 / 4000000000000) 4 (IntervalRat.scale (289 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-52602520725 / 1000000000000) (-52602520724 / 1000000000000), orderedInterval (-39068328262 / 1000000000000) (-39068328261 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 4) <| besselDerivativeNearFromState (501167148695381 / 4000000000000) 4 (IntervalRat.scale (289 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (28575624935 / 1000000000000) (28575624936 / 1000000000000), orderedInterval (65189552691 / 1000000000000) (65189552692 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 4) <| besselDerivativeNearFromState (313607131716743 / 4000000000000) 4 (IntervalRat.scale (289 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-54229420118 / 1000000000000) (-54229420117 / 1000000000000), orderedInterval (-71620697946 / 1000000000000) (-71620697945 / 1000000000000)))) (orderedInterval (8191690731 / 1000000000000) (8191690762 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 4) <| besselDerivativeNearFromState (168658958447481 / 4000000000000) 4 (IntervalRat.scale (289 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-105660045159 / 1000000000000) (-105660030056 / 1000000000000), orderedInterval (63973094897 / 1000000000000) (63973110000 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 4) <| besselDerivativeNearFromState (457941881025443 / 4000000000000) 4 (IntervalRat.scale (289 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (61475730412 / 1000000000000) (61475769038 / 1000000000000), orderedInterval (-42475332391 / 1000000000000) (-42475293765 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 4) <| besselDerivativeNearFromState (625280487884611 / 4000000000000) 4 (IntervalRat.scale (289 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (1600844190 / 1000000000000) (1600844193 / 1000000000000), orderedInterval (63791407528 / 1000000000000) (63791407531 / 1000000000000)))) (orderedInterval (-782744908 / 1000000000000) (-782744536 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 4) <| besselDerivativeNearFromState (264392868283257 / 4000000000000) 4 (IntervalRat.scale (289 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-77376837147 / 1000000000000) (-77376837146 / 1000000000000), orderedInterval (-59781754593 / 1000000000000) (-59781754592 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 4) <| besselDerivativeNearFromState (1074742330918297 / 4000000000000) 4 (IntervalRat.scale (289 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-31597708929 / 1000000000000) (-31597692350 / 1000000000000), orderedInterval (37085425716 / 1000000000000) (37085442295 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 4) <| besselDerivativeNearFromState (717878069126423 / 4000000000000) 4 (IntervalRat.scale (289 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-55145829166 / 1000000000000) (-55145829165 / 1000000000000), orderedInterval (-22344328527 / 1000000000000) (-22344328526 / 1000000000000)))) (orderedInterval (55185157010 / 1000000000000) (55185173469 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate270_chunkChecks4 :
    compactCertificate270.chunkChecks (4 : Fin 5) 0 9 = true :=
  compactCertificate270.chunkChecks_nine_of_three (4 : Fin 5) compactCertificate270_chunkChecks4_0
    compactCertificate270_chunkChecks4_1 compactCertificate270_chunkChecks4_2

theorem compactCertificate270_chunks :
    ∀ r : Fin 5, ∀ b, compactCertificate270.chunkCheck r b = true :=
  compactCertificate270.chunkChecks_all (by
    intro r
    fin_cases r
    · exact compactCertificate270_chunkChecks0
    · exact compactCertificate270_chunkChecks1
    · exact compactCertificate270_chunkChecks2
    · exact compactCertificate270_chunkChecks3
    · exact compactCertificate270_chunkChecks4)

theorem compactCertificate270_coefficient0 :
    compactCertificate270.coefficientCheck (0 : Fin 5) = true := by
  norm_num [CompactCertificate.coefficientCheck, intervalFinSumHull,
    compactCertificate270, rationalIntervalSubset, orderedInterval, Fin.sum_univ_succ]

theorem compactCertificate270_coefficient1 :
    compactCertificate270.coefficientCheck (1 : Fin 5) = true := by
  norm_num [CompactCertificate.coefficientCheck, intervalFinSumHull,
    compactCertificate270, rationalIntervalSubset, orderedInterval, Fin.sum_univ_succ]

theorem compactCertificate270_coefficient2 :
    compactCertificate270.coefficientCheck (2 : Fin 5) = true := by
  norm_num [CompactCertificate.coefficientCheck, intervalFinSumHull,
    compactCertificate270, rationalIntervalSubset, orderedInterval, Fin.sum_univ_succ]

theorem compactCertificate270_coefficient3 :
    compactCertificate270.coefficientCheck (3 : Fin 5) = true := by
  norm_num [CompactCertificate.coefficientCheck, intervalFinSumHull,
    compactCertificate270, rationalIntervalSubset, orderedInterval, Fin.sum_univ_succ]

theorem compactCertificate270_coefficient4 :
    compactCertificate270.coefficientCheck (4 : Fin 5) = true := by
  norm_num [CompactCertificate.coefficientCheck, intervalFinSumHull,
    compactCertificate270, rationalIntervalSubset, orderedInterval, Fin.sum_univ_succ]

theorem compactCertificate270_coefficients : ∀ r : Fin 5,
    compactCertificate270.coefficientCheck r = true := by
  intro r
  fin_cases r
  · exact compactCertificate270_coefficient0
  · exact compactCertificate270_coefficient1
  · exact compactCertificate270_coefficient2
  · exact compactCertificate270_coefficient3
  · exact compactCertificate270_coefficient4

theorem compactCertificate270_lower : (1 : ℚ) ≤ compactCertificate270.output.lo := by
  norm_num [CompactCertificate.output, CompactCertificate.interval,
    CompactCertificate.coefficientTargetNat, compactCertificate270, dualConstant,
    intervalTaylorSum, intervalPow, intervalSub, intervalMaxAbs, widenInterval,
    rationalErrorInterval, orderedInterval, IntervalRat.add, IntervalRat.mul, IntervalRat.scale,
    IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4]

theorem compactCertificate270_proves {t : ℝ} (ht : t ∈ compactCertificate270.interval) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t :=
  compactCertificate270.proves compactCertificate270_states compactCertificate270_chunks
    compactCertificate270_coefficients compactCertificate270_lower ht

end Erdos232
