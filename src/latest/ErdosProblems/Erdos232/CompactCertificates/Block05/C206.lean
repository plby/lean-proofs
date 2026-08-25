/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, OpenAI Codex
-/
import ErdosProblems.Erdos232.CompactBase

open LeanCert.Core
namespace Erdos232

def compactCertificate206 : CompactCertificate where
  left := 2959 / 32
  right := 185 / 2
  center := 5919 / 64
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
    | 11 => 67
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
    | 0 => 5919 / 64
    | 1 => 8719817220626019 / 128000000000000
    | 2 => 2819809729199427 / 25600000000000
    | 3 => 2544420917445033 / 128000000000000
    | 4 => 6834672486665301 / 128000000000000
    | 5 => 18557465334439617 / 128000000000000
    | 6 => 13669344973336521 / 128000000000000
    | 7 => 23422655598333933 / 128000000000000
    | 8 => 17253022101621447 / 128000000000000
    | 9 => 26470572717639081 / 128000000000000
    | 10 => 15282792284130849 / 128000000000000
    | 11 => 27119583095574741 / 128000000000000
    | 12 => 25338632387680329 / 128000000000000
    | 13 => 18082843692290457 / 128000000000000
    | 14 => 20504017459995903 / 128000000000000
    | 15 => 17094112106865807 / 128000000000000
    | 16 => 15103166458825947 / 128000000000000
    | 17 => 4377486313956753 / 25600000000000
    | 18 => 12108357518887491 / 128000000000000
    | 19 => 10264388765148651 / 128000000000000
    | 20 => 6422977898378553 / 128000000000000
    | 21 => 3454298875607751 / 128000000000000
    | 22 => 9379093404116253 / 128000000000000
    | 23 => 12806350199961981 / 128000000000000
    | 24 => 5415022101621447 / 128000000000000
    | 25 => 22011764210053287 / 128000000000000
    | _ => 14702838377713833 / 128000000000000
  state := fun i =>
    match i.val with
    | 0 => (orderedInterval (-68873778697 / 1000000000000) (-68873746790 / 1000000000000), orderedInterval (46631436378 / 1000000000000) (46631468285 / 1000000000000))
    | 1 => (orderedInterval (-19953213777 / 1000000000000) (-19953213596 / 1000000000000), orderedInterval (94735936522 / 1000000000000) (94735936703 / 1000000000000))
    | 2 => (orderedInterval (-63024374948 / 1000000000000) (-63024374947 / 1000000000000), orderedInterval (-42229082286 / 1000000000000) (-42229082285 / 1000000000000))
    | 3 => (orderedInterval (173925633310 / 1000000000000) (173925633834 / 1000000000000), orderedInterval (-46405139523 / 1000000000000) (-46405138999 / 1000000000000))
    | 4 => (orderedInterval (-76155692756 / 1000000000000) (-76155692755 / 1000000000000), orderedInterval (-77536305525 / 1000000000000) (-77536305524 / 1000000000000))
    | 5 => (orderedInterval (62915184328 / 1000000000000) (62915184329 / 1000000000000), orderedInterval (20585415181 / 1000000000000) (20585415182 / 1000000000000))
    | 6 => (orderedInterval (53293654186 / 1000000000000) (53293654187 / 1000000000000), orderedInterval (55617369303 / 1000000000000) (55617369304 / 1000000000000))
    | 7 => (orderedInterval (58980539757 / 1000000000000) (58980539810 / 1000000000000), orderedInterval (367224289 / 1000000000000) (367224342 / 1000000000000))
    | 8 => (orderedInterval (-32053379521 / 1000000000000) (-32053379520 / 1000000000000), orderedInterval (-60673163412 / 1000000000000) (-60673163411 / 1000000000000))
    | 9 => (orderedInterval (13243932257 / 1000000000000) (13243932258 / 1000000000000), orderedInterval (53847644390 / 1000000000000) (53847644391 / 1000000000000))
    | 10 => (orderedInterval (52414147216 / 1000000000000) (52414147217 / 1000000000000), orderedInterval (50620668360 / 1000000000000) (50620668361 / 1000000000000))
    | 11 => (orderedInterval (-45270641927 / 1000000000000) (-45270583747 / 1000000000000), orderedInterval (31014889607 / 1000000000000) (31014947788 / 1000000000000))
    | 12 => (orderedInterval (-41559024028 / 1000000000000) (-41559024027 / 1000000000000), orderedInterval (-38479733562 / 1000000000000) (-38479733561 / 1000000000000))
    | 13 => (orderedInterval (-42473855633 / 1000000000000) (-42473855632 / 1000000000000), orderedInterval (-51833433404 / 1000000000000) (-51833433403 / 1000000000000))
    | 14 => (orderedInterval (-43018766583 / 1000000000000) (-43018766582 / 1000000000000), orderedInterval (-45948259348 / 1000000000000) (-45948259347 / 1000000000000))
    | 15 => (orderedInterval (47378298774 / 1000000000000) (47378347810 / 1000000000000), orderedInterval (-50399696938 / 1000000000000) (-50399647902 / 1000000000000))
    | 16 => (orderedInterval (-41637818797 / 1000000000000) (-41637806149 / 1000000000000), orderedInterval (60688334499 / 1000000000000) (60688347147 / 1000000000000))
    | 17 => (orderedInterval (51585088932 / 1000000000000) (51585124253 / 1000000000000), orderedInterval (-32739028905 / 1000000000000) (-32738993584 / 1000000000000))
    | 18 => (orderedInterval (74292606136 / 1000000000000) (74292606137 / 1000000000000), orderedInterval (34397993789 / 1000000000000) (34397993790 / 1000000000000))
    | 19 => (orderedInterval (-57877165833 / 1000000000000) (-57877125797 / 1000000000000), orderedInterval (68103726566 / 1000000000000) (68103766602 / 1000000000000))
    | 20 => (orderedInterval (72296290755 / 1000000000000) (72296290756 / 1000000000000), orderedInterval (85652161788 / 1000000000000) (85652161789 / 1000000000000))
    | 21 => (orderedInterval (74551098098 / 1000000000000) (74551105526 / 1000000000000), orderedInterval (-135672973046 / 1000000000000) (-135672965618 / 1000000000000))
    | 22 => (orderedInterval (-90745635331 / 1000000000000) (-90745634692 / 1000000000000), orderedInterval (21908555339 / 1000000000000) (21908555977 / 1000000000000))
    | 23 => (orderedInterval (23785999149 / 1000000000000) (23785999150 / 1000000000000), orderedInterval (76021348141 / 1000000000000) (76021348142 / 1000000000000))
    | 24 => (orderedInterval (-95705821052 / 1000000000000) (-95705766266 / 1000000000000), orderedInterval (77867884995 / 1000000000000) (77867939781 / 1000000000000))
    | 25 => (orderedInterval (2190924923 / 1000000000000) (2190924930 / 1000000000000), orderedInterval (-60811020037 / 1000000000000) (-60811020030 / 1000000000000))
    | _ => (orderedInterval (41338081436 / 1000000000000) (41338092626 / 1000000000000), orderedInterval (-62094951678 / 1000000000000) (-62094940487 / 1000000000000))
  chunkTarget := fun r b =>
    match r.val with
    | 0 =>
      match b.val with
      | 0 => orderedInterval (-31183422228 / 1000000000000) (-31183409572 / 1000000000000)
      | 1 => orderedInterval (-9140164998 / 1000000000000) (-9140164980 / 1000000000000)
      | 2 => orderedInterval (-2593862774 / 1000000000000) (-2593862766 / 1000000000000)
      | 3 => orderedInterval (-4905318366 / 1000000000000) (-4905310057 / 1000000000000)
      | 4 => orderedInterval (-3048481152 / 1000000000000) (-3048481140 / 1000000000000)
      | 5 => orderedInterval (4250684276 / 1000000000000) (4250686480 / 1000000000000)
      | 6 => orderedInterval (-6249358118 / 1000000000000) (-6249355828 / 1000000000000)
      | 7 => orderedInterval (-1140793297 / 1000000000000) (-1140793134 / 1000000000000)
      | _ => orderedInterval (-8511414029 / 1000000000000) (-8511411572 / 1000000000000)
    | 1 =>
      match b.val with
      | 0 => orderedInterval (16181945977 / 1000000000000) (16181958634 / 1000000000000)
      | 1 => orderedInterval (-3820325749 / 1000000000000) (-3820325735 / 1000000000000)
      | 2 => orderedInterval (-2159510128 / 1000000000000) (-2159510115 / 1000000000000)
      | 3 => orderedInterval (-6452469474 / 1000000000000) (-6452450449 / 1000000000000)
      | 4 => orderedInterval (-5597525400 / 1000000000000) (-5597525381 / 1000000000000)
      | 5 => orderedInterval (-6821173012 / 1000000000000) (-6821169585 / 1000000000000)
      | 6 => orderedInterval (-7454935662 / 1000000000000) (-7454933675 / 1000000000000)
      | 7 => orderedInterval (-5965552805 / 1000000000000) (-5965552743 / 1000000000000)
      | _ => orderedInterval (23889222054 / 1000000000000) (23889224851 / 1000000000000)
    | 2 =>
      match b.val with
      | 0 => orderedInterval (32471071645 / 1000000000000) (32471084439 / 1000000000000)
      | 1 => orderedInterval (12046473124 / 1000000000000) (12046473143 / 1000000000000)
      | 2 => orderedInterval (8790701672 / 1000000000000) (8790701696 / 1000000000000)
      | 3 => orderedInterval (39138381007 / 1000000000000) (39138424783 / 1000000000000)
      | 4 => orderedInterval (5341768909 / 1000000000000) (5341768940 / 1000000000000)
      | 5 => orderedInterval (-9460635514 / 1000000000000) (-9460630006 / 1000000000000)
      | 6 => orderedInterval (9352515382 / 1000000000000) (9352517128 / 1000000000000)
      | 7 => orderedInterval (1022771058 / 1000000000000) (1022771090 / 1000000000000)
      | _ => orderedInterval (12443411259 / 1000000000000) (12443414653 / 1000000000000)
    | 3 =>
      match b.val with
      | 0 => orderedInterval (-14998649377 / 1000000000000) (-14998636585 / 1000000000000)
      | 1 => orderedInterval (6046628220 / 1000000000000) (6046628248 / 1000000000000)
      | 2 => orderedInterval (4531831453 / 1000000000000) (4531831496 / 1000000000000)
      | 3 => orderedInterval (45471407999 / 1000000000000) (45471508263 / 1000000000000)
      | 4 => orderedInterval (9391102448 / 1000000000000) (9391102499 / 1000000000000)
      | 5 => orderedInterval (14364271592 / 1000000000000) (14364280605 / 1000000000000)
      | 6 => orderedInterval (7850859202 / 1000000000000) (7850860718 / 1000000000000)
      | 7 => orderedInterval (7549276150 / 1000000000000) (7549276172 / 1000000000000)
      | _ => orderedInterval (-54321298021 / 1000000000000) (-54321293845 / 1000000000000)
    | _ =>
      match b.val with
      | 0 => orderedInterval (-34467134444 / 1000000000000) (-34467121515 / 1000000000000)
      | 1 => orderedInterval (-27452233750 / 1000000000000) (-27452233708 / 1000000000000)
      | 2 => orderedInterval (-31473241325 / 1000000000000) (-31473241244 / 1000000000000)
      | 3 => orderedInterval (-226279241526 / 1000000000000) (-226279010791 / 1000000000000)
      | 4 => orderedInterval (-4362103313 / 1000000000000) (-4362103224 / 1000000000000)
      | 5 => orderedInterval (23814802350 / 1000000000000) (23814817537 / 1000000000000)
      | 6 => orderedInterval (-11114853880 / 1000000000000) (-11114852548 / 1000000000000)
      | 7 => orderedInterval (-1858559385 / 1000000000000) (-1858559367 / 1000000000000)
      | _ => orderedInterval (-19436960518 / 1000000000000) (-19436955282 / 1000000000000)
  coefficientTarget := fun i =>
    match i.val with
    | 0 => orderedInterval (-62522130686 / 1000000000000) (-62522102569 / 1000000000000)
    | 1 => orderedInterval (1799675801 / 1000000000000) (1799715802 / 1000000000000)
    | 2 => orderedInterval (111146458542 / 1000000000000) (111146525866 / 1000000000000)
    | 3 => orderedInterval (25885429666 / 1000000000000) (25885557571 / 1000000000000)
    | _ => orderedInterval (-332629525791 / 1000000000000) (-332629260142 / 1000000000000)

theorem compactCertificate206_stateChecks0 :
    compactCertificate206.stateChecks 0 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 29 12 (5919 / 64)) (orderedInterval (-68873778697 / 1000000000000) (-68873746790 / 1000000000000), orderedInterval (46631436378 / 1000000000000) (46631468285 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 22 12 (8719817220626019 / 128000000000000)) (orderedInterval (-19953213777 / 1000000000000) (-19953213596 / 1000000000000), orderedInterval (94735936522 / 1000000000000) (94735936703 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 35 12 (2819809729199427 / 25600000000000)) (orderedInterval (-63024374948 / 1000000000000) (-63024374947 / 1000000000000), orderedInterval (-42229082286 / 1000000000000) (-42229082285 / 1000000000000))) = true
  norm_num [besselStateAtRationalPoint, besselIntervalStepZero,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, besselZeroTransition,
    besselInitial, besselGridStateAt, besselGridStateBlock00, besselGridStateBlock01,
    besselGridStateBlock02, besselGridStateBlock03, besselGridStateBlock04,
    besselGridStateBlock05, besselGridStateBlock06, besselGridStateBlock07,
    besselGridStateBlock08, besselGridStateBlock09, besselGridStateBlock10,
    besselGridStateBlock11, besselGridStateBlock12, besselGridStateBlock13,
    besselGridStateBlock14, besselGridState006, besselGridState009, besselGridState013, besselGridState016, besselGridState017, besselGridState022, besselGridState023, besselGridState026, besselGridState029, besselGridState030, besselGridState032, besselGridState034, besselGridState035, besselGridState037, besselGridState038, besselGridState043, besselGridState045, besselGridState046, besselGridState051, besselGridState054, besselGridState055, besselGridState058, besselGridState063, besselGridState066, besselGridState067, besselStateSubset, linearInterval, widenInterval,
    rationalErrorInterval, rationalIntervalSubset, orderedInterval, Finset.sum_range_succ,
    IntervalRat.add, IntervalRat.mul, IntervalRat.scale, IntervalRat.singleton]

theorem compactCertificate206_stateChecks1 :
    compactCertificate206.stateChecks 3 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 6 12 (2544420917445033 / 128000000000000)) (orderedInterval (173925633310 / 1000000000000) (173925633834 / 1000000000000), orderedInterval (-46405139523 / 1000000000000) (-46405138999 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 17 12 (6834672486665301 / 128000000000000)) (orderedInterval (-76155692756 / 1000000000000) (-76155692755 / 1000000000000), orderedInterval (-77536305525 / 1000000000000) (-77536305524 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 46 12 (18557465334439617 / 128000000000000)) (orderedInterval (62915184328 / 1000000000000) (62915184329 / 1000000000000), orderedInterval (20585415181 / 1000000000000) (20585415182 / 1000000000000))) = true
  norm_num [besselStateAtRationalPoint, besselIntervalStepZero,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, besselZeroTransition,
    besselInitial, besselGridStateAt, besselGridStateBlock00, besselGridStateBlock01,
    besselGridStateBlock02, besselGridStateBlock03, besselGridStateBlock04,
    besselGridStateBlock05, besselGridStateBlock06, besselGridStateBlock07,
    besselGridStateBlock08, besselGridStateBlock09, besselGridStateBlock10,
    besselGridStateBlock11, besselGridStateBlock12, besselGridStateBlock13,
    besselGridStateBlock14, besselGridState006, besselGridState009, besselGridState013, besselGridState016, besselGridState017, besselGridState022, besselGridState023, besselGridState026, besselGridState029, besselGridState030, besselGridState032, besselGridState034, besselGridState035, besselGridState037, besselGridState038, besselGridState043, besselGridState045, besselGridState046, besselGridState051, besselGridState054, besselGridState055, besselGridState058, besselGridState063, besselGridState066, besselGridState067, besselStateSubset, linearInterval, widenInterval,
    rationalErrorInterval, rationalIntervalSubset, orderedInterval, Finset.sum_range_succ,
    IntervalRat.add, IntervalRat.mul, IntervalRat.scale, IntervalRat.singleton]

theorem compactCertificate206_stateChecks2 :
    compactCertificate206.stateChecks 6 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 34 12 (13669344973336521 / 128000000000000)) (orderedInterval (53293654186 / 1000000000000) (53293654187 / 1000000000000), orderedInterval (55617369303 / 1000000000000) (55617369304 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 58 12 (23422655598333933 / 128000000000000)) (orderedInterval (58980539757 / 1000000000000) (58980539810 / 1000000000000), orderedInterval (367224289 / 1000000000000) (367224342 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 43 12 (17253022101621447 / 128000000000000)) (orderedInterval (-32053379521 / 1000000000000) (-32053379520 / 1000000000000), orderedInterval (-60673163412 / 1000000000000) (-60673163411 / 1000000000000))) = true
  norm_num [besselStateAtRationalPoint, besselIntervalStepZero,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, besselZeroTransition,
    besselInitial, besselGridStateAt, besselGridStateBlock00, besselGridStateBlock01,
    besselGridStateBlock02, besselGridStateBlock03, besselGridStateBlock04,
    besselGridStateBlock05, besselGridStateBlock06, besselGridStateBlock07,
    besselGridStateBlock08, besselGridStateBlock09, besselGridStateBlock10,
    besselGridStateBlock11, besselGridStateBlock12, besselGridStateBlock13,
    besselGridStateBlock14, besselGridState006, besselGridState009, besselGridState013, besselGridState016, besselGridState017, besselGridState022, besselGridState023, besselGridState026, besselGridState029, besselGridState030, besselGridState032, besselGridState034, besselGridState035, besselGridState037, besselGridState038, besselGridState043, besselGridState045, besselGridState046, besselGridState051, besselGridState054, besselGridState055, besselGridState058, besselGridState063, besselGridState066, besselGridState067, besselStateSubset, linearInterval, widenInterval,
    rationalErrorInterval, rationalIntervalSubset, orderedInterval, Finset.sum_range_succ,
    IntervalRat.add, IntervalRat.mul, IntervalRat.scale, IntervalRat.singleton]

theorem compactCertificate206_stateChecks3 :
    compactCertificate206.stateChecks 9 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 66 12 (26470572717639081 / 128000000000000)) (orderedInterval (13243932257 / 1000000000000) (13243932258 / 1000000000000), orderedInterval (53847644390 / 1000000000000) (53847644391 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 38 12 (15282792284130849 / 128000000000000)) (orderedInterval (52414147216 / 1000000000000) (52414147217 / 1000000000000), orderedInterval (50620668360 / 1000000000000) (50620668361 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 67 12 (27119583095574741 / 128000000000000)) (orderedInterval (-45270641927 / 1000000000000) (-45270583747 / 1000000000000), orderedInterval (31014889607 / 1000000000000) (31014947788 / 1000000000000))) = true
  norm_num [besselStateAtRationalPoint, besselIntervalStepZero,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, besselZeroTransition,
    besselInitial, besselGridStateAt, besselGridStateBlock00, besselGridStateBlock01,
    besselGridStateBlock02, besselGridStateBlock03, besselGridStateBlock04,
    besselGridStateBlock05, besselGridStateBlock06, besselGridStateBlock07,
    besselGridStateBlock08, besselGridStateBlock09, besselGridStateBlock10,
    besselGridStateBlock11, besselGridStateBlock12, besselGridStateBlock13,
    besselGridStateBlock14, besselGridState006, besselGridState009, besselGridState013, besselGridState016, besselGridState017, besselGridState022, besselGridState023, besselGridState026, besselGridState029, besselGridState030, besselGridState032, besselGridState034, besselGridState035, besselGridState037, besselGridState038, besselGridState043, besselGridState045, besselGridState046, besselGridState051, besselGridState054, besselGridState055, besselGridState058, besselGridState063, besselGridState066, besselGridState067, besselStateSubset, linearInterval, widenInterval,
    rationalErrorInterval, rationalIntervalSubset, orderedInterval, Finset.sum_range_succ,
    IntervalRat.add, IntervalRat.mul, IntervalRat.scale, IntervalRat.singleton]

theorem compactCertificate206_stateChecks4 :
    compactCertificate206.stateChecks 12 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 63 12 (25338632387680329 / 128000000000000)) (orderedInterval (-41559024028 / 1000000000000) (-41559024027 / 1000000000000), orderedInterval (-38479733562 / 1000000000000) (-38479733561 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 45 12 (18082843692290457 / 128000000000000)) (orderedInterval (-42473855633 / 1000000000000) (-42473855632 / 1000000000000), orderedInterval (-51833433404 / 1000000000000) (-51833433403 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 51 12 (20504017459995903 / 128000000000000)) (orderedInterval (-43018766583 / 1000000000000) (-43018766582 / 1000000000000), orderedInterval (-45948259348 / 1000000000000) (-45948259347 / 1000000000000))) = true
  norm_num [besselStateAtRationalPoint, besselIntervalStepZero,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, besselZeroTransition,
    besselInitial, besselGridStateAt, besselGridStateBlock00, besselGridStateBlock01,
    besselGridStateBlock02, besselGridStateBlock03, besselGridStateBlock04,
    besselGridStateBlock05, besselGridStateBlock06, besselGridStateBlock07,
    besselGridStateBlock08, besselGridStateBlock09, besselGridStateBlock10,
    besselGridStateBlock11, besselGridStateBlock12, besselGridStateBlock13,
    besselGridStateBlock14, besselGridState006, besselGridState009, besselGridState013, besselGridState016, besselGridState017, besselGridState022, besselGridState023, besselGridState026, besselGridState029, besselGridState030, besselGridState032, besselGridState034, besselGridState035, besselGridState037, besselGridState038, besselGridState043, besselGridState045, besselGridState046, besselGridState051, besselGridState054, besselGridState055, besselGridState058, besselGridState063, besselGridState066, besselGridState067, besselStateSubset, linearInterval, widenInterval,
    rationalErrorInterval, rationalIntervalSubset, orderedInterval, Finset.sum_range_succ,
    IntervalRat.add, IntervalRat.mul, IntervalRat.scale, IntervalRat.singleton]

theorem compactCertificate206_stateChecks5 :
    compactCertificate206.stateChecks 15 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 43 12 (17094112106865807 / 128000000000000)) (orderedInterval (47378298774 / 1000000000000) (47378347810 / 1000000000000), orderedInterval (-50399696938 / 1000000000000) (-50399647902 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 38 12 (15103166458825947 / 128000000000000)) (orderedInterval (-41637818797 / 1000000000000) (-41637806149 / 1000000000000), orderedInterval (60688334499 / 1000000000000) (60688347147 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 54 12 (4377486313956753 / 25600000000000)) (orderedInterval (51585088932 / 1000000000000) (51585124253 / 1000000000000), orderedInterval (-32739028905 / 1000000000000) (-32738993584 / 1000000000000))) = true
  norm_num [besselStateAtRationalPoint, besselIntervalStepZero,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, besselZeroTransition,
    besselInitial, besselGridStateAt, besselGridStateBlock00, besselGridStateBlock01,
    besselGridStateBlock02, besselGridStateBlock03, besselGridStateBlock04,
    besselGridStateBlock05, besselGridStateBlock06, besselGridStateBlock07,
    besselGridStateBlock08, besselGridStateBlock09, besselGridStateBlock10,
    besselGridStateBlock11, besselGridStateBlock12, besselGridStateBlock13,
    besselGridStateBlock14, besselGridState006, besselGridState009, besselGridState013, besselGridState016, besselGridState017, besselGridState022, besselGridState023, besselGridState026, besselGridState029, besselGridState030, besselGridState032, besselGridState034, besselGridState035, besselGridState037, besselGridState038, besselGridState043, besselGridState045, besselGridState046, besselGridState051, besselGridState054, besselGridState055, besselGridState058, besselGridState063, besselGridState066, besselGridState067, besselStateSubset, linearInterval, widenInterval,
    rationalErrorInterval, rationalIntervalSubset, orderedInterval, Finset.sum_range_succ,
    IntervalRat.add, IntervalRat.mul, IntervalRat.scale, IntervalRat.singleton]

theorem compactCertificate206_stateChecks6 :
    compactCertificate206.stateChecks 18 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 30 12 (12108357518887491 / 128000000000000)) (orderedInterval (74292606136 / 1000000000000) (74292606137 / 1000000000000), orderedInterval (34397993789 / 1000000000000) (34397993790 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 26 12 (10264388765148651 / 128000000000000)) (orderedInterval (-57877165833 / 1000000000000) (-57877125797 / 1000000000000), orderedInterval (68103726566 / 1000000000000) (68103766602 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 16 12 (6422977898378553 / 128000000000000)) (orderedInterval (72296290755 / 1000000000000) (72296290756 / 1000000000000), orderedInterval (85652161788 / 1000000000000) (85652161789 / 1000000000000))) = true
  norm_num [besselStateAtRationalPoint, besselIntervalStepZero,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, besselZeroTransition,
    besselInitial, besselGridStateAt, besselGridStateBlock00, besselGridStateBlock01,
    besselGridStateBlock02, besselGridStateBlock03, besselGridStateBlock04,
    besselGridStateBlock05, besselGridStateBlock06, besselGridStateBlock07,
    besselGridStateBlock08, besselGridStateBlock09, besselGridStateBlock10,
    besselGridStateBlock11, besselGridStateBlock12, besselGridStateBlock13,
    besselGridStateBlock14, besselGridState006, besselGridState009, besselGridState013, besselGridState016, besselGridState017, besselGridState022, besselGridState023, besselGridState026, besselGridState029, besselGridState030, besselGridState032, besselGridState034, besselGridState035, besselGridState037, besselGridState038, besselGridState043, besselGridState045, besselGridState046, besselGridState051, besselGridState054, besselGridState055, besselGridState058, besselGridState063, besselGridState066, besselGridState067, besselStateSubset, linearInterval, widenInterval,
    rationalErrorInterval, rationalIntervalSubset, orderedInterval, Finset.sum_range_succ,
    IntervalRat.add, IntervalRat.mul, IntervalRat.scale, IntervalRat.singleton]

theorem compactCertificate206_stateChecks7 :
    compactCertificate206.stateChecks 21 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 9 12 (3454298875607751 / 128000000000000)) (orderedInterval (74551098098 / 1000000000000) (74551105526 / 1000000000000), orderedInterval (-135672973046 / 1000000000000) (-135672965618 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 23 12 (9379093404116253 / 128000000000000)) (orderedInterval (-90745635331 / 1000000000000) (-90745634692 / 1000000000000), orderedInterval (21908555339 / 1000000000000) (21908555977 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 32 12 (12806350199961981 / 128000000000000)) (orderedInterval (23785999149 / 1000000000000) (23785999150 / 1000000000000), orderedInterval (76021348141 / 1000000000000) (76021348142 / 1000000000000))) = true
  norm_num [besselStateAtRationalPoint, besselIntervalStepZero,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, besselZeroTransition,
    besselInitial, besselGridStateAt, besselGridStateBlock00, besselGridStateBlock01,
    besselGridStateBlock02, besselGridStateBlock03, besselGridStateBlock04,
    besselGridStateBlock05, besselGridStateBlock06, besselGridStateBlock07,
    besselGridStateBlock08, besselGridStateBlock09, besselGridStateBlock10,
    besselGridStateBlock11, besselGridStateBlock12, besselGridStateBlock13,
    besselGridStateBlock14, besselGridState006, besselGridState009, besselGridState013, besselGridState016, besselGridState017, besselGridState022, besselGridState023, besselGridState026, besselGridState029, besselGridState030, besselGridState032, besselGridState034, besselGridState035, besselGridState037, besselGridState038, besselGridState043, besselGridState045, besselGridState046, besselGridState051, besselGridState054, besselGridState055, besselGridState058, besselGridState063, besselGridState066, besselGridState067, besselStateSubset, linearInterval, widenInterval,
    rationalErrorInterval, rationalIntervalSubset, orderedInterval, Finset.sum_range_succ,
    IntervalRat.add, IntervalRat.mul, IntervalRat.scale, IntervalRat.singleton]

theorem compactCertificate206_stateChecks8 :
    compactCertificate206.stateChecks 24 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 13 12 (5415022101621447 / 128000000000000)) (orderedInterval (-95705821052 / 1000000000000) (-95705766266 / 1000000000000), orderedInterval (77867884995 / 1000000000000) (77867939781 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 55 12 (22011764210053287 / 128000000000000)) (orderedInterval (2190924923 / 1000000000000) (2190924930 / 1000000000000), orderedInterval (-60811020037 / 1000000000000) (-60811020030 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 37 12 (14702838377713833 / 128000000000000)) (orderedInterval (41338081436 / 1000000000000) (41338092626 / 1000000000000), orderedInterval (-62094951678 / 1000000000000) (-62094940487 / 1000000000000))) = true
  norm_num [besselStateAtRationalPoint, besselIntervalStepZero,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, besselZeroTransition,
    besselInitial, besselGridStateAt, besselGridStateBlock00, besselGridStateBlock01,
    besselGridStateBlock02, besselGridStateBlock03, besselGridStateBlock04,
    besselGridStateBlock05, besselGridStateBlock06, besselGridStateBlock07,
    besselGridStateBlock08, besselGridStateBlock09, besselGridStateBlock10,
    besselGridStateBlock11, besselGridStateBlock12, besselGridStateBlock13,
    besselGridStateBlock14, besselGridState006, besselGridState009, besselGridState013, besselGridState016, besselGridState017, besselGridState022, besselGridState023, besselGridState026, besselGridState029, besselGridState030, besselGridState032, besselGridState034, besselGridState035, besselGridState037, besselGridState038, besselGridState043, besselGridState045, besselGridState046, besselGridState051, besselGridState054, besselGridState055, besselGridState058, besselGridState063, besselGridState066, besselGridState067, besselStateSubset, linearInterval, widenInterval,
    rationalErrorInterval, rationalIntervalSubset, orderedInterval, Finset.sum_range_succ,
    IntervalRat.add, IntervalRat.mul, IntervalRat.scale, IntervalRat.singleton]

theorem compactCertificate206_states : ∀ j,
    BesselStateValid (compactCertificate206.point j) (compactCertificate206.state j) :=
  compactCertificate206.statesValid_of_checks3 compactCertificate206_stateChecks0
    compactCertificate206_stateChecks1 compactCertificate206_stateChecks2
    compactCertificate206_stateChecks3 compactCertificate206_stateChecks4
    compactCertificate206_stateChecks5 compactCertificate206_stateChecks6
    compactCertificate206_stateChecks7 compactCertificate206_stateChecks8

theorem compactCertificate206_chunkChecks0_0 :
    compactCertificate206.chunkChecks (0 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 0) <| besselDerivativeNearFromState (5919 / 64) 0 (IntervalRat.scale (5919 / 64) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-68873778697 / 1000000000000) (-68873746790 / 1000000000000), orderedInterval (46631436378 / 1000000000000) (46631468285 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 0) <| besselDerivativeNearFromState (8719817220626019 / 128000000000000) 0 (IntervalRat.scale (5919 / 64) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-19953213777 / 1000000000000) (-19953213596 / 1000000000000), orderedInterval (94735936522 / 1000000000000) (94735936703 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 0) <| besselDerivativeNearFromState (2819809729199427 / 25600000000000) 0 (IntervalRat.scale (5919 / 64) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-63024374948 / 1000000000000) (-63024374947 / 1000000000000), orderedInterval (-42229082286 / 1000000000000) (-42229082285 / 1000000000000)))) (orderedInterval (-31183422228 / 1000000000000) (-31183409572 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 0) <| besselDerivativeNearFromState (2544420917445033 / 128000000000000) 0 (IntervalRat.scale (5919 / 64) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (173925633310 / 1000000000000) (173925633834 / 1000000000000), orderedInterval (-46405139523 / 1000000000000) (-46405138999 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 0) <| besselDerivativeNearFromState (6834672486665301 / 128000000000000) 0 (IntervalRat.scale (5919 / 64) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-76155692756 / 1000000000000) (-76155692755 / 1000000000000), orderedInterval (-77536305525 / 1000000000000) (-77536305524 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 0) <| besselDerivativeNearFromState (18557465334439617 / 128000000000000) 0 (IntervalRat.scale (5919 / 64) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (62915184328 / 1000000000000) (62915184329 / 1000000000000), orderedInterval (20585415181 / 1000000000000) (20585415182 / 1000000000000)))) (orderedInterval (-9140164998 / 1000000000000) (-9140164980 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 0) <| besselDerivativeNearFromState (13669344973336521 / 128000000000000) 0 (IntervalRat.scale (5919 / 64) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (53293654186 / 1000000000000) (53293654187 / 1000000000000), orderedInterval (55617369303 / 1000000000000) (55617369304 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 0) <| besselDerivativeNearFromState (23422655598333933 / 128000000000000) 0 (IntervalRat.scale (5919 / 64) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (58980539757 / 1000000000000) (58980539810 / 1000000000000), orderedInterval (367224289 / 1000000000000) (367224342 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 0) <| besselDerivativeNearFromState (17253022101621447 / 128000000000000) 0 (IntervalRat.scale (5919 / 64) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-32053379521 / 1000000000000) (-32053379520 / 1000000000000), orderedInterval (-60673163412 / 1000000000000) (-60673163411 / 1000000000000)))) (orderedInterval (-2593862774 / 1000000000000) (-2593862766 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate206_chunkChecks0_1 :
    compactCertificate206.chunkChecks (0 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 0) <| besselDerivativeNearFromState (26470572717639081 / 128000000000000) 0 (IntervalRat.scale (5919 / 64) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (13243932257 / 1000000000000) (13243932258 / 1000000000000), orderedInterval (53847644390 / 1000000000000) (53847644391 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 0) <| besselDerivativeNearFromState (15282792284130849 / 128000000000000) 0 (IntervalRat.scale (5919 / 64) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (52414147216 / 1000000000000) (52414147217 / 1000000000000), orderedInterval (50620668360 / 1000000000000) (50620668361 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 0) <| besselDerivativeNearFromState (27119583095574741 / 128000000000000) 0 (IntervalRat.scale (5919 / 64) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-45270641927 / 1000000000000) (-45270583747 / 1000000000000), orderedInterval (31014889607 / 1000000000000) (31014947788 / 1000000000000)))) (orderedInterval (-4905318366 / 1000000000000) (-4905310057 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 0) <| besselDerivativeNearFromState (25338632387680329 / 128000000000000) 0 (IntervalRat.scale (5919 / 64) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-41559024028 / 1000000000000) (-41559024027 / 1000000000000), orderedInterval (-38479733562 / 1000000000000) (-38479733561 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 0) <| besselDerivativeNearFromState (18082843692290457 / 128000000000000) 0 (IntervalRat.scale (5919 / 64) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-42473855633 / 1000000000000) (-42473855632 / 1000000000000), orderedInterval (-51833433404 / 1000000000000) (-51833433403 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 0) <| besselDerivativeNearFromState (20504017459995903 / 128000000000000) 0 (IntervalRat.scale (5919 / 64) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-43018766583 / 1000000000000) (-43018766582 / 1000000000000), orderedInterval (-45948259348 / 1000000000000) (-45948259347 / 1000000000000)))) (orderedInterval (-3048481152 / 1000000000000) (-3048481140 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 0) <| besselDerivativeNearFromState (17094112106865807 / 128000000000000) 0 (IntervalRat.scale (5919 / 64) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (47378298774 / 1000000000000) (47378347810 / 1000000000000), orderedInterval (-50399696938 / 1000000000000) (-50399647902 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 0) <| besselDerivativeNearFromState (15103166458825947 / 128000000000000) 0 (IntervalRat.scale (5919 / 64) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-41637818797 / 1000000000000) (-41637806149 / 1000000000000), orderedInterval (60688334499 / 1000000000000) (60688347147 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 0) <| besselDerivativeNearFromState (4377486313956753 / 25600000000000) 0 (IntervalRat.scale (5919 / 64) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (51585088932 / 1000000000000) (51585124253 / 1000000000000), orderedInterval (-32739028905 / 1000000000000) (-32738993584 / 1000000000000)))) (orderedInterval (4250684276 / 1000000000000) (4250686480 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate206_chunkChecks0_2 :
    compactCertificate206.chunkChecks (0 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 0) <| besselDerivativeNearFromState (12108357518887491 / 128000000000000) 0 (IntervalRat.scale (5919 / 64) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (74292606136 / 1000000000000) (74292606137 / 1000000000000), orderedInterval (34397993789 / 1000000000000) (34397993790 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 0) <| besselDerivativeNearFromState (10264388765148651 / 128000000000000) 0 (IntervalRat.scale (5919 / 64) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-57877165833 / 1000000000000) (-57877125797 / 1000000000000), orderedInterval (68103726566 / 1000000000000) (68103766602 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 0) <| besselDerivativeNearFromState (6422977898378553 / 128000000000000) 0 (IntervalRat.scale (5919 / 64) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (72296290755 / 1000000000000) (72296290756 / 1000000000000), orderedInterval (85652161788 / 1000000000000) (85652161789 / 1000000000000)))) (orderedInterval (-6249358118 / 1000000000000) (-6249355828 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 0) <| besselDerivativeNearFromState (3454298875607751 / 128000000000000) 0 (IntervalRat.scale (5919 / 64) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (74551098098 / 1000000000000) (74551105526 / 1000000000000), orderedInterval (-135672973046 / 1000000000000) (-135672965618 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 0) <| besselDerivativeNearFromState (9379093404116253 / 128000000000000) 0 (IntervalRat.scale (5919 / 64) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-90745635331 / 1000000000000) (-90745634692 / 1000000000000), orderedInterval (21908555339 / 1000000000000) (21908555977 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 0) <| besselDerivativeNearFromState (12806350199961981 / 128000000000000) 0 (IntervalRat.scale (5919 / 64) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (23785999149 / 1000000000000) (23785999150 / 1000000000000), orderedInterval (76021348141 / 1000000000000) (76021348142 / 1000000000000)))) (orderedInterval (-1140793297 / 1000000000000) (-1140793134 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 0) <| besselDerivativeNearFromState (5415022101621447 / 128000000000000) 0 (IntervalRat.scale (5919 / 64) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-95705821052 / 1000000000000) (-95705766266 / 1000000000000), orderedInterval (77867884995 / 1000000000000) (77867939781 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 0) <| besselDerivativeNearFromState (22011764210053287 / 128000000000000) 0 (IntervalRat.scale (5919 / 64) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (2190924923 / 1000000000000) (2190924930 / 1000000000000), orderedInterval (-60811020037 / 1000000000000) (-60811020030 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 0) <| besselDerivativeNearFromState (14702838377713833 / 128000000000000) 0 (IntervalRat.scale (5919 / 64) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (41338081436 / 1000000000000) (41338092626 / 1000000000000), orderedInterval (-62094951678 / 1000000000000) (-62094940487 / 1000000000000)))) (orderedInterval (-8511414029 / 1000000000000) (-8511411572 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate206_chunkChecks0 :
    compactCertificate206.chunkChecks (0 : Fin 5) 0 9 = true :=
  compactCertificate206.chunkChecks_nine_of_three (0 : Fin 5) compactCertificate206_chunkChecks0_0
    compactCertificate206_chunkChecks0_1 compactCertificate206_chunkChecks0_2

theorem compactCertificate206_chunkChecks1_0 :
    compactCertificate206.chunkChecks (1 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 1) <| besselDerivativeNearFromState (5919 / 64) 1 (IntervalRat.scale (5919 / 64) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-68873778697 / 1000000000000) (-68873746790 / 1000000000000), orderedInterval (46631436378 / 1000000000000) (46631468285 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 1) <| besselDerivativeNearFromState (8719817220626019 / 128000000000000) 1 (IntervalRat.scale (5919 / 64) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-19953213777 / 1000000000000) (-19953213596 / 1000000000000), orderedInterval (94735936522 / 1000000000000) (94735936703 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 1) <| besselDerivativeNearFromState (2819809729199427 / 25600000000000) 1 (IntervalRat.scale (5919 / 64) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-63024374948 / 1000000000000) (-63024374947 / 1000000000000), orderedInterval (-42229082286 / 1000000000000) (-42229082285 / 1000000000000)))) (orderedInterval (16181945977 / 1000000000000) (16181958634 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 1) <| besselDerivativeNearFromState (2544420917445033 / 128000000000000) 1 (IntervalRat.scale (5919 / 64) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (173925633310 / 1000000000000) (173925633834 / 1000000000000), orderedInterval (-46405139523 / 1000000000000) (-46405138999 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 1) <| besselDerivativeNearFromState (6834672486665301 / 128000000000000) 1 (IntervalRat.scale (5919 / 64) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-76155692756 / 1000000000000) (-76155692755 / 1000000000000), orderedInterval (-77536305525 / 1000000000000) (-77536305524 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 1) <| besselDerivativeNearFromState (18557465334439617 / 128000000000000) 1 (IntervalRat.scale (5919 / 64) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (62915184328 / 1000000000000) (62915184329 / 1000000000000), orderedInterval (20585415181 / 1000000000000) (20585415182 / 1000000000000)))) (orderedInterval (-3820325749 / 1000000000000) (-3820325735 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 1) <| besselDerivativeNearFromState (13669344973336521 / 128000000000000) 1 (IntervalRat.scale (5919 / 64) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (53293654186 / 1000000000000) (53293654187 / 1000000000000), orderedInterval (55617369303 / 1000000000000) (55617369304 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 1) <| besselDerivativeNearFromState (23422655598333933 / 128000000000000) 1 (IntervalRat.scale (5919 / 64) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (58980539757 / 1000000000000) (58980539810 / 1000000000000), orderedInterval (367224289 / 1000000000000) (367224342 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 1) <| besselDerivativeNearFromState (17253022101621447 / 128000000000000) 1 (IntervalRat.scale (5919 / 64) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-32053379521 / 1000000000000) (-32053379520 / 1000000000000), orderedInterval (-60673163412 / 1000000000000) (-60673163411 / 1000000000000)))) (orderedInterval (-2159510128 / 1000000000000) (-2159510115 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate206_chunkChecks1_1 :
    compactCertificate206.chunkChecks (1 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 1) <| besselDerivativeNearFromState (26470572717639081 / 128000000000000) 1 (IntervalRat.scale (5919 / 64) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (13243932257 / 1000000000000) (13243932258 / 1000000000000), orderedInterval (53847644390 / 1000000000000) (53847644391 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 1) <| besselDerivativeNearFromState (15282792284130849 / 128000000000000) 1 (IntervalRat.scale (5919 / 64) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (52414147216 / 1000000000000) (52414147217 / 1000000000000), orderedInterval (50620668360 / 1000000000000) (50620668361 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 1) <| besselDerivativeNearFromState (27119583095574741 / 128000000000000) 1 (IntervalRat.scale (5919 / 64) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-45270641927 / 1000000000000) (-45270583747 / 1000000000000), orderedInterval (31014889607 / 1000000000000) (31014947788 / 1000000000000)))) (orderedInterval (-6452469474 / 1000000000000) (-6452450449 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 1) <| besselDerivativeNearFromState (25338632387680329 / 128000000000000) 1 (IntervalRat.scale (5919 / 64) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-41559024028 / 1000000000000) (-41559024027 / 1000000000000), orderedInterval (-38479733562 / 1000000000000) (-38479733561 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 1) <| besselDerivativeNearFromState (18082843692290457 / 128000000000000) 1 (IntervalRat.scale (5919 / 64) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-42473855633 / 1000000000000) (-42473855632 / 1000000000000), orderedInterval (-51833433404 / 1000000000000) (-51833433403 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 1) <| besselDerivativeNearFromState (20504017459995903 / 128000000000000) 1 (IntervalRat.scale (5919 / 64) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-43018766583 / 1000000000000) (-43018766582 / 1000000000000), orderedInterval (-45948259348 / 1000000000000) (-45948259347 / 1000000000000)))) (orderedInterval (-5597525400 / 1000000000000) (-5597525381 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 1) <| besselDerivativeNearFromState (17094112106865807 / 128000000000000) 1 (IntervalRat.scale (5919 / 64) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (47378298774 / 1000000000000) (47378347810 / 1000000000000), orderedInterval (-50399696938 / 1000000000000) (-50399647902 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 1) <| besselDerivativeNearFromState (15103166458825947 / 128000000000000) 1 (IntervalRat.scale (5919 / 64) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-41637818797 / 1000000000000) (-41637806149 / 1000000000000), orderedInterval (60688334499 / 1000000000000) (60688347147 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 1) <| besselDerivativeNearFromState (4377486313956753 / 25600000000000) 1 (IntervalRat.scale (5919 / 64) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (51585088932 / 1000000000000) (51585124253 / 1000000000000), orderedInterval (-32739028905 / 1000000000000) (-32738993584 / 1000000000000)))) (orderedInterval (-6821173012 / 1000000000000) (-6821169585 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate206_chunkChecks1_2 :
    compactCertificate206.chunkChecks (1 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 1) <| besselDerivativeNearFromState (12108357518887491 / 128000000000000) 1 (IntervalRat.scale (5919 / 64) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (74292606136 / 1000000000000) (74292606137 / 1000000000000), orderedInterval (34397993789 / 1000000000000) (34397993790 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 1) <| besselDerivativeNearFromState (10264388765148651 / 128000000000000) 1 (IntervalRat.scale (5919 / 64) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-57877165833 / 1000000000000) (-57877125797 / 1000000000000), orderedInterval (68103726566 / 1000000000000) (68103766602 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 1) <| besselDerivativeNearFromState (6422977898378553 / 128000000000000) 1 (IntervalRat.scale (5919 / 64) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (72296290755 / 1000000000000) (72296290756 / 1000000000000), orderedInterval (85652161788 / 1000000000000) (85652161789 / 1000000000000)))) (orderedInterval (-7454935662 / 1000000000000) (-7454933675 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 1) <| besselDerivativeNearFromState (3454298875607751 / 128000000000000) 1 (IntervalRat.scale (5919 / 64) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (74551098098 / 1000000000000) (74551105526 / 1000000000000), orderedInterval (-135672973046 / 1000000000000) (-135672965618 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 1) <| besselDerivativeNearFromState (9379093404116253 / 128000000000000) 1 (IntervalRat.scale (5919 / 64) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-90745635331 / 1000000000000) (-90745634692 / 1000000000000), orderedInterval (21908555339 / 1000000000000) (21908555977 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 1) <| besselDerivativeNearFromState (12806350199961981 / 128000000000000) 1 (IntervalRat.scale (5919 / 64) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (23785999149 / 1000000000000) (23785999150 / 1000000000000), orderedInterval (76021348141 / 1000000000000) (76021348142 / 1000000000000)))) (orderedInterval (-5965552805 / 1000000000000) (-5965552743 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 1) <| besselDerivativeNearFromState (5415022101621447 / 128000000000000) 1 (IntervalRat.scale (5919 / 64) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-95705821052 / 1000000000000) (-95705766266 / 1000000000000), orderedInterval (77867884995 / 1000000000000) (77867939781 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 1) <| besselDerivativeNearFromState (22011764210053287 / 128000000000000) 1 (IntervalRat.scale (5919 / 64) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (2190924923 / 1000000000000) (2190924930 / 1000000000000), orderedInterval (-60811020037 / 1000000000000) (-60811020030 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 1) <| besselDerivativeNearFromState (14702838377713833 / 128000000000000) 1 (IntervalRat.scale (5919 / 64) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (41338081436 / 1000000000000) (41338092626 / 1000000000000), orderedInterval (-62094951678 / 1000000000000) (-62094940487 / 1000000000000)))) (orderedInterval (23889222054 / 1000000000000) (23889224851 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate206_chunkChecks1 :
    compactCertificate206.chunkChecks (1 : Fin 5) 0 9 = true :=
  compactCertificate206.chunkChecks_nine_of_three (1 : Fin 5) compactCertificate206_chunkChecks1_0
    compactCertificate206_chunkChecks1_1 compactCertificate206_chunkChecks1_2

theorem compactCertificate206_chunkChecks2_0 :
    compactCertificate206.chunkChecks (2 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 2) <| besselDerivativeNearFromState (5919 / 64) 2 (IntervalRat.scale (5919 / 64) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-68873778697 / 1000000000000) (-68873746790 / 1000000000000), orderedInterval (46631436378 / 1000000000000) (46631468285 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 2) <| besselDerivativeNearFromState (8719817220626019 / 128000000000000) 2 (IntervalRat.scale (5919 / 64) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-19953213777 / 1000000000000) (-19953213596 / 1000000000000), orderedInterval (94735936522 / 1000000000000) (94735936703 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 2) <| besselDerivativeNearFromState (2819809729199427 / 25600000000000) 2 (IntervalRat.scale (5919 / 64) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-63024374948 / 1000000000000) (-63024374947 / 1000000000000), orderedInterval (-42229082286 / 1000000000000) (-42229082285 / 1000000000000)))) (orderedInterval (32471071645 / 1000000000000) (32471084439 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 2) <| besselDerivativeNearFromState (2544420917445033 / 128000000000000) 2 (IntervalRat.scale (5919 / 64) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (173925633310 / 1000000000000) (173925633834 / 1000000000000), orderedInterval (-46405139523 / 1000000000000) (-46405138999 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 2) <| besselDerivativeNearFromState (6834672486665301 / 128000000000000) 2 (IntervalRat.scale (5919 / 64) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-76155692756 / 1000000000000) (-76155692755 / 1000000000000), orderedInterval (-77536305525 / 1000000000000) (-77536305524 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 2) <| besselDerivativeNearFromState (18557465334439617 / 128000000000000) 2 (IntervalRat.scale (5919 / 64) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (62915184328 / 1000000000000) (62915184329 / 1000000000000), orderedInterval (20585415181 / 1000000000000) (20585415182 / 1000000000000)))) (orderedInterval (12046473124 / 1000000000000) (12046473143 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 2) <| besselDerivativeNearFromState (13669344973336521 / 128000000000000) 2 (IntervalRat.scale (5919 / 64) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (53293654186 / 1000000000000) (53293654187 / 1000000000000), orderedInterval (55617369303 / 1000000000000) (55617369304 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 2) <| besselDerivativeNearFromState (23422655598333933 / 128000000000000) 2 (IntervalRat.scale (5919 / 64) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (58980539757 / 1000000000000) (58980539810 / 1000000000000), orderedInterval (367224289 / 1000000000000) (367224342 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 2) <| besselDerivativeNearFromState (17253022101621447 / 128000000000000) 2 (IntervalRat.scale (5919 / 64) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-32053379521 / 1000000000000) (-32053379520 / 1000000000000), orderedInterval (-60673163412 / 1000000000000) (-60673163411 / 1000000000000)))) (orderedInterval (8790701672 / 1000000000000) (8790701696 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate206_chunkChecks2_1 :
    compactCertificate206.chunkChecks (2 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 2) <| besselDerivativeNearFromState (26470572717639081 / 128000000000000) 2 (IntervalRat.scale (5919 / 64) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (13243932257 / 1000000000000) (13243932258 / 1000000000000), orderedInterval (53847644390 / 1000000000000) (53847644391 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 2) <| besselDerivativeNearFromState (15282792284130849 / 128000000000000) 2 (IntervalRat.scale (5919 / 64) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (52414147216 / 1000000000000) (52414147217 / 1000000000000), orderedInterval (50620668360 / 1000000000000) (50620668361 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 2) <| besselDerivativeNearFromState (27119583095574741 / 128000000000000) 2 (IntervalRat.scale (5919 / 64) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-45270641927 / 1000000000000) (-45270583747 / 1000000000000), orderedInterval (31014889607 / 1000000000000) (31014947788 / 1000000000000)))) (orderedInterval (39138381007 / 1000000000000) (39138424783 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 2) <| besselDerivativeNearFromState (25338632387680329 / 128000000000000) 2 (IntervalRat.scale (5919 / 64) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-41559024028 / 1000000000000) (-41559024027 / 1000000000000), orderedInterval (-38479733562 / 1000000000000) (-38479733561 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 2) <| besselDerivativeNearFromState (18082843692290457 / 128000000000000) 2 (IntervalRat.scale (5919 / 64) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-42473855633 / 1000000000000) (-42473855632 / 1000000000000), orderedInterval (-51833433404 / 1000000000000) (-51833433403 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 2) <| besselDerivativeNearFromState (20504017459995903 / 128000000000000) 2 (IntervalRat.scale (5919 / 64) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-43018766583 / 1000000000000) (-43018766582 / 1000000000000), orderedInterval (-45948259348 / 1000000000000) (-45948259347 / 1000000000000)))) (orderedInterval (5341768909 / 1000000000000) (5341768940 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 2) <| besselDerivativeNearFromState (17094112106865807 / 128000000000000) 2 (IntervalRat.scale (5919 / 64) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (47378298774 / 1000000000000) (47378347810 / 1000000000000), orderedInterval (-50399696938 / 1000000000000) (-50399647902 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 2) <| besselDerivativeNearFromState (15103166458825947 / 128000000000000) 2 (IntervalRat.scale (5919 / 64) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-41637818797 / 1000000000000) (-41637806149 / 1000000000000), orderedInterval (60688334499 / 1000000000000) (60688347147 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 2) <| besselDerivativeNearFromState (4377486313956753 / 25600000000000) 2 (IntervalRat.scale (5919 / 64) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (51585088932 / 1000000000000) (51585124253 / 1000000000000), orderedInterval (-32739028905 / 1000000000000) (-32738993584 / 1000000000000)))) (orderedInterval (-9460635514 / 1000000000000) (-9460630006 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate206_chunkChecks2_2 :
    compactCertificate206.chunkChecks (2 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 2) <| besselDerivativeNearFromState (12108357518887491 / 128000000000000) 2 (IntervalRat.scale (5919 / 64) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (74292606136 / 1000000000000) (74292606137 / 1000000000000), orderedInterval (34397993789 / 1000000000000) (34397993790 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 2) <| besselDerivativeNearFromState (10264388765148651 / 128000000000000) 2 (IntervalRat.scale (5919 / 64) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-57877165833 / 1000000000000) (-57877125797 / 1000000000000), orderedInterval (68103726566 / 1000000000000) (68103766602 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 2) <| besselDerivativeNearFromState (6422977898378553 / 128000000000000) 2 (IntervalRat.scale (5919 / 64) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (72296290755 / 1000000000000) (72296290756 / 1000000000000), orderedInterval (85652161788 / 1000000000000) (85652161789 / 1000000000000)))) (orderedInterval (9352515382 / 1000000000000) (9352517128 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 2) <| besselDerivativeNearFromState (3454298875607751 / 128000000000000) 2 (IntervalRat.scale (5919 / 64) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (74551098098 / 1000000000000) (74551105526 / 1000000000000), orderedInterval (-135672973046 / 1000000000000) (-135672965618 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 2) <| besselDerivativeNearFromState (9379093404116253 / 128000000000000) 2 (IntervalRat.scale (5919 / 64) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-90745635331 / 1000000000000) (-90745634692 / 1000000000000), orderedInterval (21908555339 / 1000000000000) (21908555977 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 2) <| besselDerivativeNearFromState (12806350199961981 / 128000000000000) 2 (IntervalRat.scale (5919 / 64) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (23785999149 / 1000000000000) (23785999150 / 1000000000000), orderedInterval (76021348141 / 1000000000000) (76021348142 / 1000000000000)))) (orderedInterval (1022771058 / 1000000000000) (1022771090 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 2) <| besselDerivativeNearFromState (5415022101621447 / 128000000000000) 2 (IntervalRat.scale (5919 / 64) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-95705821052 / 1000000000000) (-95705766266 / 1000000000000), orderedInterval (77867884995 / 1000000000000) (77867939781 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 2) <| besselDerivativeNearFromState (22011764210053287 / 128000000000000) 2 (IntervalRat.scale (5919 / 64) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (2190924923 / 1000000000000) (2190924930 / 1000000000000), orderedInterval (-60811020037 / 1000000000000) (-60811020030 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 2) <| besselDerivativeNearFromState (14702838377713833 / 128000000000000) 2 (IntervalRat.scale (5919 / 64) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (41338081436 / 1000000000000) (41338092626 / 1000000000000), orderedInterval (-62094951678 / 1000000000000) (-62094940487 / 1000000000000)))) (orderedInterval (12443411259 / 1000000000000) (12443414653 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate206_chunkChecks2 :
    compactCertificate206.chunkChecks (2 : Fin 5) 0 9 = true :=
  compactCertificate206.chunkChecks_nine_of_three (2 : Fin 5) compactCertificate206_chunkChecks2_0
    compactCertificate206_chunkChecks2_1 compactCertificate206_chunkChecks2_2

theorem compactCertificate206_chunkChecks3_0 :
    compactCertificate206.chunkChecks (3 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 3) <| besselDerivativeNearFromState (5919 / 64) 3 (IntervalRat.scale (5919 / 64) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-68873778697 / 1000000000000) (-68873746790 / 1000000000000), orderedInterval (46631436378 / 1000000000000) (46631468285 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 3) <| besselDerivativeNearFromState (8719817220626019 / 128000000000000) 3 (IntervalRat.scale (5919 / 64) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-19953213777 / 1000000000000) (-19953213596 / 1000000000000), orderedInterval (94735936522 / 1000000000000) (94735936703 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 3) <| besselDerivativeNearFromState (2819809729199427 / 25600000000000) 3 (IntervalRat.scale (5919 / 64) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-63024374948 / 1000000000000) (-63024374947 / 1000000000000), orderedInterval (-42229082286 / 1000000000000) (-42229082285 / 1000000000000)))) (orderedInterval (-14998649377 / 1000000000000) (-14998636585 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 3) <| besselDerivativeNearFromState (2544420917445033 / 128000000000000) 3 (IntervalRat.scale (5919 / 64) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (173925633310 / 1000000000000) (173925633834 / 1000000000000), orderedInterval (-46405139523 / 1000000000000) (-46405138999 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 3) <| besselDerivativeNearFromState (6834672486665301 / 128000000000000) 3 (IntervalRat.scale (5919 / 64) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-76155692756 / 1000000000000) (-76155692755 / 1000000000000), orderedInterval (-77536305525 / 1000000000000) (-77536305524 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 3) <| besselDerivativeNearFromState (18557465334439617 / 128000000000000) 3 (IntervalRat.scale (5919 / 64) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (62915184328 / 1000000000000) (62915184329 / 1000000000000), orderedInterval (20585415181 / 1000000000000) (20585415182 / 1000000000000)))) (orderedInterval (6046628220 / 1000000000000) (6046628248 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 3) <| besselDerivativeNearFromState (13669344973336521 / 128000000000000) 3 (IntervalRat.scale (5919 / 64) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (53293654186 / 1000000000000) (53293654187 / 1000000000000), orderedInterval (55617369303 / 1000000000000) (55617369304 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 3) <| besselDerivativeNearFromState (23422655598333933 / 128000000000000) 3 (IntervalRat.scale (5919 / 64) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (58980539757 / 1000000000000) (58980539810 / 1000000000000), orderedInterval (367224289 / 1000000000000) (367224342 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 3) <| besselDerivativeNearFromState (17253022101621447 / 128000000000000) 3 (IntervalRat.scale (5919 / 64) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-32053379521 / 1000000000000) (-32053379520 / 1000000000000), orderedInterval (-60673163412 / 1000000000000) (-60673163411 / 1000000000000)))) (orderedInterval (4531831453 / 1000000000000) (4531831496 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate206_chunkChecks3_1 :
    compactCertificate206.chunkChecks (3 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 3) <| besselDerivativeNearFromState (26470572717639081 / 128000000000000) 3 (IntervalRat.scale (5919 / 64) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (13243932257 / 1000000000000) (13243932258 / 1000000000000), orderedInterval (53847644390 / 1000000000000) (53847644391 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 3) <| besselDerivativeNearFromState (15282792284130849 / 128000000000000) 3 (IntervalRat.scale (5919 / 64) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (52414147216 / 1000000000000) (52414147217 / 1000000000000), orderedInterval (50620668360 / 1000000000000) (50620668361 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 3) <| besselDerivativeNearFromState (27119583095574741 / 128000000000000) 3 (IntervalRat.scale (5919 / 64) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-45270641927 / 1000000000000) (-45270583747 / 1000000000000), orderedInterval (31014889607 / 1000000000000) (31014947788 / 1000000000000)))) (orderedInterval (45471407999 / 1000000000000) (45471508263 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 3) <| besselDerivativeNearFromState (25338632387680329 / 128000000000000) 3 (IntervalRat.scale (5919 / 64) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-41559024028 / 1000000000000) (-41559024027 / 1000000000000), orderedInterval (-38479733562 / 1000000000000) (-38479733561 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 3) <| besselDerivativeNearFromState (18082843692290457 / 128000000000000) 3 (IntervalRat.scale (5919 / 64) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-42473855633 / 1000000000000) (-42473855632 / 1000000000000), orderedInterval (-51833433404 / 1000000000000) (-51833433403 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 3) <| besselDerivativeNearFromState (20504017459995903 / 128000000000000) 3 (IntervalRat.scale (5919 / 64) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-43018766583 / 1000000000000) (-43018766582 / 1000000000000), orderedInterval (-45948259348 / 1000000000000) (-45948259347 / 1000000000000)))) (orderedInterval (9391102448 / 1000000000000) (9391102499 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 3) <| besselDerivativeNearFromState (17094112106865807 / 128000000000000) 3 (IntervalRat.scale (5919 / 64) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (47378298774 / 1000000000000) (47378347810 / 1000000000000), orderedInterval (-50399696938 / 1000000000000) (-50399647902 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 3) <| besselDerivativeNearFromState (15103166458825947 / 128000000000000) 3 (IntervalRat.scale (5919 / 64) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-41637818797 / 1000000000000) (-41637806149 / 1000000000000), orderedInterval (60688334499 / 1000000000000) (60688347147 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 3) <| besselDerivativeNearFromState (4377486313956753 / 25600000000000) 3 (IntervalRat.scale (5919 / 64) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (51585088932 / 1000000000000) (51585124253 / 1000000000000), orderedInterval (-32739028905 / 1000000000000) (-32738993584 / 1000000000000)))) (orderedInterval (14364271592 / 1000000000000) (14364280605 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate206_chunkChecks3_2 :
    compactCertificate206.chunkChecks (3 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 3) <| besselDerivativeNearFromState (12108357518887491 / 128000000000000) 3 (IntervalRat.scale (5919 / 64) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (74292606136 / 1000000000000) (74292606137 / 1000000000000), orderedInterval (34397993789 / 1000000000000) (34397993790 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 3) <| besselDerivativeNearFromState (10264388765148651 / 128000000000000) 3 (IntervalRat.scale (5919 / 64) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-57877165833 / 1000000000000) (-57877125797 / 1000000000000), orderedInterval (68103726566 / 1000000000000) (68103766602 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 3) <| besselDerivativeNearFromState (6422977898378553 / 128000000000000) 3 (IntervalRat.scale (5919 / 64) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (72296290755 / 1000000000000) (72296290756 / 1000000000000), orderedInterval (85652161788 / 1000000000000) (85652161789 / 1000000000000)))) (orderedInterval (7850859202 / 1000000000000) (7850860718 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 3) <| besselDerivativeNearFromState (3454298875607751 / 128000000000000) 3 (IntervalRat.scale (5919 / 64) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (74551098098 / 1000000000000) (74551105526 / 1000000000000), orderedInterval (-135672973046 / 1000000000000) (-135672965618 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 3) <| besselDerivativeNearFromState (9379093404116253 / 128000000000000) 3 (IntervalRat.scale (5919 / 64) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-90745635331 / 1000000000000) (-90745634692 / 1000000000000), orderedInterval (21908555339 / 1000000000000) (21908555977 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 3) <| besselDerivativeNearFromState (12806350199961981 / 128000000000000) 3 (IntervalRat.scale (5919 / 64) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (23785999149 / 1000000000000) (23785999150 / 1000000000000), orderedInterval (76021348141 / 1000000000000) (76021348142 / 1000000000000)))) (orderedInterval (7549276150 / 1000000000000) (7549276172 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 3) <| besselDerivativeNearFromState (5415022101621447 / 128000000000000) 3 (IntervalRat.scale (5919 / 64) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-95705821052 / 1000000000000) (-95705766266 / 1000000000000), orderedInterval (77867884995 / 1000000000000) (77867939781 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 3) <| besselDerivativeNearFromState (22011764210053287 / 128000000000000) 3 (IntervalRat.scale (5919 / 64) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (2190924923 / 1000000000000) (2190924930 / 1000000000000), orderedInterval (-60811020037 / 1000000000000) (-60811020030 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 3) <| besselDerivativeNearFromState (14702838377713833 / 128000000000000) 3 (IntervalRat.scale (5919 / 64) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (41338081436 / 1000000000000) (41338092626 / 1000000000000), orderedInterval (-62094951678 / 1000000000000) (-62094940487 / 1000000000000)))) (orderedInterval (-54321298021 / 1000000000000) (-54321293845 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate206_chunkChecks3 :
    compactCertificate206.chunkChecks (3 : Fin 5) 0 9 = true :=
  compactCertificate206.chunkChecks_nine_of_three (3 : Fin 5) compactCertificate206_chunkChecks3_0
    compactCertificate206_chunkChecks3_1 compactCertificate206_chunkChecks3_2

theorem compactCertificate206_chunkChecks4_0 :
    compactCertificate206.chunkChecks (4 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 4) <| besselDerivativeNearFromState (5919 / 64) 4 (IntervalRat.scale (5919 / 64) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-68873778697 / 1000000000000) (-68873746790 / 1000000000000), orderedInterval (46631436378 / 1000000000000) (46631468285 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 4) <| besselDerivativeNearFromState (8719817220626019 / 128000000000000) 4 (IntervalRat.scale (5919 / 64) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-19953213777 / 1000000000000) (-19953213596 / 1000000000000), orderedInterval (94735936522 / 1000000000000) (94735936703 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 4) <| besselDerivativeNearFromState (2819809729199427 / 25600000000000) 4 (IntervalRat.scale (5919 / 64) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-63024374948 / 1000000000000) (-63024374947 / 1000000000000), orderedInterval (-42229082286 / 1000000000000) (-42229082285 / 1000000000000)))) (orderedInterval (-34467134444 / 1000000000000) (-34467121515 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 4) <| besselDerivativeNearFromState (2544420917445033 / 128000000000000) 4 (IntervalRat.scale (5919 / 64) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (173925633310 / 1000000000000) (173925633834 / 1000000000000), orderedInterval (-46405139523 / 1000000000000) (-46405138999 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 4) <| besselDerivativeNearFromState (6834672486665301 / 128000000000000) 4 (IntervalRat.scale (5919 / 64) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-76155692756 / 1000000000000) (-76155692755 / 1000000000000), orderedInterval (-77536305525 / 1000000000000) (-77536305524 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 4) <| besselDerivativeNearFromState (18557465334439617 / 128000000000000) 4 (IntervalRat.scale (5919 / 64) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (62915184328 / 1000000000000) (62915184329 / 1000000000000), orderedInterval (20585415181 / 1000000000000) (20585415182 / 1000000000000)))) (orderedInterval (-27452233750 / 1000000000000) (-27452233708 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 4) <| besselDerivativeNearFromState (13669344973336521 / 128000000000000) 4 (IntervalRat.scale (5919 / 64) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (53293654186 / 1000000000000) (53293654187 / 1000000000000), orderedInterval (55617369303 / 1000000000000) (55617369304 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 4) <| besselDerivativeNearFromState (23422655598333933 / 128000000000000) 4 (IntervalRat.scale (5919 / 64) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (58980539757 / 1000000000000) (58980539810 / 1000000000000), orderedInterval (367224289 / 1000000000000) (367224342 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 4) <| besselDerivativeNearFromState (17253022101621447 / 128000000000000) 4 (IntervalRat.scale (5919 / 64) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-32053379521 / 1000000000000) (-32053379520 / 1000000000000), orderedInterval (-60673163412 / 1000000000000) (-60673163411 / 1000000000000)))) (orderedInterval (-31473241325 / 1000000000000) (-31473241244 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate206_chunkChecks4_1 :
    compactCertificate206.chunkChecks (4 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 4) <| besselDerivativeNearFromState (26470572717639081 / 128000000000000) 4 (IntervalRat.scale (5919 / 64) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (13243932257 / 1000000000000) (13243932258 / 1000000000000), orderedInterval (53847644390 / 1000000000000) (53847644391 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 4) <| besselDerivativeNearFromState (15282792284130849 / 128000000000000) 4 (IntervalRat.scale (5919 / 64) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (52414147216 / 1000000000000) (52414147217 / 1000000000000), orderedInterval (50620668360 / 1000000000000) (50620668361 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 4) <| besselDerivativeNearFromState (27119583095574741 / 128000000000000) 4 (IntervalRat.scale (5919 / 64) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-45270641927 / 1000000000000) (-45270583747 / 1000000000000), orderedInterval (31014889607 / 1000000000000) (31014947788 / 1000000000000)))) (orderedInterval (-226279241526 / 1000000000000) (-226279010791 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 4) <| besselDerivativeNearFromState (25338632387680329 / 128000000000000) 4 (IntervalRat.scale (5919 / 64) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-41559024028 / 1000000000000) (-41559024027 / 1000000000000), orderedInterval (-38479733562 / 1000000000000) (-38479733561 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 4) <| besselDerivativeNearFromState (18082843692290457 / 128000000000000) 4 (IntervalRat.scale (5919 / 64) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-42473855633 / 1000000000000) (-42473855632 / 1000000000000), orderedInterval (-51833433404 / 1000000000000) (-51833433403 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 4) <| besselDerivativeNearFromState (20504017459995903 / 128000000000000) 4 (IntervalRat.scale (5919 / 64) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-43018766583 / 1000000000000) (-43018766582 / 1000000000000), orderedInterval (-45948259348 / 1000000000000) (-45948259347 / 1000000000000)))) (orderedInterval (-4362103313 / 1000000000000) (-4362103224 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 4) <| besselDerivativeNearFromState (17094112106865807 / 128000000000000) 4 (IntervalRat.scale (5919 / 64) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (47378298774 / 1000000000000) (47378347810 / 1000000000000), orderedInterval (-50399696938 / 1000000000000) (-50399647902 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 4) <| besselDerivativeNearFromState (15103166458825947 / 128000000000000) 4 (IntervalRat.scale (5919 / 64) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-41637818797 / 1000000000000) (-41637806149 / 1000000000000), orderedInterval (60688334499 / 1000000000000) (60688347147 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 4) <| besselDerivativeNearFromState (4377486313956753 / 25600000000000) 4 (IntervalRat.scale (5919 / 64) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (51585088932 / 1000000000000) (51585124253 / 1000000000000), orderedInterval (-32739028905 / 1000000000000) (-32738993584 / 1000000000000)))) (orderedInterval (23814802350 / 1000000000000) (23814817537 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate206_chunkChecks4_2 :
    compactCertificate206.chunkChecks (4 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 4) <| besselDerivativeNearFromState (12108357518887491 / 128000000000000) 4 (IntervalRat.scale (5919 / 64) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (74292606136 / 1000000000000) (74292606137 / 1000000000000), orderedInterval (34397993789 / 1000000000000) (34397993790 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 4) <| besselDerivativeNearFromState (10264388765148651 / 128000000000000) 4 (IntervalRat.scale (5919 / 64) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-57877165833 / 1000000000000) (-57877125797 / 1000000000000), orderedInterval (68103726566 / 1000000000000) (68103766602 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 4) <| besselDerivativeNearFromState (6422977898378553 / 128000000000000) 4 (IntervalRat.scale (5919 / 64) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (72296290755 / 1000000000000) (72296290756 / 1000000000000), orderedInterval (85652161788 / 1000000000000) (85652161789 / 1000000000000)))) (orderedInterval (-11114853880 / 1000000000000) (-11114852548 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 4) <| besselDerivativeNearFromState (3454298875607751 / 128000000000000) 4 (IntervalRat.scale (5919 / 64) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (74551098098 / 1000000000000) (74551105526 / 1000000000000), orderedInterval (-135672973046 / 1000000000000) (-135672965618 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 4) <| besselDerivativeNearFromState (9379093404116253 / 128000000000000) 4 (IntervalRat.scale (5919 / 64) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-90745635331 / 1000000000000) (-90745634692 / 1000000000000), orderedInterval (21908555339 / 1000000000000) (21908555977 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 4) <| besselDerivativeNearFromState (12806350199961981 / 128000000000000) 4 (IntervalRat.scale (5919 / 64) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (23785999149 / 1000000000000) (23785999150 / 1000000000000), orderedInterval (76021348141 / 1000000000000) (76021348142 / 1000000000000)))) (orderedInterval (-1858559385 / 1000000000000) (-1858559367 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 4) <| besselDerivativeNearFromState (5415022101621447 / 128000000000000) 4 (IntervalRat.scale (5919 / 64) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-95705821052 / 1000000000000) (-95705766266 / 1000000000000), orderedInterval (77867884995 / 1000000000000) (77867939781 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 4) <| besselDerivativeNearFromState (22011764210053287 / 128000000000000) 4 (IntervalRat.scale (5919 / 64) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (2190924923 / 1000000000000) (2190924930 / 1000000000000), orderedInterval (-60811020037 / 1000000000000) (-60811020030 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 4) <| besselDerivativeNearFromState (14702838377713833 / 128000000000000) 4 (IntervalRat.scale (5919 / 64) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (41338081436 / 1000000000000) (41338092626 / 1000000000000), orderedInterval (-62094951678 / 1000000000000) (-62094940487 / 1000000000000)))) (orderedInterval (-19436960518 / 1000000000000) (-19436955282 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate206_chunkChecks4 :
    compactCertificate206.chunkChecks (4 : Fin 5) 0 9 = true :=
  compactCertificate206.chunkChecks_nine_of_three (4 : Fin 5) compactCertificate206_chunkChecks4_0
    compactCertificate206_chunkChecks4_1 compactCertificate206_chunkChecks4_2

theorem compactCertificate206_chunks :
    ∀ r : Fin 5, ∀ b, compactCertificate206.chunkCheck r b = true :=
  compactCertificate206.chunkChecks_all (by
    intro r
    fin_cases r
    · exact compactCertificate206_chunkChecks0
    · exact compactCertificate206_chunkChecks1
    · exact compactCertificate206_chunkChecks2
    · exact compactCertificate206_chunkChecks3
    · exact compactCertificate206_chunkChecks4)

theorem compactCertificate206_coefficient0 :
    compactCertificate206.coefficientCheck (0 : Fin 5) = true := by
  norm_num [CompactCertificate.coefficientCheck, intervalFinSumHull,
    compactCertificate206, rationalIntervalSubset, orderedInterval, Fin.sum_univ_succ]

theorem compactCertificate206_coefficient1 :
    compactCertificate206.coefficientCheck (1 : Fin 5) = true := by
  norm_num [CompactCertificate.coefficientCheck, intervalFinSumHull,
    compactCertificate206, rationalIntervalSubset, orderedInterval, Fin.sum_univ_succ]

theorem compactCertificate206_coefficient2 :
    compactCertificate206.coefficientCheck (2 : Fin 5) = true := by
  norm_num [CompactCertificate.coefficientCheck, intervalFinSumHull,
    compactCertificate206, rationalIntervalSubset, orderedInterval, Fin.sum_univ_succ]

theorem compactCertificate206_coefficient3 :
    compactCertificate206.coefficientCheck (3 : Fin 5) = true := by
  norm_num [CompactCertificate.coefficientCheck, intervalFinSumHull,
    compactCertificate206, rationalIntervalSubset, orderedInterval, Fin.sum_univ_succ]

theorem compactCertificate206_coefficient4 :
    compactCertificate206.coefficientCheck (4 : Fin 5) = true := by
  norm_num [CompactCertificate.coefficientCheck, intervalFinSumHull,
    compactCertificate206, rationalIntervalSubset, orderedInterval, Fin.sum_univ_succ]

theorem compactCertificate206_coefficients : ∀ r : Fin 5,
    compactCertificate206.coefficientCheck r = true := by
  intro r
  fin_cases r
  · exact compactCertificate206_coefficient0
  · exact compactCertificate206_coefficient1
  · exact compactCertificate206_coefficient2
  · exact compactCertificate206_coefficient3
  · exact compactCertificate206_coefficient4

theorem compactCertificate206_lower : (1 : ℚ) ≤ compactCertificate206.output.lo := by
  norm_num [CompactCertificate.output, CompactCertificate.interval,
    CompactCertificate.coefficientTargetNat, compactCertificate206, dualConstant,
    intervalTaylorSum, intervalPow, intervalSub, intervalMaxAbs, widenInterval,
    rationalErrorInterval, orderedInterval, IntervalRat.add, IntervalRat.mul, IntervalRat.scale,
    IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4]

theorem compactCertificate206_proves {t : ℝ} (ht : t ∈ compactCertificate206.interval) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t :=
  compactCertificate206.proves compactCertificate206_states compactCertificate206_chunks
    compactCertificate206_coefficients compactCertificate206_lower ht

end Erdos232
