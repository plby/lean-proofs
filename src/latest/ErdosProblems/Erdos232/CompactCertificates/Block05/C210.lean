/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, OpenAI Codex
-/
import ErdosProblems.Erdos232.CompactBase

open LeanCert.Core
namespace Erdos232

def compactCertificate210 : CompactCertificate where
  left := 741 / 8
  right := 371 / 4
  center := 1483 / 16
  grid := fun i =>
    match i.val with
    | 0 => 30
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
    | 17 => 55
    | 18 => 30
    | 19 => 26
    | 20 => 16
    | 21 => 9
    | 22 => 23
    | 23 => 32
    | 24 => 14
    | 25 => 55
    | _ => 37
  point := fun i =>
    match i.val with
    | 0 => 1483 / 16
    | 1 => 2184742175737183 / 32000000000000
    | 2 => 706500731272639 / 6400000000000
    | 3 => 637502318055581 / 32000000000000
    | 4 => 1712420898416057 / 32000000000000
    | 5 => 4649555852504469 / 32000000000000
    | 6 => 3424841796833597 / 32000000000000
    | 7 => 5868524793432881 / 32000000000000
    | 8 => 4322728801605779 / 32000000000000
    | 9 => 6632177621263517 / 32000000000000
    | 10 => 3829089534949493 / 32000000000000
    | 11 => 6794786573870137 / 32000000000000
    | 12 => 6348571013841853 / 32000000000000
    | 13 => 4530639837078349 / 32000000000000
    | 14 => 5137262695248171 / 32000000000000
    | 15 => 4282914048738299 / 32000000000000
    | 16 => 3784084449812279 / 32000000000000
    | 17 => 1096775165331621 / 6400000000000
    | 18 => 3033737827421887 / 32000000000000
    | 19 => 2571733154032007 / 32000000000000
    | 20 => 1609271198394221 / 32000000000000
    | 21 => 865471402690707 / 32000000000000
    | 22 => 2349923216473121 / 32000000000000
    | 23 => 3208619250978817 / 32000000000000
    | 24 => 1356728801605779 / 32000000000000
    | 25 => 5515027255196659 / 32000000000000
    | _ => 3683782617697181 / 32000000000000
  state := fun i =>
    match i.val with
    | 0 => (orderedInterval (-58062153990 / 1000000000000) (-58062084360 / 1000000000000), orderedInterval (59450680215 / 1000000000000) (59450749845 / 1000000000000))
    | 1 => (orderedInterval (-5624282922 / 1000000000000) (-5624282901 / 1000000000000), orderedInterval (96442480003 / 1000000000000) (96442480024 / 1000000000000))
    | 2 => (orderedInterval (-71296084361 / 1000000000000) (-71296084360 / 1000000000000), orderedInterval (-25826467456 / 1000000000000) (-25826467455 / 1000000000000))
    | 3 => (orderedInterval (171736881362 / 1000000000000) (171736882257 / 1000000000000), orderedInterval (-53841980700 / 1000000000000) (-53841979805 / 1000000000000))
    | 4 => (orderedInterval (-84695217591 / 1000000000000) (-84695217590 / 1000000000000), orderedInterval (-67933703535 / 1000000000000) (-67933703534 / 1000000000000))
    | 5 => (orderedInterval (66192358307 / 1000000000000) (66192358352 / 1000000000000), orderedInterval (-168196712 / 1000000000000) (-168196666 / 1000000000000))
    | 6 => (orderedInterval (64747026151 / 1000000000000) (64747026152 / 1000000000000), orderedInterval (41602788549 / 1000000000000) (41602788550 / 1000000000000))
    | 7 => (orderedInterval (54427781165 / 1000000000000) (54427788451 / 1000000000000), orderedInterval (-22708960355 / 1000000000000) (-22708953069 / 1000000000000))
    | 8 => (orderedInterval (-48341107169 / 1000000000000) (-48341107168 / 1000000000000), orderedInterval (-48563897081 / 1000000000000) (-48563897080 / 1000000000000))
    | 9 => (orderedInterval (35501595190 / 1000000000000) (35501595191 / 1000000000000), orderedInterval (42473771727 / 1000000000000) (42473771728 / 1000000000000))
    | 10 => (orderedInterval (63732012083 / 1000000000000) (63732012084 / 1000000000000), orderedInterval (35208862136 / 1000000000000) (35208862137 / 1000000000000))
    | 11 => (orderedInterval (-26558612592 / 1000000000000) (-26558609739 / 1000000000000), orderedInterval (47945738107 / 1000000000000) (47945740960 / 1000000000000))
    | 12 => (orderedInterval (-53885588989 / 1000000000000) (-53885588988 / 1000000000000), orderedInterval (-17334736460 / 1000000000000) (-17334736458 / 1000000000000))
    | 13 => (orderedInterval (-56255780128 / 1000000000000) (-56255780127 / 1000000000000), orderedInterval (-36294265288 / 1000000000000) (-36294265287 / 1000000000000))
    | 14 => (orderedInterval (-56202467480 / 1000000000000) (-56202467479 / 1000000000000), orderedInterval (-28228737942 / 1000000000000) (-28228737941 / 1000000000000))
    | 15 => (orderedInterval (30800477237 / 1000000000000) (30800479968 / 1000000000000), orderedInterval (-61823133821 / 1000000000000) (-61823131090 / 1000000000000))
    | 16 => (orderedInterval (-24713506830 / 1000000000000) (-24713506080 / 1000000000000), orderedInterval (69190209830 / 1000000000000) (69190210581 / 1000000000000))
    | 17 => (orderedInterval (35997049490 / 1000000000000) (35997062435 / 1000000000000), orderedInterval (-49289145668 / 1000000000000) (-49289132723 / 1000000000000))
    | 18 => (orderedInterval (79783659456 / 1000000000000) (79783659458 / 1000000000000), orderedInterval (18276219544 / 1000000000000) (18276219545 / 1000000000000))
    | 19 => (orderedInterval (-45062766888 / 1000000000000) (-45062759456 / 1000000000000), orderedInterval (77032301120 / 1000000000000) (77032308551 / 1000000000000))
    | 20 => (orderedInterval (81268297069 / 1000000000000) (81268297070 / 1000000000000), orderedInterval (77002613676 / 1000000000000) (77002613677 / 1000000000000))
    | 21 => (orderedInterval (66392279260 / 1000000000000) (66392283258 / 1000000000000), orderedInterval (-139549065663 / 1000000000000) (-139549061666 / 1000000000000))
    | 22 => (orderedInterval (-86067126596 / 1000000000000) (-86067122552 / 1000000000000), orderedInterval (36102958720 / 1000000000000) (36102962764 / 1000000000000))
    | 23 => (orderedInterval (39767157285 / 1000000000000) (39767157286 / 1000000000000), orderedInterval (68850303119 / 1000000000000) (68850303120 / 1000000000000))
    | 24 => (orderedInterval (-88076560362 / 1000000000000) (-88076454334 / 1000000000000), orderedInterval (86231791999 / 1000000000000) (86231898027 / 1000000000000))
    | 25 => (orderedInterval (-20364549122 / 1000000000000) (-20364549121 / 1000000000000), orderedInterval (-57204994395 / 1000000000000) (-57204994394 / 1000000000000))
    | _ => (orderedInterval (24547705572 / 1000000000000) (24547706274 / 1000000000000), orderedInterval (-70303417538 / 1000000000000) (-70303416837 / 1000000000000))
  chunkTarget := fun r b =>
    match r.val with
    | 0 =>
      match b.val with
      | 0 => orderedInterval (-27249948177 / 1000000000000) (-27249920571 / 1000000000000)
      | 1 => orderedInterval (-9661184681 / 1000000000000) (-9661184656 / 1000000000000)
      | 2 => orderedInterval (-2847079948 / 1000000000000) (-2847079717 / 1000000000000)
      | 3 => orderedInterval (-5361650457 / 1000000000000) (-5361650013 / 1000000000000)
      | 4 => orderedInterval (-4062489774 / 1000000000000) (-4062489762 / 1000000000000)
      | 5 => orderedInterval (2691612227 / 1000000000000) (2691612643 / 1000000000000)
      | 6 => orderedInterval (-7560542517 / 1000000000000) (-7560542072 / 1000000000000)
      | 7 => orderedInterval (-2321058350 / 1000000000000) (-2321058172 / 1000000000000)
      | _ => orderedInterval (-3479044796 / 1000000000000) (-3479043999 / 1000000000000)
    | 1 =>
      match b.val with
      | 0 => orderedInterval (22421124059 / 1000000000000) (22421151667 / 1000000000000)
      | 1 => orderedInterval (-1287748204 / 1000000000000) (-1287748183 / 1000000000000)
      | 2 => orderedInterval (-324692867 / 1000000000000) (-324692413 / 1000000000000)
      | 3 => orderedInterval (2106217588 / 1000000000000) (2106218594 / 1000000000000)
      | 4 => orderedInterval (-4325330090 / 1000000000000) (-4325330071 / 1000000000000)
      | 5 => orderedInterval (-8415860642 / 1000000000000) (-8415859915 / 1000000000000)
      | 6 => orderedInterval (-5409275936 / 1000000000000) (-5409275549 / 1000000000000)
      | 7 => orderedInterval (-5605268974 / 1000000000000) (-5605268869 / 1000000000000)
      | _ => orderedInterval (25279322938 / 1000000000000) (25279323431 / 1000000000000)
    | 2 =>
      match b.val with
      | 0 => orderedInterval (28734853456 / 1000000000000) (28734881362 / 1000000000000)
      | 1 => orderedInterval (12694407187 / 1000000000000) (12694407214 / 1000000000000)
      | 2 => orderedInterval (9057243254 / 1000000000000) (9057244156 / 1000000000000)
      | 3 => orderedInterval (43462607898 / 1000000000000) (43462610201 / 1000000000000)
      | 4 => orderedInterval (7149157787 / 1000000000000) (7149157818 / 1000000000000)
      | 5 => orderedInterval (-6103569560 / 1000000000000) (-6103568264 / 1000000000000)
      | 6 => orderedInterval (10708106320 / 1000000000000) (10708106662 / 1000000000000)
      | 7 => orderedInterval (2505888843 / 1000000000000) (2505888919 / 1000000000000)
      | _ => orderedInterval (1211729565 / 1000000000000) (1211729961 / 1000000000000)
    | 3 =>
      match b.val with
      | 0 => orderedInterval (-21670417461 / 1000000000000) (-21670389560 / 1000000000000)
      | 1 => orderedInterval (288377307 / 1000000000000) (288377347 / 1000000000000)
      | 2 => orderedInterval (-1889858567 / 1000000000000) (-1889856786 / 1000000000000)
      | 3 => orderedInterval (-3649010656 / 1000000000000) (-3649005396 / 1000000000000)
      | 4 => orderedInterval (8343913849 / 1000000000000) (8343913901 / 1000000000000)
      | 5 => orderedInterval (18413502293 / 1000000000000) (18413504616 / 1000000000000)
      | 6 => orderedInterval (5452676881 / 1000000000000) (5452677179 / 1000000000000)
      | 7 => orderedInterval (6995939218 / 1000000000000) (6995939277 / 1000000000000)
      | _ => orderedInterval (-55268111162 / 1000000000000) (-55268110762 / 1000000000000)
    | _ =>
      match b.val with
      | 0 => orderedInterval (-30976338613 / 1000000000000) (-30976310416 / 1000000000000)
      | 1 => orderedInterval (-28769135850 / 1000000000000) (-28769135789 / 1000000000000)
      | 2 => orderedInterval (-30958294572 / 1000000000000) (-30958291036 / 1000000000000)
      | 3 => orderedInterval (-248493979674 / 1000000000000) (-248493967598 / 1000000000000)
      | 4 => orderedInterval (-6162887156 / 1000000000000) (-6162887067 / 1000000000000)
      | 5 => orderedInterval (15666049813 / 1000000000000) (15666054033 / 1000000000000)
      | 6 => orderedInterval (-12408195052 / 1000000000000) (-12408194788 / 1000000000000)
      | 7 => orderedInterval (-3564254877 / 1000000000000) (-3564254828 / 1000000000000)
      | _ => orderedInterval (10025728945 / 1000000000000) (10025729427 / 1000000000000)
  coefficientTarget := fun i =>
    match i.val with
    | 0 => orderedInterval (-59851386473 / 1000000000000) (-59851356319 / 1000000000000)
    | 1 => orderedInterval (24438487872 / 1000000000000) (24438518692 / 1000000000000)
    | 2 => orderedInterval (109420424750 / 1000000000000) (109420458029 / 1000000000000)
    | 3 => orderedInterval (-42982988298 / 1000000000000) (-42982950184 / 1000000000000)
    | _ => orderedInterval (-335641307036 / 1000000000000) (-335641258062 / 1000000000000)

theorem compactCertificate210_stateChecks0 :
    compactCertificate210.stateChecks 0 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 30 12 (1483 / 16)) (orderedInterval (-58062153990 / 1000000000000) (-58062084360 / 1000000000000), orderedInterval (59450680215 / 1000000000000) (59450749845 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 22 12 (2184742175737183 / 32000000000000)) (orderedInterval (-5624282922 / 1000000000000) (-5624282901 / 1000000000000), orderedInterval (96442480003 / 1000000000000) (96442480024 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 35 12 (706500731272639 / 6400000000000)) (orderedInterval (-71296084361 / 1000000000000) (-71296084360 / 1000000000000), orderedInterval (-25826467456 / 1000000000000) (-25826467455 / 1000000000000))) = true
  norm_num [besselStateAtRationalPoint, besselIntervalStepZero,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, besselZeroTransition,
    besselInitial, besselGridStateAt, besselGridStateBlock00, besselGridStateBlock01,
    besselGridStateBlock02, besselGridStateBlock03, besselGridStateBlock04,
    besselGridStateBlock05, besselGridStateBlock06, besselGridStateBlock07,
    besselGridStateBlock08, besselGridStateBlock09, besselGridStateBlock10,
    besselGridStateBlock11, besselGridStateBlock12, besselGridStateBlock13,
    besselGridStateBlock14, besselGridState006, besselGridState009, besselGridState014, besselGridState016, besselGridState017, besselGridState022, besselGridState023, besselGridState026, besselGridState030, besselGridState032, besselGridState034, besselGridState035, besselGridState037, besselGridState038, besselGridState043, besselGridState045, besselGridState046, besselGridState051, besselGridState055, besselGridState058, besselGridState063, besselGridState066, besselGridState068, besselStateSubset, linearInterval, widenInterval,
    rationalErrorInterval, rationalIntervalSubset, orderedInterval, Finset.sum_range_succ,
    IntervalRat.add, IntervalRat.mul, IntervalRat.scale, IntervalRat.singleton]

theorem compactCertificate210_stateChecks1 :
    compactCertificate210.stateChecks 3 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 6 12 (637502318055581 / 32000000000000)) (orderedInterval (171736881362 / 1000000000000) (171736882257 / 1000000000000), orderedInterval (-53841980700 / 1000000000000) (-53841979805 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 17 12 (1712420898416057 / 32000000000000)) (orderedInterval (-84695217591 / 1000000000000) (-84695217590 / 1000000000000), orderedInterval (-67933703535 / 1000000000000) (-67933703534 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 46 12 (4649555852504469 / 32000000000000)) (orderedInterval (66192358307 / 1000000000000) (66192358352 / 1000000000000), orderedInterval (-168196712 / 1000000000000) (-168196666 / 1000000000000))) = true
  norm_num [besselStateAtRationalPoint, besselIntervalStepZero,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, besselZeroTransition,
    besselInitial, besselGridStateAt, besselGridStateBlock00, besselGridStateBlock01,
    besselGridStateBlock02, besselGridStateBlock03, besselGridStateBlock04,
    besselGridStateBlock05, besselGridStateBlock06, besselGridStateBlock07,
    besselGridStateBlock08, besselGridStateBlock09, besselGridStateBlock10,
    besselGridStateBlock11, besselGridStateBlock12, besselGridStateBlock13,
    besselGridStateBlock14, besselGridState006, besselGridState009, besselGridState014, besselGridState016, besselGridState017, besselGridState022, besselGridState023, besselGridState026, besselGridState030, besselGridState032, besselGridState034, besselGridState035, besselGridState037, besselGridState038, besselGridState043, besselGridState045, besselGridState046, besselGridState051, besselGridState055, besselGridState058, besselGridState063, besselGridState066, besselGridState068, besselStateSubset, linearInterval, widenInterval,
    rationalErrorInterval, rationalIntervalSubset, orderedInterval, Finset.sum_range_succ,
    IntervalRat.add, IntervalRat.mul, IntervalRat.scale, IntervalRat.singleton]

theorem compactCertificate210_stateChecks2 :
    compactCertificate210.stateChecks 6 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 34 12 (3424841796833597 / 32000000000000)) (orderedInterval (64747026151 / 1000000000000) (64747026152 / 1000000000000), orderedInterval (41602788549 / 1000000000000) (41602788550 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 58 12 (5868524793432881 / 32000000000000)) (orderedInterval (54427781165 / 1000000000000) (54427788451 / 1000000000000), orderedInterval (-22708960355 / 1000000000000) (-22708953069 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 43 12 (4322728801605779 / 32000000000000)) (orderedInterval (-48341107169 / 1000000000000) (-48341107168 / 1000000000000), orderedInterval (-48563897081 / 1000000000000) (-48563897080 / 1000000000000))) = true
  norm_num [besselStateAtRationalPoint, besselIntervalStepZero,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, besselZeroTransition,
    besselInitial, besselGridStateAt, besselGridStateBlock00, besselGridStateBlock01,
    besselGridStateBlock02, besselGridStateBlock03, besselGridStateBlock04,
    besselGridStateBlock05, besselGridStateBlock06, besselGridStateBlock07,
    besselGridStateBlock08, besselGridStateBlock09, besselGridStateBlock10,
    besselGridStateBlock11, besselGridStateBlock12, besselGridStateBlock13,
    besselGridStateBlock14, besselGridState006, besselGridState009, besselGridState014, besselGridState016, besselGridState017, besselGridState022, besselGridState023, besselGridState026, besselGridState030, besselGridState032, besselGridState034, besselGridState035, besselGridState037, besselGridState038, besselGridState043, besselGridState045, besselGridState046, besselGridState051, besselGridState055, besselGridState058, besselGridState063, besselGridState066, besselGridState068, besselStateSubset, linearInterval, widenInterval,
    rationalErrorInterval, rationalIntervalSubset, orderedInterval, Finset.sum_range_succ,
    IntervalRat.add, IntervalRat.mul, IntervalRat.scale, IntervalRat.singleton]

theorem compactCertificate210_stateChecks3 :
    compactCertificate210.stateChecks 9 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 66 12 (6632177621263517 / 32000000000000)) (orderedInterval (35501595190 / 1000000000000) (35501595191 / 1000000000000), orderedInterval (42473771727 / 1000000000000) (42473771728 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 38 12 (3829089534949493 / 32000000000000)) (orderedInterval (63732012083 / 1000000000000) (63732012084 / 1000000000000), orderedInterval (35208862136 / 1000000000000) (35208862137 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 68 12 (6794786573870137 / 32000000000000)) (orderedInterval (-26558612592 / 1000000000000) (-26558609739 / 1000000000000), orderedInterval (47945738107 / 1000000000000) (47945740960 / 1000000000000))) = true
  norm_num [besselStateAtRationalPoint, besselIntervalStepZero,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, besselZeroTransition,
    besselInitial, besselGridStateAt, besselGridStateBlock00, besselGridStateBlock01,
    besselGridStateBlock02, besselGridStateBlock03, besselGridStateBlock04,
    besselGridStateBlock05, besselGridStateBlock06, besselGridStateBlock07,
    besselGridStateBlock08, besselGridStateBlock09, besselGridStateBlock10,
    besselGridStateBlock11, besselGridStateBlock12, besselGridStateBlock13,
    besselGridStateBlock14, besselGridState006, besselGridState009, besselGridState014, besselGridState016, besselGridState017, besselGridState022, besselGridState023, besselGridState026, besselGridState030, besselGridState032, besselGridState034, besselGridState035, besselGridState037, besselGridState038, besselGridState043, besselGridState045, besselGridState046, besselGridState051, besselGridState055, besselGridState058, besselGridState063, besselGridState066, besselGridState068, besselStateSubset, linearInterval, widenInterval,
    rationalErrorInterval, rationalIntervalSubset, orderedInterval, Finset.sum_range_succ,
    IntervalRat.add, IntervalRat.mul, IntervalRat.scale, IntervalRat.singleton]

theorem compactCertificate210_stateChecks4 :
    compactCertificate210.stateChecks 12 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 63 12 (6348571013841853 / 32000000000000)) (orderedInterval (-53885588989 / 1000000000000) (-53885588988 / 1000000000000), orderedInterval (-17334736460 / 1000000000000) (-17334736458 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 45 12 (4530639837078349 / 32000000000000)) (orderedInterval (-56255780128 / 1000000000000) (-56255780127 / 1000000000000), orderedInterval (-36294265288 / 1000000000000) (-36294265287 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 51 12 (5137262695248171 / 32000000000000)) (orderedInterval (-56202467480 / 1000000000000) (-56202467479 / 1000000000000), orderedInterval (-28228737942 / 1000000000000) (-28228737941 / 1000000000000))) = true
  norm_num [besselStateAtRationalPoint, besselIntervalStepZero,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, besselZeroTransition,
    besselInitial, besselGridStateAt, besselGridStateBlock00, besselGridStateBlock01,
    besselGridStateBlock02, besselGridStateBlock03, besselGridStateBlock04,
    besselGridStateBlock05, besselGridStateBlock06, besselGridStateBlock07,
    besselGridStateBlock08, besselGridStateBlock09, besselGridStateBlock10,
    besselGridStateBlock11, besselGridStateBlock12, besselGridStateBlock13,
    besselGridStateBlock14, besselGridState006, besselGridState009, besselGridState014, besselGridState016, besselGridState017, besselGridState022, besselGridState023, besselGridState026, besselGridState030, besselGridState032, besselGridState034, besselGridState035, besselGridState037, besselGridState038, besselGridState043, besselGridState045, besselGridState046, besselGridState051, besselGridState055, besselGridState058, besselGridState063, besselGridState066, besselGridState068, besselStateSubset, linearInterval, widenInterval,
    rationalErrorInterval, rationalIntervalSubset, orderedInterval, Finset.sum_range_succ,
    IntervalRat.add, IntervalRat.mul, IntervalRat.scale, IntervalRat.singleton]

theorem compactCertificate210_stateChecks5 :
    compactCertificate210.stateChecks 15 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 43 12 (4282914048738299 / 32000000000000)) (orderedInterval (30800477237 / 1000000000000) (30800479968 / 1000000000000), orderedInterval (-61823133821 / 1000000000000) (-61823131090 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 38 12 (3784084449812279 / 32000000000000)) (orderedInterval (-24713506830 / 1000000000000) (-24713506080 / 1000000000000), orderedInterval (69190209830 / 1000000000000) (69190210581 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 55 12 (1096775165331621 / 6400000000000)) (orderedInterval (35997049490 / 1000000000000) (35997062435 / 1000000000000), orderedInterval (-49289145668 / 1000000000000) (-49289132723 / 1000000000000))) = true
  norm_num [besselStateAtRationalPoint, besselIntervalStepZero,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, besselZeroTransition,
    besselInitial, besselGridStateAt, besselGridStateBlock00, besselGridStateBlock01,
    besselGridStateBlock02, besselGridStateBlock03, besselGridStateBlock04,
    besselGridStateBlock05, besselGridStateBlock06, besselGridStateBlock07,
    besselGridStateBlock08, besselGridStateBlock09, besselGridStateBlock10,
    besselGridStateBlock11, besselGridStateBlock12, besselGridStateBlock13,
    besselGridStateBlock14, besselGridState006, besselGridState009, besselGridState014, besselGridState016, besselGridState017, besselGridState022, besselGridState023, besselGridState026, besselGridState030, besselGridState032, besselGridState034, besselGridState035, besselGridState037, besselGridState038, besselGridState043, besselGridState045, besselGridState046, besselGridState051, besselGridState055, besselGridState058, besselGridState063, besselGridState066, besselGridState068, besselStateSubset, linearInterval, widenInterval,
    rationalErrorInterval, rationalIntervalSubset, orderedInterval, Finset.sum_range_succ,
    IntervalRat.add, IntervalRat.mul, IntervalRat.scale, IntervalRat.singleton]

theorem compactCertificate210_stateChecks6 :
    compactCertificate210.stateChecks 18 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 30 12 (3033737827421887 / 32000000000000)) (orderedInterval (79783659456 / 1000000000000) (79783659458 / 1000000000000), orderedInterval (18276219544 / 1000000000000) (18276219545 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 26 12 (2571733154032007 / 32000000000000)) (orderedInterval (-45062766888 / 1000000000000) (-45062759456 / 1000000000000), orderedInterval (77032301120 / 1000000000000) (77032308551 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 16 12 (1609271198394221 / 32000000000000)) (orderedInterval (81268297069 / 1000000000000) (81268297070 / 1000000000000), orderedInterval (77002613676 / 1000000000000) (77002613677 / 1000000000000))) = true
  norm_num [besselStateAtRationalPoint, besselIntervalStepZero,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, besselZeroTransition,
    besselInitial, besselGridStateAt, besselGridStateBlock00, besselGridStateBlock01,
    besselGridStateBlock02, besselGridStateBlock03, besselGridStateBlock04,
    besselGridStateBlock05, besselGridStateBlock06, besselGridStateBlock07,
    besselGridStateBlock08, besselGridStateBlock09, besselGridStateBlock10,
    besselGridStateBlock11, besselGridStateBlock12, besselGridStateBlock13,
    besselGridStateBlock14, besselGridState006, besselGridState009, besselGridState014, besselGridState016, besselGridState017, besselGridState022, besselGridState023, besselGridState026, besselGridState030, besselGridState032, besselGridState034, besselGridState035, besselGridState037, besselGridState038, besselGridState043, besselGridState045, besselGridState046, besselGridState051, besselGridState055, besselGridState058, besselGridState063, besselGridState066, besselGridState068, besselStateSubset, linearInterval, widenInterval,
    rationalErrorInterval, rationalIntervalSubset, orderedInterval, Finset.sum_range_succ,
    IntervalRat.add, IntervalRat.mul, IntervalRat.scale, IntervalRat.singleton]

theorem compactCertificate210_stateChecks7 :
    compactCertificate210.stateChecks 21 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 9 12 (865471402690707 / 32000000000000)) (orderedInterval (66392279260 / 1000000000000) (66392283258 / 1000000000000), orderedInterval (-139549065663 / 1000000000000) (-139549061666 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 23 12 (2349923216473121 / 32000000000000)) (orderedInterval (-86067126596 / 1000000000000) (-86067122552 / 1000000000000), orderedInterval (36102958720 / 1000000000000) (36102962764 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 32 12 (3208619250978817 / 32000000000000)) (orderedInterval (39767157285 / 1000000000000) (39767157286 / 1000000000000), orderedInterval (68850303119 / 1000000000000) (68850303120 / 1000000000000))) = true
  norm_num [besselStateAtRationalPoint, besselIntervalStepZero,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, besselZeroTransition,
    besselInitial, besselGridStateAt, besselGridStateBlock00, besselGridStateBlock01,
    besselGridStateBlock02, besselGridStateBlock03, besselGridStateBlock04,
    besselGridStateBlock05, besselGridStateBlock06, besselGridStateBlock07,
    besselGridStateBlock08, besselGridStateBlock09, besselGridStateBlock10,
    besselGridStateBlock11, besselGridStateBlock12, besselGridStateBlock13,
    besselGridStateBlock14, besselGridState006, besselGridState009, besselGridState014, besselGridState016, besselGridState017, besselGridState022, besselGridState023, besselGridState026, besselGridState030, besselGridState032, besselGridState034, besselGridState035, besselGridState037, besselGridState038, besselGridState043, besselGridState045, besselGridState046, besselGridState051, besselGridState055, besselGridState058, besselGridState063, besselGridState066, besselGridState068, besselStateSubset, linearInterval, widenInterval,
    rationalErrorInterval, rationalIntervalSubset, orderedInterval, Finset.sum_range_succ,
    IntervalRat.add, IntervalRat.mul, IntervalRat.scale, IntervalRat.singleton]

theorem compactCertificate210_stateChecks8 :
    compactCertificate210.stateChecks 24 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 14 12 (1356728801605779 / 32000000000000)) (orderedInterval (-88076560362 / 1000000000000) (-88076454334 / 1000000000000), orderedInterval (86231791999 / 1000000000000) (86231898027 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 55 12 (5515027255196659 / 32000000000000)) (orderedInterval (-20364549122 / 1000000000000) (-20364549121 / 1000000000000), orderedInterval (-57204994395 / 1000000000000) (-57204994394 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 37 12 (3683782617697181 / 32000000000000)) (orderedInterval (24547705572 / 1000000000000) (24547706274 / 1000000000000), orderedInterval (-70303417538 / 1000000000000) (-70303416837 / 1000000000000))) = true
  norm_num [besselStateAtRationalPoint, besselIntervalStepZero,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, besselZeroTransition,
    besselInitial, besselGridStateAt, besselGridStateBlock00, besselGridStateBlock01,
    besselGridStateBlock02, besselGridStateBlock03, besselGridStateBlock04,
    besselGridStateBlock05, besselGridStateBlock06, besselGridStateBlock07,
    besselGridStateBlock08, besselGridStateBlock09, besselGridStateBlock10,
    besselGridStateBlock11, besselGridStateBlock12, besselGridStateBlock13,
    besselGridStateBlock14, besselGridState006, besselGridState009, besselGridState014, besselGridState016, besselGridState017, besselGridState022, besselGridState023, besselGridState026, besselGridState030, besselGridState032, besselGridState034, besselGridState035, besselGridState037, besselGridState038, besselGridState043, besselGridState045, besselGridState046, besselGridState051, besselGridState055, besselGridState058, besselGridState063, besselGridState066, besselGridState068, besselStateSubset, linearInterval, widenInterval,
    rationalErrorInterval, rationalIntervalSubset, orderedInterval, Finset.sum_range_succ,
    IntervalRat.add, IntervalRat.mul, IntervalRat.scale, IntervalRat.singleton]

theorem compactCertificate210_states : ∀ j,
    BesselStateValid (compactCertificate210.point j) (compactCertificate210.state j) :=
  compactCertificate210.statesValid_of_checks3 compactCertificate210_stateChecks0
    compactCertificate210_stateChecks1 compactCertificate210_stateChecks2
    compactCertificate210_stateChecks3 compactCertificate210_stateChecks4
    compactCertificate210_stateChecks5 compactCertificate210_stateChecks6
    compactCertificate210_stateChecks7 compactCertificate210_stateChecks8

theorem compactCertificate210_chunkChecks0_0 :
    compactCertificate210.chunkChecks (0 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 0) <| besselDerivativeNearFromState (1483 / 16) 0 (IntervalRat.scale (1483 / 16) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-58062153990 / 1000000000000) (-58062084360 / 1000000000000), orderedInterval (59450680215 / 1000000000000) (59450749845 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 0) <| besselDerivativeNearFromState (2184742175737183 / 32000000000000) 0 (IntervalRat.scale (1483 / 16) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-5624282922 / 1000000000000) (-5624282901 / 1000000000000), orderedInterval (96442480003 / 1000000000000) (96442480024 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 0) <| besselDerivativeNearFromState (706500731272639 / 6400000000000) 0 (IntervalRat.scale (1483 / 16) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-71296084361 / 1000000000000) (-71296084360 / 1000000000000), orderedInterval (-25826467456 / 1000000000000) (-25826467455 / 1000000000000)))) (orderedInterval (-27249948177 / 1000000000000) (-27249920571 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 0) <| besselDerivativeNearFromState (637502318055581 / 32000000000000) 0 (IntervalRat.scale (1483 / 16) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (171736881362 / 1000000000000) (171736882257 / 1000000000000), orderedInterval (-53841980700 / 1000000000000) (-53841979805 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 0) <| besselDerivativeNearFromState (1712420898416057 / 32000000000000) 0 (IntervalRat.scale (1483 / 16) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-84695217591 / 1000000000000) (-84695217590 / 1000000000000), orderedInterval (-67933703535 / 1000000000000) (-67933703534 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 0) <| besselDerivativeNearFromState (4649555852504469 / 32000000000000) 0 (IntervalRat.scale (1483 / 16) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (66192358307 / 1000000000000) (66192358352 / 1000000000000), orderedInterval (-168196712 / 1000000000000) (-168196666 / 1000000000000)))) (orderedInterval (-9661184681 / 1000000000000) (-9661184656 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 0) <| besselDerivativeNearFromState (3424841796833597 / 32000000000000) 0 (IntervalRat.scale (1483 / 16) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (64747026151 / 1000000000000) (64747026152 / 1000000000000), orderedInterval (41602788549 / 1000000000000) (41602788550 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 0) <| besselDerivativeNearFromState (5868524793432881 / 32000000000000) 0 (IntervalRat.scale (1483 / 16) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (54427781165 / 1000000000000) (54427788451 / 1000000000000), orderedInterval (-22708960355 / 1000000000000) (-22708953069 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 0) <| besselDerivativeNearFromState (4322728801605779 / 32000000000000) 0 (IntervalRat.scale (1483 / 16) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-48341107169 / 1000000000000) (-48341107168 / 1000000000000), orderedInterval (-48563897081 / 1000000000000) (-48563897080 / 1000000000000)))) (orderedInterval (-2847079948 / 1000000000000) (-2847079717 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate210_chunkChecks0_1 :
    compactCertificate210.chunkChecks (0 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 0) <| besselDerivativeNearFromState (6632177621263517 / 32000000000000) 0 (IntervalRat.scale (1483 / 16) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (35501595190 / 1000000000000) (35501595191 / 1000000000000), orderedInterval (42473771727 / 1000000000000) (42473771728 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 0) <| besselDerivativeNearFromState (3829089534949493 / 32000000000000) 0 (IntervalRat.scale (1483 / 16) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (63732012083 / 1000000000000) (63732012084 / 1000000000000), orderedInterval (35208862136 / 1000000000000) (35208862137 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 0) <| besselDerivativeNearFromState (6794786573870137 / 32000000000000) 0 (IntervalRat.scale (1483 / 16) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-26558612592 / 1000000000000) (-26558609739 / 1000000000000), orderedInterval (47945738107 / 1000000000000) (47945740960 / 1000000000000)))) (orderedInterval (-5361650457 / 1000000000000) (-5361650013 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 0) <| besselDerivativeNearFromState (6348571013841853 / 32000000000000) 0 (IntervalRat.scale (1483 / 16) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-53885588989 / 1000000000000) (-53885588988 / 1000000000000), orderedInterval (-17334736460 / 1000000000000) (-17334736458 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 0) <| besselDerivativeNearFromState (4530639837078349 / 32000000000000) 0 (IntervalRat.scale (1483 / 16) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-56255780128 / 1000000000000) (-56255780127 / 1000000000000), orderedInterval (-36294265288 / 1000000000000) (-36294265287 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 0) <| besselDerivativeNearFromState (5137262695248171 / 32000000000000) 0 (IntervalRat.scale (1483 / 16) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-56202467480 / 1000000000000) (-56202467479 / 1000000000000), orderedInterval (-28228737942 / 1000000000000) (-28228737941 / 1000000000000)))) (orderedInterval (-4062489774 / 1000000000000) (-4062489762 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 0) <| besselDerivativeNearFromState (4282914048738299 / 32000000000000) 0 (IntervalRat.scale (1483 / 16) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (30800477237 / 1000000000000) (30800479968 / 1000000000000), orderedInterval (-61823133821 / 1000000000000) (-61823131090 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 0) <| besselDerivativeNearFromState (3784084449812279 / 32000000000000) 0 (IntervalRat.scale (1483 / 16) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-24713506830 / 1000000000000) (-24713506080 / 1000000000000), orderedInterval (69190209830 / 1000000000000) (69190210581 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 0) <| besselDerivativeNearFromState (1096775165331621 / 6400000000000) 0 (IntervalRat.scale (1483 / 16) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (35997049490 / 1000000000000) (35997062435 / 1000000000000), orderedInterval (-49289145668 / 1000000000000) (-49289132723 / 1000000000000)))) (orderedInterval (2691612227 / 1000000000000) (2691612643 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate210_chunkChecks0_2 :
    compactCertificate210.chunkChecks (0 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 0) <| besselDerivativeNearFromState (3033737827421887 / 32000000000000) 0 (IntervalRat.scale (1483 / 16) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (79783659456 / 1000000000000) (79783659458 / 1000000000000), orderedInterval (18276219544 / 1000000000000) (18276219545 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 0) <| besselDerivativeNearFromState (2571733154032007 / 32000000000000) 0 (IntervalRat.scale (1483 / 16) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-45062766888 / 1000000000000) (-45062759456 / 1000000000000), orderedInterval (77032301120 / 1000000000000) (77032308551 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 0) <| besselDerivativeNearFromState (1609271198394221 / 32000000000000) 0 (IntervalRat.scale (1483 / 16) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (81268297069 / 1000000000000) (81268297070 / 1000000000000), orderedInterval (77002613676 / 1000000000000) (77002613677 / 1000000000000)))) (orderedInterval (-7560542517 / 1000000000000) (-7560542072 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 0) <| besselDerivativeNearFromState (865471402690707 / 32000000000000) 0 (IntervalRat.scale (1483 / 16) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (66392279260 / 1000000000000) (66392283258 / 1000000000000), orderedInterval (-139549065663 / 1000000000000) (-139549061666 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 0) <| besselDerivativeNearFromState (2349923216473121 / 32000000000000) 0 (IntervalRat.scale (1483 / 16) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-86067126596 / 1000000000000) (-86067122552 / 1000000000000), orderedInterval (36102958720 / 1000000000000) (36102962764 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 0) <| besselDerivativeNearFromState (3208619250978817 / 32000000000000) 0 (IntervalRat.scale (1483 / 16) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (39767157285 / 1000000000000) (39767157286 / 1000000000000), orderedInterval (68850303119 / 1000000000000) (68850303120 / 1000000000000)))) (orderedInterval (-2321058350 / 1000000000000) (-2321058172 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 0) <| besselDerivativeNearFromState (1356728801605779 / 32000000000000) 0 (IntervalRat.scale (1483 / 16) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-88076560362 / 1000000000000) (-88076454334 / 1000000000000), orderedInterval (86231791999 / 1000000000000) (86231898027 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 0) <| besselDerivativeNearFromState (5515027255196659 / 32000000000000) 0 (IntervalRat.scale (1483 / 16) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-20364549122 / 1000000000000) (-20364549121 / 1000000000000), orderedInterval (-57204994395 / 1000000000000) (-57204994394 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 0) <| besselDerivativeNearFromState (3683782617697181 / 32000000000000) 0 (IntervalRat.scale (1483 / 16) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (24547705572 / 1000000000000) (24547706274 / 1000000000000), orderedInterval (-70303417538 / 1000000000000) (-70303416837 / 1000000000000)))) (orderedInterval (-3479044796 / 1000000000000) (-3479043999 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate210_chunkChecks0 :
    compactCertificate210.chunkChecks (0 : Fin 5) 0 9 = true :=
  compactCertificate210.chunkChecks_nine_of_three (0 : Fin 5) compactCertificate210_chunkChecks0_0
    compactCertificate210_chunkChecks0_1 compactCertificate210_chunkChecks0_2

theorem compactCertificate210_chunkChecks1_0 :
    compactCertificate210.chunkChecks (1 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 1) <| besselDerivativeNearFromState (1483 / 16) 1 (IntervalRat.scale (1483 / 16) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-58062153990 / 1000000000000) (-58062084360 / 1000000000000), orderedInterval (59450680215 / 1000000000000) (59450749845 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 1) <| besselDerivativeNearFromState (2184742175737183 / 32000000000000) 1 (IntervalRat.scale (1483 / 16) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-5624282922 / 1000000000000) (-5624282901 / 1000000000000), orderedInterval (96442480003 / 1000000000000) (96442480024 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 1) <| besselDerivativeNearFromState (706500731272639 / 6400000000000) 1 (IntervalRat.scale (1483 / 16) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-71296084361 / 1000000000000) (-71296084360 / 1000000000000), orderedInterval (-25826467456 / 1000000000000) (-25826467455 / 1000000000000)))) (orderedInterval (22421124059 / 1000000000000) (22421151667 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 1) <| besselDerivativeNearFromState (637502318055581 / 32000000000000) 1 (IntervalRat.scale (1483 / 16) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (171736881362 / 1000000000000) (171736882257 / 1000000000000), orderedInterval (-53841980700 / 1000000000000) (-53841979805 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 1) <| besselDerivativeNearFromState (1712420898416057 / 32000000000000) 1 (IntervalRat.scale (1483 / 16) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-84695217591 / 1000000000000) (-84695217590 / 1000000000000), orderedInterval (-67933703535 / 1000000000000) (-67933703534 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 1) <| besselDerivativeNearFromState (4649555852504469 / 32000000000000) 1 (IntervalRat.scale (1483 / 16) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (66192358307 / 1000000000000) (66192358352 / 1000000000000), orderedInterval (-168196712 / 1000000000000) (-168196666 / 1000000000000)))) (orderedInterval (-1287748204 / 1000000000000) (-1287748183 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 1) <| besselDerivativeNearFromState (3424841796833597 / 32000000000000) 1 (IntervalRat.scale (1483 / 16) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (64747026151 / 1000000000000) (64747026152 / 1000000000000), orderedInterval (41602788549 / 1000000000000) (41602788550 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 1) <| besselDerivativeNearFromState (5868524793432881 / 32000000000000) 1 (IntervalRat.scale (1483 / 16) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (54427781165 / 1000000000000) (54427788451 / 1000000000000), orderedInterval (-22708960355 / 1000000000000) (-22708953069 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 1) <| besselDerivativeNearFromState (4322728801605779 / 32000000000000) 1 (IntervalRat.scale (1483 / 16) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-48341107169 / 1000000000000) (-48341107168 / 1000000000000), orderedInterval (-48563897081 / 1000000000000) (-48563897080 / 1000000000000)))) (orderedInterval (-324692867 / 1000000000000) (-324692413 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate210_chunkChecks1_1 :
    compactCertificate210.chunkChecks (1 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 1) <| besselDerivativeNearFromState (6632177621263517 / 32000000000000) 1 (IntervalRat.scale (1483 / 16) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (35501595190 / 1000000000000) (35501595191 / 1000000000000), orderedInterval (42473771727 / 1000000000000) (42473771728 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 1) <| besselDerivativeNearFromState (3829089534949493 / 32000000000000) 1 (IntervalRat.scale (1483 / 16) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (63732012083 / 1000000000000) (63732012084 / 1000000000000), orderedInterval (35208862136 / 1000000000000) (35208862137 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 1) <| besselDerivativeNearFromState (6794786573870137 / 32000000000000) 1 (IntervalRat.scale (1483 / 16) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-26558612592 / 1000000000000) (-26558609739 / 1000000000000), orderedInterval (47945738107 / 1000000000000) (47945740960 / 1000000000000)))) (orderedInterval (2106217588 / 1000000000000) (2106218594 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 1) <| besselDerivativeNearFromState (6348571013841853 / 32000000000000) 1 (IntervalRat.scale (1483 / 16) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-53885588989 / 1000000000000) (-53885588988 / 1000000000000), orderedInterval (-17334736460 / 1000000000000) (-17334736458 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 1) <| besselDerivativeNearFromState (4530639837078349 / 32000000000000) 1 (IntervalRat.scale (1483 / 16) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-56255780128 / 1000000000000) (-56255780127 / 1000000000000), orderedInterval (-36294265288 / 1000000000000) (-36294265287 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 1) <| besselDerivativeNearFromState (5137262695248171 / 32000000000000) 1 (IntervalRat.scale (1483 / 16) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-56202467480 / 1000000000000) (-56202467479 / 1000000000000), orderedInterval (-28228737942 / 1000000000000) (-28228737941 / 1000000000000)))) (orderedInterval (-4325330090 / 1000000000000) (-4325330071 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 1) <| besselDerivativeNearFromState (4282914048738299 / 32000000000000) 1 (IntervalRat.scale (1483 / 16) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (30800477237 / 1000000000000) (30800479968 / 1000000000000), orderedInterval (-61823133821 / 1000000000000) (-61823131090 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 1) <| besselDerivativeNearFromState (3784084449812279 / 32000000000000) 1 (IntervalRat.scale (1483 / 16) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-24713506830 / 1000000000000) (-24713506080 / 1000000000000), orderedInterval (69190209830 / 1000000000000) (69190210581 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 1) <| besselDerivativeNearFromState (1096775165331621 / 6400000000000) 1 (IntervalRat.scale (1483 / 16) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (35997049490 / 1000000000000) (35997062435 / 1000000000000), orderedInterval (-49289145668 / 1000000000000) (-49289132723 / 1000000000000)))) (orderedInterval (-8415860642 / 1000000000000) (-8415859915 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate210_chunkChecks1_2 :
    compactCertificate210.chunkChecks (1 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 1) <| besselDerivativeNearFromState (3033737827421887 / 32000000000000) 1 (IntervalRat.scale (1483 / 16) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (79783659456 / 1000000000000) (79783659458 / 1000000000000), orderedInterval (18276219544 / 1000000000000) (18276219545 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 1) <| besselDerivativeNearFromState (2571733154032007 / 32000000000000) 1 (IntervalRat.scale (1483 / 16) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-45062766888 / 1000000000000) (-45062759456 / 1000000000000), orderedInterval (77032301120 / 1000000000000) (77032308551 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 1) <| besselDerivativeNearFromState (1609271198394221 / 32000000000000) 1 (IntervalRat.scale (1483 / 16) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (81268297069 / 1000000000000) (81268297070 / 1000000000000), orderedInterval (77002613676 / 1000000000000) (77002613677 / 1000000000000)))) (orderedInterval (-5409275936 / 1000000000000) (-5409275549 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 1) <| besselDerivativeNearFromState (865471402690707 / 32000000000000) 1 (IntervalRat.scale (1483 / 16) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (66392279260 / 1000000000000) (66392283258 / 1000000000000), orderedInterval (-139549065663 / 1000000000000) (-139549061666 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 1) <| besselDerivativeNearFromState (2349923216473121 / 32000000000000) 1 (IntervalRat.scale (1483 / 16) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-86067126596 / 1000000000000) (-86067122552 / 1000000000000), orderedInterval (36102958720 / 1000000000000) (36102962764 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 1) <| besselDerivativeNearFromState (3208619250978817 / 32000000000000) 1 (IntervalRat.scale (1483 / 16) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (39767157285 / 1000000000000) (39767157286 / 1000000000000), orderedInterval (68850303119 / 1000000000000) (68850303120 / 1000000000000)))) (orderedInterval (-5605268974 / 1000000000000) (-5605268869 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 1) <| besselDerivativeNearFromState (1356728801605779 / 32000000000000) 1 (IntervalRat.scale (1483 / 16) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-88076560362 / 1000000000000) (-88076454334 / 1000000000000), orderedInterval (86231791999 / 1000000000000) (86231898027 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 1) <| besselDerivativeNearFromState (5515027255196659 / 32000000000000) 1 (IntervalRat.scale (1483 / 16) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-20364549122 / 1000000000000) (-20364549121 / 1000000000000), orderedInterval (-57204994395 / 1000000000000) (-57204994394 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 1) <| besselDerivativeNearFromState (3683782617697181 / 32000000000000) 1 (IntervalRat.scale (1483 / 16) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (24547705572 / 1000000000000) (24547706274 / 1000000000000), orderedInterval (-70303417538 / 1000000000000) (-70303416837 / 1000000000000)))) (orderedInterval (25279322938 / 1000000000000) (25279323431 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate210_chunkChecks1 :
    compactCertificate210.chunkChecks (1 : Fin 5) 0 9 = true :=
  compactCertificate210.chunkChecks_nine_of_three (1 : Fin 5) compactCertificate210_chunkChecks1_0
    compactCertificate210_chunkChecks1_1 compactCertificate210_chunkChecks1_2

theorem compactCertificate210_chunkChecks2_0 :
    compactCertificate210.chunkChecks (2 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 2) <| besselDerivativeNearFromState (1483 / 16) 2 (IntervalRat.scale (1483 / 16) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-58062153990 / 1000000000000) (-58062084360 / 1000000000000), orderedInterval (59450680215 / 1000000000000) (59450749845 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 2) <| besselDerivativeNearFromState (2184742175737183 / 32000000000000) 2 (IntervalRat.scale (1483 / 16) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-5624282922 / 1000000000000) (-5624282901 / 1000000000000), orderedInterval (96442480003 / 1000000000000) (96442480024 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 2) <| besselDerivativeNearFromState (706500731272639 / 6400000000000) 2 (IntervalRat.scale (1483 / 16) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-71296084361 / 1000000000000) (-71296084360 / 1000000000000), orderedInterval (-25826467456 / 1000000000000) (-25826467455 / 1000000000000)))) (orderedInterval (28734853456 / 1000000000000) (28734881362 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 2) <| besselDerivativeNearFromState (637502318055581 / 32000000000000) 2 (IntervalRat.scale (1483 / 16) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (171736881362 / 1000000000000) (171736882257 / 1000000000000), orderedInterval (-53841980700 / 1000000000000) (-53841979805 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 2) <| besselDerivativeNearFromState (1712420898416057 / 32000000000000) 2 (IntervalRat.scale (1483 / 16) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-84695217591 / 1000000000000) (-84695217590 / 1000000000000), orderedInterval (-67933703535 / 1000000000000) (-67933703534 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 2) <| besselDerivativeNearFromState (4649555852504469 / 32000000000000) 2 (IntervalRat.scale (1483 / 16) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (66192358307 / 1000000000000) (66192358352 / 1000000000000), orderedInterval (-168196712 / 1000000000000) (-168196666 / 1000000000000)))) (orderedInterval (12694407187 / 1000000000000) (12694407214 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 2) <| besselDerivativeNearFromState (3424841796833597 / 32000000000000) 2 (IntervalRat.scale (1483 / 16) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (64747026151 / 1000000000000) (64747026152 / 1000000000000), orderedInterval (41602788549 / 1000000000000) (41602788550 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 2) <| besselDerivativeNearFromState (5868524793432881 / 32000000000000) 2 (IntervalRat.scale (1483 / 16) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (54427781165 / 1000000000000) (54427788451 / 1000000000000), orderedInterval (-22708960355 / 1000000000000) (-22708953069 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 2) <| besselDerivativeNearFromState (4322728801605779 / 32000000000000) 2 (IntervalRat.scale (1483 / 16) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-48341107169 / 1000000000000) (-48341107168 / 1000000000000), orderedInterval (-48563897081 / 1000000000000) (-48563897080 / 1000000000000)))) (orderedInterval (9057243254 / 1000000000000) (9057244156 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate210_chunkChecks2_1 :
    compactCertificate210.chunkChecks (2 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 2) <| besselDerivativeNearFromState (6632177621263517 / 32000000000000) 2 (IntervalRat.scale (1483 / 16) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (35501595190 / 1000000000000) (35501595191 / 1000000000000), orderedInterval (42473771727 / 1000000000000) (42473771728 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 2) <| besselDerivativeNearFromState (3829089534949493 / 32000000000000) 2 (IntervalRat.scale (1483 / 16) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (63732012083 / 1000000000000) (63732012084 / 1000000000000), orderedInterval (35208862136 / 1000000000000) (35208862137 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 2) <| besselDerivativeNearFromState (6794786573870137 / 32000000000000) 2 (IntervalRat.scale (1483 / 16) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-26558612592 / 1000000000000) (-26558609739 / 1000000000000), orderedInterval (47945738107 / 1000000000000) (47945740960 / 1000000000000)))) (orderedInterval (43462607898 / 1000000000000) (43462610201 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 2) <| besselDerivativeNearFromState (6348571013841853 / 32000000000000) 2 (IntervalRat.scale (1483 / 16) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-53885588989 / 1000000000000) (-53885588988 / 1000000000000), orderedInterval (-17334736460 / 1000000000000) (-17334736458 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 2) <| besselDerivativeNearFromState (4530639837078349 / 32000000000000) 2 (IntervalRat.scale (1483 / 16) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-56255780128 / 1000000000000) (-56255780127 / 1000000000000), orderedInterval (-36294265288 / 1000000000000) (-36294265287 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 2) <| besselDerivativeNearFromState (5137262695248171 / 32000000000000) 2 (IntervalRat.scale (1483 / 16) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-56202467480 / 1000000000000) (-56202467479 / 1000000000000), orderedInterval (-28228737942 / 1000000000000) (-28228737941 / 1000000000000)))) (orderedInterval (7149157787 / 1000000000000) (7149157818 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 2) <| besselDerivativeNearFromState (4282914048738299 / 32000000000000) 2 (IntervalRat.scale (1483 / 16) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (30800477237 / 1000000000000) (30800479968 / 1000000000000), orderedInterval (-61823133821 / 1000000000000) (-61823131090 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 2) <| besselDerivativeNearFromState (3784084449812279 / 32000000000000) 2 (IntervalRat.scale (1483 / 16) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-24713506830 / 1000000000000) (-24713506080 / 1000000000000), orderedInterval (69190209830 / 1000000000000) (69190210581 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 2) <| besselDerivativeNearFromState (1096775165331621 / 6400000000000) 2 (IntervalRat.scale (1483 / 16) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (35997049490 / 1000000000000) (35997062435 / 1000000000000), orderedInterval (-49289145668 / 1000000000000) (-49289132723 / 1000000000000)))) (orderedInterval (-6103569560 / 1000000000000) (-6103568264 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate210_chunkChecks2_2 :
    compactCertificate210.chunkChecks (2 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 2) <| besselDerivativeNearFromState (3033737827421887 / 32000000000000) 2 (IntervalRat.scale (1483 / 16) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (79783659456 / 1000000000000) (79783659458 / 1000000000000), orderedInterval (18276219544 / 1000000000000) (18276219545 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 2) <| besselDerivativeNearFromState (2571733154032007 / 32000000000000) 2 (IntervalRat.scale (1483 / 16) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-45062766888 / 1000000000000) (-45062759456 / 1000000000000), orderedInterval (77032301120 / 1000000000000) (77032308551 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 2) <| besselDerivativeNearFromState (1609271198394221 / 32000000000000) 2 (IntervalRat.scale (1483 / 16) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (81268297069 / 1000000000000) (81268297070 / 1000000000000), orderedInterval (77002613676 / 1000000000000) (77002613677 / 1000000000000)))) (orderedInterval (10708106320 / 1000000000000) (10708106662 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 2) <| besselDerivativeNearFromState (865471402690707 / 32000000000000) 2 (IntervalRat.scale (1483 / 16) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (66392279260 / 1000000000000) (66392283258 / 1000000000000), orderedInterval (-139549065663 / 1000000000000) (-139549061666 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 2) <| besselDerivativeNearFromState (2349923216473121 / 32000000000000) 2 (IntervalRat.scale (1483 / 16) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-86067126596 / 1000000000000) (-86067122552 / 1000000000000), orderedInterval (36102958720 / 1000000000000) (36102962764 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 2) <| besselDerivativeNearFromState (3208619250978817 / 32000000000000) 2 (IntervalRat.scale (1483 / 16) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (39767157285 / 1000000000000) (39767157286 / 1000000000000), orderedInterval (68850303119 / 1000000000000) (68850303120 / 1000000000000)))) (orderedInterval (2505888843 / 1000000000000) (2505888919 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 2) <| besselDerivativeNearFromState (1356728801605779 / 32000000000000) 2 (IntervalRat.scale (1483 / 16) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-88076560362 / 1000000000000) (-88076454334 / 1000000000000), orderedInterval (86231791999 / 1000000000000) (86231898027 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 2) <| besselDerivativeNearFromState (5515027255196659 / 32000000000000) 2 (IntervalRat.scale (1483 / 16) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-20364549122 / 1000000000000) (-20364549121 / 1000000000000), orderedInterval (-57204994395 / 1000000000000) (-57204994394 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 2) <| besselDerivativeNearFromState (3683782617697181 / 32000000000000) 2 (IntervalRat.scale (1483 / 16) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (24547705572 / 1000000000000) (24547706274 / 1000000000000), orderedInterval (-70303417538 / 1000000000000) (-70303416837 / 1000000000000)))) (orderedInterval (1211729565 / 1000000000000) (1211729961 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate210_chunkChecks2 :
    compactCertificate210.chunkChecks (2 : Fin 5) 0 9 = true :=
  compactCertificate210.chunkChecks_nine_of_three (2 : Fin 5) compactCertificate210_chunkChecks2_0
    compactCertificate210_chunkChecks2_1 compactCertificate210_chunkChecks2_2

theorem compactCertificate210_chunkChecks3_0 :
    compactCertificate210.chunkChecks (3 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 3) <| besselDerivativeNearFromState (1483 / 16) 3 (IntervalRat.scale (1483 / 16) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-58062153990 / 1000000000000) (-58062084360 / 1000000000000), orderedInterval (59450680215 / 1000000000000) (59450749845 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 3) <| besselDerivativeNearFromState (2184742175737183 / 32000000000000) 3 (IntervalRat.scale (1483 / 16) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-5624282922 / 1000000000000) (-5624282901 / 1000000000000), orderedInterval (96442480003 / 1000000000000) (96442480024 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 3) <| besselDerivativeNearFromState (706500731272639 / 6400000000000) 3 (IntervalRat.scale (1483 / 16) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-71296084361 / 1000000000000) (-71296084360 / 1000000000000), orderedInterval (-25826467456 / 1000000000000) (-25826467455 / 1000000000000)))) (orderedInterval (-21670417461 / 1000000000000) (-21670389560 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 3) <| besselDerivativeNearFromState (637502318055581 / 32000000000000) 3 (IntervalRat.scale (1483 / 16) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (171736881362 / 1000000000000) (171736882257 / 1000000000000), orderedInterval (-53841980700 / 1000000000000) (-53841979805 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 3) <| besselDerivativeNearFromState (1712420898416057 / 32000000000000) 3 (IntervalRat.scale (1483 / 16) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-84695217591 / 1000000000000) (-84695217590 / 1000000000000), orderedInterval (-67933703535 / 1000000000000) (-67933703534 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 3) <| besselDerivativeNearFromState (4649555852504469 / 32000000000000) 3 (IntervalRat.scale (1483 / 16) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (66192358307 / 1000000000000) (66192358352 / 1000000000000), orderedInterval (-168196712 / 1000000000000) (-168196666 / 1000000000000)))) (orderedInterval (288377307 / 1000000000000) (288377347 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 3) <| besselDerivativeNearFromState (3424841796833597 / 32000000000000) 3 (IntervalRat.scale (1483 / 16) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (64747026151 / 1000000000000) (64747026152 / 1000000000000), orderedInterval (41602788549 / 1000000000000) (41602788550 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 3) <| besselDerivativeNearFromState (5868524793432881 / 32000000000000) 3 (IntervalRat.scale (1483 / 16) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (54427781165 / 1000000000000) (54427788451 / 1000000000000), orderedInterval (-22708960355 / 1000000000000) (-22708953069 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 3) <| besselDerivativeNearFromState (4322728801605779 / 32000000000000) 3 (IntervalRat.scale (1483 / 16) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-48341107169 / 1000000000000) (-48341107168 / 1000000000000), orderedInterval (-48563897081 / 1000000000000) (-48563897080 / 1000000000000)))) (orderedInterval (-1889858567 / 1000000000000) (-1889856786 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate210_chunkChecks3_1 :
    compactCertificate210.chunkChecks (3 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 3) <| besselDerivativeNearFromState (6632177621263517 / 32000000000000) 3 (IntervalRat.scale (1483 / 16) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (35501595190 / 1000000000000) (35501595191 / 1000000000000), orderedInterval (42473771727 / 1000000000000) (42473771728 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 3) <| besselDerivativeNearFromState (3829089534949493 / 32000000000000) 3 (IntervalRat.scale (1483 / 16) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (63732012083 / 1000000000000) (63732012084 / 1000000000000), orderedInterval (35208862136 / 1000000000000) (35208862137 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 3) <| besselDerivativeNearFromState (6794786573870137 / 32000000000000) 3 (IntervalRat.scale (1483 / 16) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-26558612592 / 1000000000000) (-26558609739 / 1000000000000), orderedInterval (47945738107 / 1000000000000) (47945740960 / 1000000000000)))) (orderedInterval (-3649010656 / 1000000000000) (-3649005396 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 3) <| besselDerivativeNearFromState (6348571013841853 / 32000000000000) 3 (IntervalRat.scale (1483 / 16) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-53885588989 / 1000000000000) (-53885588988 / 1000000000000), orderedInterval (-17334736460 / 1000000000000) (-17334736458 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 3) <| besselDerivativeNearFromState (4530639837078349 / 32000000000000) 3 (IntervalRat.scale (1483 / 16) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-56255780128 / 1000000000000) (-56255780127 / 1000000000000), orderedInterval (-36294265288 / 1000000000000) (-36294265287 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 3) <| besselDerivativeNearFromState (5137262695248171 / 32000000000000) 3 (IntervalRat.scale (1483 / 16) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-56202467480 / 1000000000000) (-56202467479 / 1000000000000), orderedInterval (-28228737942 / 1000000000000) (-28228737941 / 1000000000000)))) (orderedInterval (8343913849 / 1000000000000) (8343913901 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 3) <| besselDerivativeNearFromState (4282914048738299 / 32000000000000) 3 (IntervalRat.scale (1483 / 16) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (30800477237 / 1000000000000) (30800479968 / 1000000000000), orderedInterval (-61823133821 / 1000000000000) (-61823131090 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 3) <| besselDerivativeNearFromState (3784084449812279 / 32000000000000) 3 (IntervalRat.scale (1483 / 16) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-24713506830 / 1000000000000) (-24713506080 / 1000000000000), orderedInterval (69190209830 / 1000000000000) (69190210581 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 3) <| besselDerivativeNearFromState (1096775165331621 / 6400000000000) 3 (IntervalRat.scale (1483 / 16) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (35997049490 / 1000000000000) (35997062435 / 1000000000000), orderedInterval (-49289145668 / 1000000000000) (-49289132723 / 1000000000000)))) (orderedInterval (18413502293 / 1000000000000) (18413504616 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate210_chunkChecks3_2 :
    compactCertificate210.chunkChecks (3 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 3) <| besselDerivativeNearFromState (3033737827421887 / 32000000000000) 3 (IntervalRat.scale (1483 / 16) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (79783659456 / 1000000000000) (79783659458 / 1000000000000), orderedInterval (18276219544 / 1000000000000) (18276219545 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 3) <| besselDerivativeNearFromState (2571733154032007 / 32000000000000) 3 (IntervalRat.scale (1483 / 16) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-45062766888 / 1000000000000) (-45062759456 / 1000000000000), orderedInterval (77032301120 / 1000000000000) (77032308551 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 3) <| besselDerivativeNearFromState (1609271198394221 / 32000000000000) 3 (IntervalRat.scale (1483 / 16) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (81268297069 / 1000000000000) (81268297070 / 1000000000000), orderedInterval (77002613676 / 1000000000000) (77002613677 / 1000000000000)))) (orderedInterval (5452676881 / 1000000000000) (5452677179 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 3) <| besselDerivativeNearFromState (865471402690707 / 32000000000000) 3 (IntervalRat.scale (1483 / 16) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (66392279260 / 1000000000000) (66392283258 / 1000000000000), orderedInterval (-139549065663 / 1000000000000) (-139549061666 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 3) <| besselDerivativeNearFromState (2349923216473121 / 32000000000000) 3 (IntervalRat.scale (1483 / 16) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-86067126596 / 1000000000000) (-86067122552 / 1000000000000), orderedInterval (36102958720 / 1000000000000) (36102962764 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 3) <| besselDerivativeNearFromState (3208619250978817 / 32000000000000) 3 (IntervalRat.scale (1483 / 16) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (39767157285 / 1000000000000) (39767157286 / 1000000000000), orderedInterval (68850303119 / 1000000000000) (68850303120 / 1000000000000)))) (orderedInterval (6995939218 / 1000000000000) (6995939277 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 3) <| besselDerivativeNearFromState (1356728801605779 / 32000000000000) 3 (IntervalRat.scale (1483 / 16) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-88076560362 / 1000000000000) (-88076454334 / 1000000000000), orderedInterval (86231791999 / 1000000000000) (86231898027 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 3) <| besselDerivativeNearFromState (5515027255196659 / 32000000000000) 3 (IntervalRat.scale (1483 / 16) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-20364549122 / 1000000000000) (-20364549121 / 1000000000000), orderedInterval (-57204994395 / 1000000000000) (-57204994394 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 3) <| besselDerivativeNearFromState (3683782617697181 / 32000000000000) 3 (IntervalRat.scale (1483 / 16) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (24547705572 / 1000000000000) (24547706274 / 1000000000000), orderedInterval (-70303417538 / 1000000000000) (-70303416837 / 1000000000000)))) (orderedInterval (-55268111162 / 1000000000000) (-55268110762 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate210_chunkChecks3 :
    compactCertificate210.chunkChecks (3 : Fin 5) 0 9 = true :=
  compactCertificate210.chunkChecks_nine_of_three (3 : Fin 5) compactCertificate210_chunkChecks3_0
    compactCertificate210_chunkChecks3_1 compactCertificate210_chunkChecks3_2

theorem compactCertificate210_chunkChecks4_0 :
    compactCertificate210.chunkChecks (4 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 4) <| besselDerivativeNearFromState (1483 / 16) 4 (IntervalRat.scale (1483 / 16) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-58062153990 / 1000000000000) (-58062084360 / 1000000000000), orderedInterval (59450680215 / 1000000000000) (59450749845 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 4) <| besselDerivativeNearFromState (2184742175737183 / 32000000000000) 4 (IntervalRat.scale (1483 / 16) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-5624282922 / 1000000000000) (-5624282901 / 1000000000000), orderedInterval (96442480003 / 1000000000000) (96442480024 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 4) <| besselDerivativeNearFromState (706500731272639 / 6400000000000) 4 (IntervalRat.scale (1483 / 16) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-71296084361 / 1000000000000) (-71296084360 / 1000000000000), orderedInterval (-25826467456 / 1000000000000) (-25826467455 / 1000000000000)))) (orderedInterval (-30976338613 / 1000000000000) (-30976310416 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 4) <| besselDerivativeNearFromState (637502318055581 / 32000000000000) 4 (IntervalRat.scale (1483 / 16) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (171736881362 / 1000000000000) (171736882257 / 1000000000000), orderedInterval (-53841980700 / 1000000000000) (-53841979805 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 4) <| besselDerivativeNearFromState (1712420898416057 / 32000000000000) 4 (IntervalRat.scale (1483 / 16) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-84695217591 / 1000000000000) (-84695217590 / 1000000000000), orderedInterval (-67933703535 / 1000000000000) (-67933703534 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 4) <| besselDerivativeNearFromState (4649555852504469 / 32000000000000) 4 (IntervalRat.scale (1483 / 16) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (66192358307 / 1000000000000) (66192358352 / 1000000000000), orderedInterval (-168196712 / 1000000000000) (-168196666 / 1000000000000)))) (orderedInterval (-28769135850 / 1000000000000) (-28769135789 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 4) <| besselDerivativeNearFromState (3424841796833597 / 32000000000000) 4 (IntervalRat.scale (1483 / 16) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (64747026151 / 1000000000000) (64747026152 / 1000000000000), orderedInterval (41602788549 / 1000000000000) (41602788550 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 4) <| besselDerivativeNearFromState (5868524793432881 / 32000000000000) 4 (IntervalRat.scale (1483 / 16) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (54427781165 / 1000000000000) (54427788451 / 1000000000000), orderedInterval (-22708960355 / 1000000000000) (-22708953069 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 4) <| besselDerivativeNearFromState (4322728801605779 / 32000000000000) 4 (IntervalRat.scale (1483 / 16) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-48341107169 / 1000000000000) (-48341107168 / 1000000000000), orderedInterval (-48563897081 / 1000000000000) (-48563897080 / 1000000000000)))) (orderedInterval (-30958294572 / 1000000000000) (-30958291036 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate210_chunkChecks4_1 :
    compactCertificate210.chunkChecks (4 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 4) <| besselDerivativeNearFromState (6632177621263517 / 32000000000000) 4 (IntervalRat.scale (1483 / 16) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (35501595190 / 1000000000000) (35501595191 / 1000000000000), orderedInterval (42473771727 / 1000000000000) (42473771728 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 4) <| besselDerivativeNearFromState (3829089534949493 / 32000000000000) 4 (IntervalRat.scale (1483 / 16) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (63732012083 / 1000000000000) (63732012084 / 1000000000000), orderedInterval (35208862136 / 1000000000000) (35208862137 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 4) <| besselDerivativeNearFromState (6794786573870137 / 32000000000000) 4 (IntervalRat.scale (1483 / 16) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-26558612592 / 1000000000000) (-26558609739 / 1000000000000), orderedInterval (47945738107 / 1000000000000) (47945740960 / 1000000000000)))) (orderedInterval (-248493979674 / 1000000000000) (-248493967598 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 4) <| besselDerivativeNearFromState (6348571013841853 / 32000000000000) 4 (IntervalRat.scale (1483 / 16) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-53885588989 / 1000000000000) (-53885588988 / 1000000000000), orderedInterval (-17334736460 / 1000000000000) (-17334736458 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 4) <| besselDerivativeNearFromState (4530639837078349 / 32000000000000) 4 (IntervalRat.scale (1483 / 16) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-56255780128 / 1000000000000) (-56255780127 / 1000000000000), orderedInterval (-36294265288 / 1000000000000) (-36294265287 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 4) <| besselDerivativeNearFromState (5137262695248171 / 32000000000000) 4 (IntervalRat.scale (1483 / 16) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-56202467480 / 1000000000000) (-56202467479 / 1000000000000), orderedInterval (-28228737942 / 1000000000000) (-28228737941 / 1000000000000)))) (orderedInterval (-6162887156 / 1000000000000) (-6162887067 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 4) <| besselDerivativeNearFromState (4282914048738299 / 32000000000000) 4 (IntervalRat.scale (1483 / 16) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (30800477237 / 1000000000000) (30800479968 / 1000000000000), orderedInterval (-61823133821 / 1000000000000) (-61823131090 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 4) <| besselDerivativeNearFromState (3784084449812279 / 32000000000000) 4 (IntervalRat.scale (1483 / 16) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-24713506830 / 1000000000000) (-24713506080 / 1000000000000), orderedInterval (69190209830 / 1000000000000) (69190210581 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 4) <| besselDerivativeNearFromState (1096775165331621 / 6400000000000) 4 (IntervalRat.scale (1483 / 16) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (35997049490 / 1000000000000) (35997062435 / 1000000000000), orderedInterval (-49289145668 / 1000000000000) (-49289132723 / 1000000000000)))) (orderedInterval (15666049813 / 1000000000000) (15666054033 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate210_chunkChecks4_2 :
    compactCertificate210.chunkChecks (4 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 4) <| besselDerivativeNearFromState (3033737827421887 / 32000000000000) 4 (IntervalRat.scale (1483 / 16) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (79783659456 / 1000000000000) (79783659458 / 1000000000000), orderedInterval (18276219544 / 1000000000000) (18276219545 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 4) <| besselDerivativeNearFromState (2571733154032007 / 32000000000000) 4 (IntervalRat.scale (1483 / 16) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-45062766888 / 1000000000000) (-45062759456 / 1000000000000), orderedInterval (77032301120 / 1000000000000) (77032308551 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 4) <| besselDerivativeNearFromState (1609271198394221 / 32000000000000) 4 (IntervalRat.scale (1483 / 16) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (81268297069 / 1000000000000) (81268297070 / 1000000000000), orderedInterval (77002613676 / 1000000000000) (77002613677 / 1000000000000)))) (orderedInterval (-12408195052 / 1000000000000) (-12408194788 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 4) <| besselDerivativeNearFromState (865471402690707 / 32000000000000) 4 (IntervalRat.scale (1483 / 16) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (66392279260 / 1000000000000) (66392283258 / 1000000000000), orderedInterval (-139549065663 / 1000000000000) (-139549061666 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 4) <| besselDerivativeNearFromState (2349923216473121 / 32000000000000) 4 (IntervalRat.scale (1483 / 16) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-86067126596 / 1000000000000) (-86067122552 / 1000000000000), orderedInterval (36102958720 / 1000000000000) (36102962764 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 4) <| besselDerivativeNearFromState (3208619250978817 / 32000000000000) 4 (IntervalRat.scale (1483 / 16) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (39767157285 / 1000000000000) (39767157286 / 1000000000000), orderedInterval (68850303119 / 1000000000000) (68850303120 / 1000000000000)))) (orderedInterval (-3564254877 / 1000000000000) (-3564254828 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 4) <| besselDerivativeNearFromState (1356728801605779 / 32000000000000) 4 (IntervalRat.scale (1483 / 16) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-88076560362 / 1000000000000) (-88076454334 / 1000000000000), orderedInterval (86231791999 / 1000000000000) (86231898027 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 4) <| besselDerivativeNearFromState (5515027255196659 / 32000000000000) 4 (IntervalRat.scale (1483 / 16) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-20364549122 / 1000000000000) (-20364549121 / 1000000000000), orderedInterval (-57204994395 / 1000000000000) (-57204994394 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 4) <| besselDerivativeNearFromState (3683782617697181 / 32000000000000) 4 (IntervalRat.scale (1483 / 16) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (24547705572 / 1000000000000) (24547706274 / 1000000000000), orderedInterval (-70303417538 / 1000000000000) (-70303416837 / 1000000000000)))) (orderedInterval (10025728945 / 1000000000000) (10025729427 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate210_chunkChecks4 :
    compactCertificate210.chunkChecks (4 : Fin 5) 0 9 = true :=
  compactCertificate210.chunkChecks_nine_of_three (4 : Fin 5) compactCertificate210_chunkChecks4_0
    compactCertificate210_chunkChecks4_1 compactCertificate210_chunkChecks4_2

theorem compactCertificate210_chunks :
    ∀ r : Fin 5, ∀ b, compactCertificate210.chunkCheck r b = true :=
  compactCertificate210.chunkChecks_all (by
    intro r
    fin_cases r
    · exact compactCertificate210_chunkChecks0
    · exact compactCertificate210_chunkChecks1
    · exact compactCertificate210_chunkChecks2
    · exact compactCertificate210_chunkChecks3
    · exact compactCertificate210_chunkChecks4)

theorem compactCertificate210_coefficient0 :
    compactCertificate210.coefficientCheck (0 : Fin 5) = true := by
  norm_num [CompactCertificate.coefficientCheck, intervalFinSumHull,
    compactCertificate210, rationalIntervalSubset, orderedInterval, Fin.sum_univ_succ]

theorem compactCertificate210_coefficient1 :
    compactCertificate210.coefficientCheck (1 : Fin 5) = true := by
  norm_num [CompactCertificate.coefficientCheck, intervalFinSumHull,
    compactCertificate210, rationalIntervalSubset, orderedInterval, Fin.sum_univ_succ]

theorem compactCertificate210_coefficient2 :
    compactCertificate210.coefficientCheck (2 : Fin 5) = true := by
  norm_num [CompactCertificate.coefficientCheck, intervalFinSumHull,
    compactCertificate210, rationalIntervalSubset, orderedInterval, Fin.sum_univ_succ]

theorem compactCertificate210_coefficient3 :
    compactCertificate210.coefficientCheck (3 : Fin 5) = true := by
  norm_num [CompactCertificate.coefficientCheck, intervalFinSumHull,
    compactCertificate210, rationalIntervalSubset, orderedInterval, Fin.sum_univ_succ]

theorem compactCertificate210_coefficient4 :
    compactCertificate210.coefficientCheck (4 : Fin 5) = true := by
  norm_num [CompactCertificate.coefficientCheck, intervalFinSumHull,
    compactCertificate210, rationalIntervalSubset, orderedInterval, Fin.sum_univ_succ]

theorem compactCertificate210_coefficients : ∀ r : Fin 5,
    compactCertificate210.coefficientCheck r = true := by
  intro r
  fin_cases r
  · exact compactCertificate210_coefficient0
  · exact compactCertificate210_coefficient1
  · exact compactCertificate210_coefficient2
  · exact compactCertificate210_coefficient3
  · exact compactCertificate210_coefficient4

theorem compactCertificate210_lower : (1 : ℚ) ≤ compactCertificate210.output.lo := by
  norm_num [CompactCertificate.output, CompactCertificate.interval,
    CompactCertificate.coefficientTargetNat, compactCertificate210, dualConstant,
    intervalTaylorSum, intervalPow, intervalSub, intervalMaxAbs, widenInterval,
    rationalErrorInterval, orderedInterval, IntervalRat.add, IntervalRat.mul, IntervalRat.scale,
    IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4]

theorem compactCertificate210_proves {t : ℝ} (ht : t ∈ compactCertificate210.interval) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t :=
  compactCertificate210.proves compactCertificate210_states compactCertificate210_chunks
    compactCertificate210_coefficients compactCertificate210_lower ht

end Erdos232
