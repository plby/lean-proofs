/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, OpenAI Codex
-/
import ErdosProblems.Erdos232.CompactBase

open LeanCert.Core
namespace Erdos232

def compactCertificate205 : CompactCertificate where
  left := 1479 / 16
  right := 2959 / 32
  center := 5917 / 64
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
    | 0 => 5917 / 64
    | 1 => 8716870838730217 / 128000000000000
    | 2 => 2818856929831561 / 25600000000000
    | 3 => 2543561170556219 / 128000000000000
    | 4 => 6832363085588543 / 128000000000000
    | 5 => 18551194861273731 / 128000000000000
    | 6 => 13664726171183003 / 128000000000000
    | 7 => 23414741202118919 / 128000000000000
    | 8 => 17247192393190421 / 128000000000000
    | 9 => 26461628445729083 / 128000000000000
    | 10 => 15277628306335907 / 128000000000000
    | 11 => 27110419526358463 / 128000000000000
    | 12 => 25330070592651547 / 128000000000000
    | 13 => 18076733591363851 / 128000000000000
    | 14 => 20497089256765629 / 128000000000000
    | 15 => 17088336093313901 / 128000000000000
    | 16 => 15098063175683921 / 128000000000000
    | 17 => 4376007183592179 / 25600000000000
    | 18 => 12104266166456713 / 128000000000000
    | 19 => 10260920480382593 / 128000000000000
    | 20 => 6420807606809579 / 128000000000000
    | 21 => 3453131685583893 / 128000000000000
    | 22 => 9375924256150679 / 128000000000000
    | 23 => 12802022999353783 / 128000000000000
    | 24 => 5413192393190421 / 128000000000000
    | 25 => 22004326546863541 / 128000000000000
    | _ => 14697870363394619 / 128000000000000
  state := fun i =>
    match i.val with
    | 0 => (orderedInterval (-70297386043 / 1000000000000) (-70297362130 / 1000000000000), orderedInterval (44472111446 / 1000000000000) (44472135359 / 1000000000000))
    | 1 => (orderedInterval (-22128792621 / 1000000000000) (-22128792374 / 1000000000000), orderedInterval (94283523061 / 1000000000000) (94283523307 / 1000000000000))
    | 2 => (orderedInterval (-61409108022 / 1000000000000) (-61409108021 / 1000000000000), orderedInterval (-44559646040 / 1000000000000) (-44559646039 / 1000000000000))
    | 3 => (orderedInterval (174233452669 / 1000000000000) (174233453151 / 1000000000000), orderedInterval (-45251370276 / 1000000000000) (-45251369794 / 1000000000000))
    | 4 => (orderedInterval (-74744210859 / 1000000000000) (-74744210858 / 1000000000000), orderedInterval (-78924064748 / 1000000000000) (-78924064747 / 1000000000000))
    | 5 => (orderedInterval (61831491174 / 1000000000000) (61831491175 / 1000000000000), orderedInterval (23649053486 / 1000000000000) (23649053487 / 1000000000000))
    | 6 => (orderedInterval (51252135141 / 1000000000000) (51252135142 / 1000000000000), orderedInterval (57522931758 / 1000000000000) (57522931759 / 1000000000000))
    | 7 => (orderedInterval (58845123449 / 1000000000000) (58845123470 / 1000000000000), orderedInterval (4011777963 / 1000000000000) (4011777984 / 1000000000000))
    | 8 => (orderedInterval (-29257290846 / 1000000000000) (-29257290845 / 1000000000000), orderedInterval (-62090340956 / 1000000000000) (-62090340955 / 1000000000000))
    | 9 => (orderedInterval (9451315445 / 1000000000000) (9451315446 / 1000000000000), orderedInterval (54659256513 / 1000000000000) (54659256514 / 1000000000000))
    | 10 => (orderedInterval (50329483576 / 1000000000000) (50329483577 / 1000000000000), orderedInterval (52710937575 / 1000000000000) (52710937576 / 1000000000000))
    | 11 => (orderedInterval (-47373503860 / 1000000000000) (-47373473162 / 1000000000000), orderedInterval (27707204459 / 1000000000000) (27707235158 / 1000000000000))
    | 12 => (orderedInterval (-38893690190 / 1000000000000) (-38893690189 / 1000000000000), orderedInterval (-41184910437 / 1000000000000) (-41184910436 / 1000000000000))
    | 13 => (orderedInterval (-39951712118 / 1000000000000) (-39951712117 / 1000000000000), orderedInterval (-53818965533 / 1000000000000) (-53818965532 / 1000000000000))
    | 14 => (orderedInterval (-40469530730 / 1000000000000) (-40469530729 / 1000000000000), orderedInterval (-48224200122 / 1000000000000) (-48224200121 / 1000000000000))
    | 15 => (orderedInterval (49603954472 / 1000000000000) (49604027076 / 1000000000000), orderedInterval (-48227839515 / 1000000000000) (-48227766911 / 1000000000000))
    | 16 => (orderedInterval (-44024104684 / 1000000000000) (-44024086097 / 1000000000000), orderedInterval (59000690659 / 1000000000000) (59000709246 / 1000000000000))
    | 17 => (orderedInterval (53389885156 / 1000000000000) (53389905863 / 1000000000000), orderedInterval (-29716086583 / 1000000000000) (-29716065876 / 1000000000000))
    | 18 => (orderedInterval (73155168154 / 1000000000000) (73155168155 / 1000000000000), orderedInterval (36766709153 / 1000000000000) (36766709154 / 1000000000000))
    | 19 => (orderedInterval (-59701346792 / 1000000000000) (-59701295856 / 1000000000000), orderedInterval (66533424948 / 1000000000000) (66533475884 / 1000000000000))
    | 20 => (orderedInterval (70833455031 / 1000000000000) (70833455032 / 1000000000000), orderedInterval (86894759797 / 1000000000000) (86894759798 / 1000000000000))
    | 21 => (orderedInterval (75785347141 / 1000000000000) (75785355291 / 1000000000000), orderedInterval (-135033277701 / 1000000000000) (-135033269551 / 1000000000000))
    | 22 => (orderedInterval (-91260289182 / 1000000000000) (-91260288712 / 1000000000000), orderedInterval (19662326055 / 1000000000000) (19662326524 / 1000000000000))
    | 23 => (orderedInterval (21202465071 / 1000000000000) (21202465072 / 1000000000000), orderedInterval (76807695675 / 1000000000000) (76807695676 / 1000000000000))
    | 24 => (orderedInterval (-96809279696 / 1000000000000) (-96809231384 / 1000000000000), orderedInterval (76517990989 / 1000000000000) (76518039302 / 1000000000000))
    | 25 => (orderedInterval (5719365867 / 1000000000000) (5719365883 / 1000000000000), orderedInterval (-60601662117 / 1000000000000) (-60601662101 / 1000000000000))
    | _ => (orderedInterval (43716812045 / 1000000000000) (43716828383 / 1000000000000), orderedInterval (-60464860192 / 1000000000000) (-60464843855 / 1000000000000))
  chunkTarget := fun r b =>
    match r.val with
    | 0 =>
      match b.val with
      | 0 => orderedInterval (-31673176813 / 1000000000000) (-31673167325 / 1000000000000)
      | 1 => orderedInterval (-9014929593 / 1000000000000) (-9014929576 / 1000000000000)
      | 2 => orderedInterval (-2522110045 / 1000000000000) (-2522110039 / 1000000000000)
      | 3 => orderedInterval (-4684806785 / 1000000000000) (-4684802383 / 1000000000000)
      | 4 => orderedInterval (-2870998136 / 1000000000000) (-2870998124 / 1000000000000)
      | 5 => orderedInterval (4459154197 / 1000000000000) (4459156639 / 1000000000000)
      | 6 => orderedInterval (-6011865450 / 1000000000000) (-6011862543 / 1000000000000)
      | 7 => orderedInterval (-953908847 / 1000000000000) (-953908673 / 1000000000000)
      | _ => orderedInterval (-9251601332 / 1000000000000) (-9251597947 / 1000000000000)
    | 1 =>
      match b.val with
      | 0 => orderedInterval (15160078746 / 1000000000000) (15160088234 / 1000000000000)
      | 1 => orderedInterval (-4193686501 / 1000000000000) (-4193686486 / 1000000000000)
      | 2 => orderedInterval (-2431847064 / 1000000000000) (-2431847053 / 1000000000000)
      | 3 => orderedInterval (-7652195930 / 1000000000000) (-7652185856 / 1000000000000)
      | 4 => orderedInterval (-5759848218 / 1000000000000) (-5759848199 / 1000000000000)
      | 5 => orderedInterval (-6518636956 / 1000000000000) (-6518633394 / 1000000000000)
      | 6 => orderedInterval (-7743312393 / 1000000000000) (-7743309870 / 1000000000000)
      | 7 => orderedInterval (-5993819127 / 1000000000000) (-5993819064 / 1000000000000)
      | _ => orderedInterval (23473945318 / 1000000000000) (23473949297 / 1000000000000)
    | 2 =>
      match b.val with
      | 0 => orderedInterval (32922884226 / 1000000000000) (32922893817 / 1000000000000)
      | 1 => orderedInterval (11844182587 / 1000000000000) (11844182606 / 1000000000000)
      | 2 => orderedInterval (8633766106 / 1000000000000) (8633766125 / 1000000000000)
      | 3 => orderedInterval (37608180891 / 1000000000000) (37608204067 / 1000000000000)
      | 4 => orderedInterval (5046195627 / 1000000000000) (5046195658 / 1000000000000)
      | 5 => orderedInterval (-9897720410 / 1000000000000) (-9897715060 / 1000000000000)
      | 6 => orderedInterval (9101788127 / 1000000000000) (9101790343 / 1000000000000)
      | 7 => orderedInterval (785993234 / 1000000000000) (785993264 / 1000000000000)
      | _ => orderedInterval (14130724767 / 1000000000000) (14130729658 / 1000000000000)
    | 3 =>
      match b.val with
      | 0 => orderedInterval (-13915160842 / 1000000000000) (-13915151252 / 1000000000000)
      | 1 => orderedInterval (6897609335 / 1000000000000) (6897609363 / 1000000000000)
      | 2 => orderedInterval (5510233986 / 1000000000000) (5510234021 / 1000000000000)
      | 3 => orderedInterval (52420162545 / 1000000000000) (52420215619 / 1000000000000)
      | 4 => orderedInterval (9524705397 / 1000000000000) (9524705449 / 1000000000000)
      | 5 => orderedInterval (13603794104 / 1000000000000) (13603802275 / 1000000000000)
      | 6 => orderedInterval (8194389158 / 1000000000000) (8194391081 / 1000000000000)
      | 7 => orderedInterval (7603075633 / 1000000000000) (7603075653 / 1000000000000)
      | _ => orderedInterval (-53643332451 / 1000000000000) (-53643326408 / 1000000000000)
    | _ =>
      match b.val with
      | 0 => orderedInterval (-34869925942 / 1000000000000) (-34869916249 / 1000000000000)
      | 1 => orderedInterval (-26999753376 / 1000000000000) (-26999753334 / 1000000000000)
      | 2 => orderedInterval (-31125556014 / 1000000000000) (-31125555949 / 1000000000000)
      | 3 => orderedInterval (-218245243347 / 1000000000000) (-218245121225 / 1000000000000)
      | 4 => orderedInterval (-4192697800 / 1000000000000) (-4192697711 / 1000000000000)
      | 5 => orderedInterval (24844657845 / 1000000000000) (24844670724 / 1000000000000)
      | 6 => orderedInterval (-10869080408 / 1000000000000) (-10869078717 / 1000000000000)
      | 7 => orderedInterval (-1584194417 / 1000000000000) (-1584194400 / 1000000000000)
      | _ => orderedInterval (-23946727249 / 1000000000000) (-23946719668 / 1000000000000)
  coefficientTarget := fun i =>
    match i.val with
    | 0 => orderedInterval (-62524242804 / 1000000000000) (-62524219971 / 1000000000000)
    | 1 => orderedInterval (-1659322125 / 1000000000000) (-1659292391 / 1000000000000)
    | 2 => orderedInterval (110175995155 / 1000000000000) (110176040478 / 1000000000000)
    | 3 => orderedInterval (36195476865 / 1000000000000) (36195555801 / 1000000000000)
    | _ => orderedInterval (-326988520708 / 1000000000000) (-326988366529 / 1000000000000)

theorem compactCertificate205_stateChecks0 :
    compactCertificate205.stateChecks 0 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 29 12 (5917 / 64)) (orderedInterval (-70297386043 / 1000000000000) (-70297362130 / 1000000000000), orderedInterval (44472111446 / 1000000000000) (44472135359 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 22 12 (8716870838730217 / 128000000000000)) (orderedInterval (-22128792621 / 1000000000000) (-22128792374 / 1000000000000), orderedInterval (94283523061 / 1000000000000) (94283523307 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 35 12 (2818856929831561 / 25600000000000)) (orderedInterval (-61409108022 / 1000000000000) (-61409108021 / 1000000000000), orderedInterval (-44559646040 / 1000000000000) (-44559646039 / 1000000000000))) = true
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

theorem compactCertificate205_stateChecks1 :
    compactCertificate205.stateChecks 3 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 6 12 (2543561170556219 / 128000000000000)) (orderedInterval (174233452669 / 1000000000000) (174233453151 / 1000000000000), orderedInterval (-45251370276 / 1000000000000) (-45251369794 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 17 12 (6832363085588543 / 128000000000000)) (orderedInterval (-74744210859 / 1000000000000) (-74744210858 / 1000000000000), orderedInterval (-78924064748 / 1000000000000) (-78924064747 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 46 12 (18551194861273731 / 128000000000000)) (orderedInterval (61831491174 / 1000000000000) (61831491175 / 1000000000000), orderedInterval (23649053486 / 1000000000000) (23649053487 / 1000000000000))) = true
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

theorem compactCertificate205_stateChecks2 :
    compactCertificate205.stateChecks 6 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 34 12 (13664726171183003 / 128000000000000)) (orderedInterval (51252135141 / 1000000000000) (51252135142 / 1000000000000), orderedInterval (57522931758 / 1000000000000) (57522931759 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 58 12 (23414741202118919 / 128000000000000)) (orderedInterval (58845123449 / 1000000000000) (58845123470 / 1000000000000), orderedInterval (4011777963 / 1000000000000) (4011777984 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 43 12 (17247192393190421 / 128000000000000)) (orderedInterval (-29257290846 / 1000000000000) (-29257290845 / 1000000000000), orderedInterval (-62090340956 / 1000000000000) (-62090340955 / 1000000000000))) = true
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

theorem compactCertificate205_stateChecks3 :
    compactCertificate205.stateChecks 9 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 66 12 (26461628445729083 / 128000000000000)) (orderedInterval (9451315445 / 1000000000000) (9451315446 / 1000000000000), orderedInterval (54659256513 / 1000000000000) (54659256514 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 38 12 (15277628306335907 / 128000000000000)) (orderedInterval (50329483576 / 1000000000000) (50329483577 / 1000000000000), orderedInterval (52710937575 / 1000000000000) (52710937576 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 67 12 (27110419526358463 / 128000000000000)) (orderedInterval (-47373503860 / 1000000000000) (-47373473162 / 1000000000000), orderedInterval (27707204459 / 1000000000000) (27707235158 / 1000000000000))) = true
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

theorem compactCertificate205_stateChecks4 :
    compactCertificate205.stateChecks 12 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 63 12 (25330070592651547 / 128000000000000)) (orderedInterval (-38893690190 / 1000000000000) (-38893690189 / 1000000000000), orderedInterval (-41184910437 / 1000000000000) (-41184910436 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 45 12 (18076733591363851 / 128000000000000)) (orderedInterval (-39951712118 / 1000000000000) (-39951712117 / 1000000000000), orderedInterval (-53818965533 / 1000000000000) (-53818965532 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 51 12 (20497089256765629 / 128000000000000)) (orderedInterval (-40469530730 / 1000000000000) (-40469530729 / 1000000000000), orderedInterval (-48224200122 / 1000000000000) (-48224200121 / 1000000000000))) = true
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

theorem compactCertificate205_stateChecks5 :
    compactCertificate205.stateChecks 15 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 43 12 (17088336093313901 / 128000000000000)) (orderedInterval (49603954472 / 1000000000000) (49604027076 / 1000000000000), orderedInterval (-48227839515 / 1000000000000) (-48227766911 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 38 12 (15098063175683921 / 128000000000000)) (orderedInterval (-44024104684 / 1000000000000) (-44024086097 / 1000000000000), orderedInterval (59000690659 / 1000000000000) (59000709246 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 54 12 (4376007183592179 / 25600000000000)) (orderedInterval (53389885156 / 1000000000000) (53389905863 / 1000000000000), orderedInterval (-29716086583 / 1000000000000) (-29716065876 / 1000000000000))) = true
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

theorem compactCertificate205_stateChecks6 :
    compactCertificate205.stateChecks 18 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 30 12 (12104266166456713 / 128000000000000)) (orderedInterval (73155168154 / 1000000000000) (73155168155 / 1000000000000), orderedInterval (36766709153 / 1000000000000) (36766709154 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 26 12 (10260920480382593 / 128000000000000)) (orderedInterval (-59701346792 / 1000000000000) (-59701295856 / 1000000000000), orderedInterval (66533424948 / 1000000000000) (66533475884 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 16 12 (6420807606809579 / 128000000000000)) (orderedInterval (70833455031 / 1000000000000) (70833455032 / 1000000000000), orderedInterval (86894759797 / 1000000000000) (86894759798 / 1000000000000))) = true
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

theorem compactCertificate205_stateChecks7 :
    compactCertificate205.stateChecks 21 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 9 12 (3453131685583893 / 128000000000000)) (orderedInterval (75785347141 / 1000000000000) (75785355291 / 1000000000000), orderedInterval (-135033277701 / 1000000000000) (-135033269551 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 23 12 (9375924256150679 / 128000000000000)) (orderedInterval (-91260289182 / 1000000000000) (-91260288712 / 1000000000000), orderedInterval (19662326055 / 1000000000000) (19662326524 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 32 12 (12802022999353783 / 128000000000000)) (orderedInterval (21202465071 / 1000000000000) (21202465072 / 1000000000000), orderedInterval (76807695675 / 1000000000000) (76807695676 / 1000000000000))) = true
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

theorem compactCertificate205_stateChecks8 :
    compactCertificate205.stateChecks 24 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 13 12 (5413192393190421 / 128000000000000)) (orderedInterval (-96809279696 / 1000000000000) (-96809231384 / 1000000000000), orderedInterval (76517990989 / 1000000000000) (76518039302 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 55 12 (22004326546863541 / 128000000000000)) (orderedInterval (5719365867 / 1000000000000) (5719365883 / 1000000000000), orderedInterval (-60601662117 / 1000000000000) (-60601662101 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 37 12 (14697870363394619 / 128000000000000)) (orderedInterval (43716812045 / 1000000000000) (43716828383 / 1000000000000), orderedInterval (-60464860192 / 1000000000000) (-60464843855 / 1000000000000))) = true
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

theorem compactCertificate205_states : ∀ j,
    BesselStateValid (compactCertificate205.point j) (compactCertificate205.state j) :=
  compactCertificate205.statesValid_of_checks3 compactCertificate205_stateChecks0
    compactCertificate205_stateChecks1 compactCertificate205_stateChecks2
    compactCertificate205_stateChecks3 compactCertificate205_stateChecks4
    compactCertificate205_stateChecks5 compactCertificate205_stateChecks6
    compactCertificate205_stateChecks7 compactCertificate205_stateChecks8

theorem compactCertificate205_chunkChecks0_0 :
    compactCertificate205.chunkChecks (0 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 0) <| besselDerivativeNearFromState (5917 / 64) 0 (IntervalRat.scale (5917 / 64) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-70297386043 / 1000000000000) (-70297362130 / 1000000000000), orderedInterval (44472111446 / 1000000000000) (44472135359 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 0) <| besselDerivativeNearFromState (8716870838730217 / 128000000000000) 0 (IntervalRat.scale (5917 / 64) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-22128792621 / 1000000000000) (-22128792374 / 1000000000000), orderedInterval (94283523061 / 1000000000000) (94283523307 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 0) <| besselDerivativeNearFromState (2818856929831561 / 25600000000000) 0 (IntervalRat.scale (5917 / 64) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-61409108022 / 1000000000000) (-61409108021 / 1000000000000), orderedInterval (-44559646040 / 1000000000000) (-44559646039 / 1000000000000)))) (orderedInterval (-31673176813 / 1000000000000) (-31673167325 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 0) <| besselDerivativeNearFromState (2543561170556219 / 128000000000000) 0 (IntervalRat.scale (5917 / 64) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (174233452669 / 1000000000000) (174233453151 / 1000000000000), orderedInterval (-45251370276 / 1000000000000) (-45251369794 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 0) <| besselDerivativeNearFromState (6832363085588543 / 128000000000000) 0 (IntervalRat.scale (5917 / 64) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-74744210859 / 1000000000000) (-74744210858 / 1000000000000), orderedInterval (-78924064748 / 1000000000000) (-78924064747 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 0) <| besselDerivativeNearFromState (18551194861273731 / 128000000000000) 0 (IntervalRat.scale (5917 / 64) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (61831491174 / 1000000000000) (61831491175 / 1000000000000), orderedInterval (23649053486 / 1000000000000) (23649053487 / 1000000000000)))) (orderedInterval (-9014929593 / 1000000000000) (-9014929576 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 0) <| besselDerivativeNearFromState (13664726171183003 / 128000000000000) 0 (IntervalRat.scale (5917 / 64) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (51252135141 / 1000000000000) (51252135142 / 1000000000000), orderedInterval (57522931758 / 1000000000000) (57522931759 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 0) <| besselDerivativeNearFromState (23414741202118919 / 128000000000000) 0 (IntervalRat.scale (5917 / 64) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (58845123449 / 1000000000000) (58845123470 / 1000000000000), orderedInterval (4011777963 / 1000000000000) (4011777984 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 0) <| besselDerivativeNearFromState (17247192393190421 / 128000000000000) 0 (IntervalRat.scale (5917 / 64) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-29257290846 / 1000000000000) (-29257290845 / 1000000000000), orderedInterval (-62090340956 / 1000000000000) (-62090340955 / 1000000000000)))) (orderedInterval (-2522110045 / 1000000000000) (-2522110039 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate205_chunkChecks0_1 :
    compactCertificate205.chunkChecks (0 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 0) <| besselDerivativeNearFromState (26461628445729083 / 128000000000000) 0 (IntervalRat.scale (5917 / 64) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (9451315445 / 1000000000000) (9451315446 / 1000000000000), orderedInterval (54659256513 / 1000000000000) (54659256514 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 0) <| besselDerivativeNearFromState (15277628306335907 / 128000000000000) 0 (IntervalRat.scale (5917 / 64) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (50329483576 / 1000000000000) (50329483577 / 1000000000000), orderedInterval (52710937575 / 1000000000000) (52710937576 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 0) <| besselDerivativeNearFromState (27110419526358463 / 128000000000000) 0 (IntervalRat.scale (5917 / 64) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-47373503860 / 1000000000000) (-47373473162 / 1000000000000), orderedInterval (27707204459 / 1000000000000) (27707235158 / 1000000000000)))) (orderedInterval (-4684806785 / 1000000000000) (-4684802383 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 0) <| besselDerivativeNearFromState (25330070592651547 / 128000000000000) 0 (IntervalRat.scale (5917 / 64) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-38893690190 / 1000000000000) (-38893690189 / 1000000000000), orderedInterval (-41184910437 / 1000000000000) (-41184910436 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 0) <| besselDerivativeNearFromState (18076733591363851 / 128000000000000) 0 (IntervalRat.scale (5917 / 64) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-39951712118 / 1000000000000) (-39951712117 / 1000000000000), orderedInterval (-53818965533 / 1000000000000) (-53818965532 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 0) <| besselDerivativeNearFromState (20497089256765629 / 128000000000000) 0 (IntervalRat.scale (5917 / 64) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-40469530730 / 1000000000000) (-40469530729 / 1000000000000), orderedInterval (-48224200122 / 1000000000000) (-48224200121 / 1000000000000)))) (orderedInterval (-2870998136 / 1000000000000) (-2870998124 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 0) <| besselDerivativeNearFromState (17088336093313901 / 128000000000000) 0 (IntervalRat.scale (5917 / 64) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (49603954472 / 1000000000000) (49604027076 / 1000000000000), orderedInterval (-48227839515 / 1000000000000) (-48227766911 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 0) <| besselDerivativeNearFromState (15098063175683921 / 128000000000000) 0 (IntervalRat.scale (5917 / 64) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-44024104684 / 1000000000000) (-44024086097 / 1000000000000), orderedInterval (59000690659 / 1000000000000) (59000709246 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 0) <| besselDerivativeNearFromState (4376007183592179 / 25600000000000) 0 (IntervalRat.scale (5917 / 64) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (53389885156 / 1000000000000) (53389905863 / 1000000000000), orderedInterval (-29716086583 / 1000000000000) (-29716065876 / 1000000000000)))) (orderedInterval (4459154197 / 1000000000000) (4459156639 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate205_chunkChecks0_2 :
    compactCertificate205.chunkChecks (0 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 0) <| besselDerivativeNearFromState (12104266166456713 / 128000000000000) 0 (IntervalRat.scale (5917 / 64) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (73155168154 / 1000000000000) (73155168155 / 1000000000000), orderedInterval (36766709153 / 1000000000000) (36766709154 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 0) <| besselDerivativeNearFromState (10260920480382593 / 128000000000000) 0 (IntervalRat.scale (5917 / 64) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-59701346792 / 1000000000000) (-59701295856 / 1000000000000), orderedInterval (66533424948 / 1000000000000) (66533475884 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 0) <| besselDerivativeNearFromState (6420807606809579 / 128000000000000) 0 (IntervalRat.scale (5917 / 64) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (70833455031 / 1000000000000) (70833455032 / 1000000000000), orderedInterval (86894759797 / 1000000000000) (86894759798 / 1000000000000)))) (orderedInterval (-6011865450 / 1000000000000) (-6011862543 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 0) <| besselDerivativeNearFromState (3453131685583893 / 128000000000000) 0 (IntervalRat.scale (5917 / 64) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (75785347141 / 1000000000000) (75785355291 / 1000000000000), orderedInterval (-135033277701 / 1000000000000) (-135033269551 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 0) <| besselDerivativeNearFromState (9375924256150679 / 128000000000000) 0 (IntervalRat.scale (5917 / 64) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-91260289182 / 1000000000000) (-91260288712 / 1000000000000), orderedInterval (19662326055 / 1000000000000) (19662326524 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 0) <| besselDerivativeNearFromState (12802022999353783 / 128000000000000) 0 (IntervalRat.scale (5917 / 64) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (21202465071 / 1000000000000) (21202465072 / 1000000000000), orderedInterval (76807695675 / 1000000000000) (76807695676 / 1000000000000)))) (orderedInterval (-953908847 / 1000000000000) (-953908673 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 0) <| besselDerivativeNearFromState (5413192393190421 / 128000000000000) 0 (IntervalRat.scale (5917 / 64) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-96809279696 / 1000000000000) (-96809231384 / 1000000000000), orderedInterval (76517990989 / 1000000000000) (76518039302 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 0) <| besselDerivativeNearFromState (22004326546863541 / 128000000000000) 0 (IntervalRat.scale (5917 / 64) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (5719365867 / 1000000000000) (5719365883 / 1000000000000), orderedInterval (-60601662117 / 1000000000000) (-60601662101 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 0) <| besselDerivativeNearFromState (14697870363394619 / 128000000000000) 0 (IntervalRat.scale (5917 / 64) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (43716812045 / 1000000000000) (43716828383 / 1000000000000), orderedInterval (-60464860192 / 1000000000000) (-60464843855 / 1000000000000)))) (orderedInterval (-9251601332 / 1000000000000) (-9251597947 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate205_chunkChecks0 :
    compactCertificate205.chunkChecks (0 : Fin 5) 0 9 = true :=
  compactCertificate205.chunkChecks_nine_of_three (0 : Fin 5) compactCertificate205_chunkChecks0_0
    compactCertificate205_chunkChecks0_1 compactCertificate205_chunkChecks0_2

theorem compactCertificate205_chunkChecks1_0 :
    compactCertificate205.chunkChecks (1 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 1) <| besselDerivativeNearFromState (5917 / 64) 1 (IntervalRat.scale (5917 / 64) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-70297386043 / 1000000000000) (-70297362130 / 1000000000000), orderedInterval (44472111446 / 1000000000000) (44472135359 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 1) <| besselDerivativeNearFromState (8716870838730217 / 128000000000000) 1 (IntervalRat.scale (5917 / 64) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-22128792621 / 1000000000000) (-22128792374 / 1000000000000), orderedInterval (94283523061 / 1000000000000) (94283523307 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 1) <| besselDerivativeNearFromState (2818856929831561 / 25600000000000) 1 (IntervalRat.scale (5917 / 64) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-61409108022 / 1000000000000) (-61409108021 / 1000000000000), orderedInterval (-44559646040 / 1000000000000) (-44559646039 / 1000000000000)))) (orderedInterval (15160078746 / 1000000000000) (15160088234 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 1) <| besselDerivativeNearFromState (2543561170556219 / 128000000000000) 1 (IntervalRat.scale (5917 / 64) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (174233452669 / 1000000000000) (174233453151 / 1000000000000), orderedInterval (-45251370276 / 1000000000000) (-45251369794 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 1) <| besselDerivativeNearFromState (6832363085588543 / 128000000000000) 1 (IntervalRat.scale (5917 / 64) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-74744210859 / 1000000000000) (-74744210858 / 1000000000000), orderedInterval (-78924064748 / 1000000000000) (-78924064747 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 1) <| besselDerivativeNearFromState (18551194861273731 / 128000000000000) 1 (IntervalRat.scale (5917 / 64) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (61831491174 / 1000000000000) (61831491175 / 1000000000000), orderedInterval (23649053486 / 1000000000000) (23649053487 / 1000000000000)))) (orderedInterval (-4193686501 / 1000000000000) (-4193686486 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 1) <| besselDerivativeNearFromState (13664726171183003 / 128000000000000) 1 (IntervalRat.scale (5917 / 64) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (51252135141 / 1000000000000) (51252135142 / 1000000000000), orderedInterval (57522931758 / 1000000000000) (57522931759 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 1) <| besselDerivativeNearFromState (23414741202118919 / 128000000000000) 1 (IntervalRat.scale (5917 / 64) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (58845123449 / 1000000000000) (58845123470 / 1000000000000), orderedInterval (4011777963 / 1000000000000) (4011777984 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 1) <| besselDerivativeNearFromState (17247192393190421 / 128000000000000) 1 (IntervalRat.scale (5917 / 64) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-29257290846 / 1000000000000) (-29257290845 / 1000000000000), orderedInterval (-62090340956 / 1000000000000) (-62090340955 / 1000000000000)))) (orderedInterval (-2431847064 / 1000000000000) (-2431847053 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate205_chunkChecks1_1 :
    compactCertificate205.chunkChecks (1 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 1) <| besselDerivativeNearFromState (26461628445729083 / 128000000000000) 1 (IntervalRat.scale (5917 / 64) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (9451315445 / 1000000000000) (9451315446 / 1000000000000), orderedInterval (54659256513 / 1000000000000) (54659256514 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 1) <| besselDerivativeNearFromState (15277628306335907 / 128000000000000) 1 (IntervalRat.scale (5917 / 64) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (50329483576 / 1000000000000) (50329483577 / 1000000000000), orderedInterval (52710937575 / 1000000000000) (52710937576 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 1) <| besselDerivativeNearFromState (27110419526358463 / 128000000000000) 1 (IntervalRat.scale (5917 / 64) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-47373503860 / 1000000000000) (-47373473162 / 1000000000000), orderedInterval (27707204459 / 1000000000000) (27707235158 / 1000000000000)))) (orderedInterval (-7652195930 / 1000000000000) (-7652185856 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 1) <| besselDerivativeNearFromState (25330070592651547 / 128000000000000) 1 (IntervalRat.scale (5917 / 64) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-38893690190 / 1000000000000) (-38893690189 / 1000000000000), orderedInterval (-41184910437 / 1000000000000) (-41184910436 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 1) <| besselDerivativeNearFromState (18076733591363851 / 128000000000000) 1 (IntervalRat.scale (5917 / 64) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-39951712118 / 1000000000000) (-39951712117 / 1000000000000), orderedInterval (-53818965533 / 1000000000000) (-53818965532 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 1) <| besselDerivativeNearFromState (20497089256765629 / 128000000000000) 1 (IntervalRat.scale (5917 / 64) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-40469530730 / 1000000000000) (-40469530729 / 1000000000000), orderedInterval (-48224200122 / 1000000000000) (-48224200121 / 1000000000000)))) (orderedInterval (-5759848218 / 1000000000000) (-5759848199 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 1) <| besselDerivativeNearFromState (17088336093313901 / 128000000000000) 1 (IntervalRat.scale (5917 / 64) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (49603954472 / 1000000000000) (49604027076 / 1000000000000), orderedInterval (-48227839515 / 1000000000000) (-48227766911 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 1) <| besselDerivativeNearFromState (15098063175683921 / 128000000000000) 1 (IntervalRat.scale (5917 / 64) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-44024104684 / 1000000000000) (-44024086097 / 1000000000000), orderedInterval (59000690659 / 1000000000000) (59000709246 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 1) <| besselDerivativeNearFromState (4376007183592179 / 25600000000000) 1 (IntervalRat.scale (5917 / 64) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (53389885156 / 1000000000000) (53389905863 / 1000000000000), orderedInterval (-29716086583 / 1000000000000) (-29716065876 / 1000000000000)))) (orderedInterval (-6518636956 / 1000000000000) (-6518633394 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate205_chunkChecks1_2 :
    compactCertificate205.chunkChecks (1 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 1) <| besselDerivativeNearFromState (12104266166456713 / 128000000000000) 1 (IntervalRat.scale (5917 / 64) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (73155168154 / 1000000000000) (73155168155 / 1000000000000), orderedInterval (36766709153 / 1000000000000) (36766709154 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 1) <| besselDerivativeNearFromState (10260920480382593 / 128000000000000) 1 (IntervalRat.scale (5917 / 64) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-59701346792 / 1000000000000) (-59701295856 / 1000000000000), orderedInterval (66533424948 / 1000000000000) (66533475884 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 1) <| besselDerivativeNearFromState (6420807606809579 / 128000000000000) 1 (IntervalRat.scale (5917 / 64) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (70833455031 / 1000000000000) (70833455032 / 1000000000000), orderedInterval (86894759797 / 1000000000000) (86894759798 / 1000000000000)))) (orderedInterval (-7743312393 / 1000000000000) (-7743309870 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 1) <| besselDerivativeNearFromState (3453131685583893 / 128000000000000) 1 (IntervalRat.scale (5917 / 64) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (75785347141 / 1000000000000) (75785355291 / 1000000000000), orderedInterval (-135033277701 / 1000000000000) (-135033269551 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 1) <| besselDerivativeNearFromState (9375924256150679 / 128000000000000) 1 (IntervalRat.scale (5917 / 64) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-91260289182 / 1000000000000) (-91260288712 / 1000000000000), orderedInterval (19662326055 / 1000000000000) (19662326524 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 1) <| besselDerivativeNearFromState (12802022999353783 / 128000000000000) 1 (IntervalRat.scale (5917 / 64) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (21202465071 / 1000000000000) (21202465072 / 1000000000000), orderedInterval (76807695675 / 1000000000000) (76807695676 / 1000000000000)))) (orderedInterval (-5993819127 / 1000000000000) (-5993819064 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 1) <| besselDerivativeNearFromState (5413192393190421 / 128000000000000) 1 (IntervalRat.scale (5917 / 64) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-96809279696 / 1000000000000) (-96809231384 / 1000000000000), orderedInterval (76517990989 / 1000000000000) (76518039302 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 1) <| besselDerivativeNearFromState (22004326546863541 / 128000000000000) 1 (IntervalRat.scale (5917 / 64) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (5719365867 / 1000000000000) (5719365883 / 1000000000000), orderedInterval (-60601662117 / 1000000000000) (-60601662101 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 1) <| besselDerivativeNearFromState (14697870363394619 / 128000000000000) 1 (IntervalRat.scale (5917 / 64) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (43716812045 / 1000000000000) (43716828383 / 1000000000000), orderedInterval (-60464860192 / 1000000000000) (-60464843855 / 1000000000000)))) (orderedInterval (23473945318 / 1000000000000) (23473949297 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate205_chunkChecks1 :
    compactCertificate205.chunkChecks (1 : Fin 5) 0 9 = true :=
  compactCertificate205.chunkChecks_nine_of_three (1 : Fin 5) compactCertificate205_chunkChecks1_0
    compactCertificate205_chunkChecks1_1 compactCertificate205_chunkChecks1_2

theorem compactCertificate205_chunkChecks2_0 :
    compactCertificate205.chunkChecks (2 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 2) <| besselDerivativeNearFromState (5917 / 64) 2 (IntervalRat.scale (5917 / 64) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-70297386043 / 1000000000000) (-70297362130 / 1000000000000), orderedInterval (44472111446 / 1000000000000) (44472135359 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 2) <| besselDerivativeNearFromState (8716870838730217 / 128000000000000) 2 (IntervalRat.scale (5917 / 64) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-22128792621 / 1000000000000) (-22128792374 / 1000000000000), orderedInterval (94283523061 / 1000000000000) (94283523307 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 2) <| besselDerivativeNearFromState (2818856929831561 / 25600000000000) 2 (IntervalRat.scale (5917 / 64) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-61409108022 / 1000000000000) (-61409108021 / 1000000000000), orderedInterval (-44559646040 / 1000000000000) (-44559646039 / 1000000000000)))) (orderedInterval (32922884226 / 1000000000000) (32922893817 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 2) <| besselDerivativeNearFromState (2543561170556219 / 128000000000000) 2 (IntervalRat.scale (5917 / 64) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (174233452669 / 1000000000000) (174233453151 / 1000000000000), orderedInterval (-45251370276 / 1000000000000) (-45251369794 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 2) <| besselDerivativeNearFromState (6832363085588543 / 128000000000000) 2 (IntervalRat.scale (5917 / 64) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-74744210859 / 1000000000000) (-74744210858 / 1000000000000), orderedInterval (-78924064748 / 1000000000000) (-78924064747 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 2) <| besselDerivativeNearFromState (18551194861273731 / 128000000000000) 2 (IntervalRat.scale (5917 / 64) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (61831491174 / 1000000000000) (61831491175 / 1000000000000), orderedInterval (23649053486 / 1000000000000) (23649053487 / 1000000000000)))) (orderedInterval (11844182587 / 1000000000000) (11844182606 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 2) <| besselDerivativeNearFromState (13664726171183003 / 128000000000000) 2 (IntervalRat.scale (5917 / 64) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (51252135141 / 1000000000000) (51252135142 / 1000000000000), orderedInterval (57522931758 / 1000000000000) (57522931759 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 2) <| besselDerivativeNearFromState (23414741202118919 / 128000000000000) 2 (IntervalRat.scale (5917 / 64) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (58845123449 / 1000000000000) (58845123470 / 1000000000000), orderedInterval (4011777963 / 1000000000000) (4011777984 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 2) <| besselDerivativeNearFromState (17247192393190421 / 128000000000000) 2 (IntervalRat.scale (5917 / 64) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-29257290846 / 1000000000000) (-29257290845 / 1000000000000), orderedInterval (-62090340956 / 1000000000000) (-62090340955 / 1000000000000)))) (orderedInterval (8633766106 / 1000000000000) (8633766125 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate205_chunkChecks2_1 :
    compactCertificate205.chunkChecks (2 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 2) <| besselDerivativeNearFromState (26461628445729083 / 128000000000000) 2 (IntervalRat.scale (5917 / 64) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (9451315445 / 1000000000000) (9451315446 / 1000000000000), orderedInterval (54659256513 / 1000000000000) (54659256514 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 2) <| besselDerivativeNearFromState (15277628306335907 / 128000000000000) 2 (IntervalRat.scale (5917 / 64) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (50329483576 / 1000000000000) (50329483577 / 1000000000000), orderedInterval (52710937575 / 1000000000000) (52710937576 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 2) <| besselDerivativeNearFromState (27110419526358463 / 128000000000000) 2 (IntervalRat.scale (5917 / 64) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-47373503860 / 1000000000000) (-47373473162 / 1000000000000), orderedInterval (27707204459 / 1000000000000) (27707235158 / 1000000000000)))) (orderedInterval (37608180891 / 1000000000000) (37608204067 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 2) <| besselDerivativeNearFromState (25330070592651547 / 128000000000000) 2 (IntervalRat.scale (5917 / 64) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-38893690190 / 1000000000000) (-38893690189 / 1000000000000), orderedInterval (-41184910437 / 1000000000000) (-41184910436 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 2) <| besselDerivativeNearFromState (18076733591363851 / 128000000000000) 2 (IntervalRat.scale (5917 / 64) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-39951712118 / 1000000000000) (-39951712117 / 1000000000000), orderedInterval (-53818965533 / 1000000000000) (-53818965532 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 2) <| besselDerivativeNearFromState (20497089256765629 / 128000000000000) 2 (IntervalRat.scale (5917 / 64) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-40469530730 / 1000000000000) (-40469530729 / 1000000000000), orderedInterval (-48224200122 / 1000000000000) (-48224200121 / 1000000000000)))) (orderedInterval (5046195627 / 1000000000000) (5046195658 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 2) <| besselDerivativeNearFromState (17088336093313901 / 128000000000000) 2 (IntervalRat.scale (5917 / 64) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (49603954472 / 1000000000000) (49604027076 / 1000000000000), orderedInterval (-48227839515 / 1000000000000) (-48227766911 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 2) <| besselDerivativeNearFromState (15098063175683921 / 128000000000000) 2 (IntervalRat.scale (5917 / 64) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-44024104684 / 1000000000000) (-44024086097 / 1000000000000), orderedInterval (59000690659 / 1000000000000) (59000709246 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 2) <| besselDerivativeNearFromState (4376007183592179 / 25600000000000) 2 (IntervalRat.scale (5917 / 64) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (53389885156 / 1000000000000) (53389905863 / 1000000000000), orderedInterval (-29716086583 / 1000000000000) (-29716065876 / 1000000000000)))) (orderedInterval (-9897720410 / 1000000000000) (-9897715060 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate205_chunkChecks2_2 :
    compactCertificate205.chunkChecks (2 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 2) <| besselDerivativeNearFromState (12104266166456713 / 128000000000000) 2 (IntervalRat.scale (5917 / 64) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (73155168154 / 1000000000000) (73155168155 / 1000000000000), orderedInterval (36766709153 / 1000000000000) (36766709154 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 2) <| besselDerivativeNearFromState (10260920480382593 / 128000000000000) 2 (IntervalRat.scale (5917 / 64) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-59701346792 / 1000000000000) (-59701295856 / 1000000000000), orderedInterval (66533424948 / 1000000000000) (66533475884 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 2) <| besselDerivativeNearFromState (6420807606809579 / 128000000000000) 2 (IntervalRat.scale (5917 / 64) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (70833455031 / 1000000000000) (70833455032 / 1000000000000), orderedInterval (86894759797 / 1000000000000) (86894759798 / 1000000000000)))) (orderedInterval (9101788127 / 1000000000000) (9101790343 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 2) <| besselDerivativeNearFromState (3453131685583893 / 128000000000000) 2 (IntervalRat.scale (5917 / 64) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (75785347141 / 1000000000000) (75785355291 / 1000000000000), orderedInterval (-135033277701 / 1000000000000) (-135033269551 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 2) <| besselDerivativeNearFromState (9375924256150679 / 128000000000000) 2 (IntervalRat.scale (5917 / 64) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-91260289182 / 1000000000000) (-91260288712 / 1000000000000), orderedInterval (19662326055 / 1000000000000) (19662326524 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 2) <| besselDerivativeNearFromState (12802022999353783 / 128000000000000) 2 (IntervalRat.scale (5917 / 64) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (21202465071 / 1000000000000) (21202465072 / 1000000000000), orderedInterval (76807695675 / 1000000000000) (76807695676 / 1000000000000)))) (orderedInterval (785993234 / 1000000000000) (785993264 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 2) <| besselDerivativeNearFromState (5413192393190421 / 128000000000000) 2 (IntervalRat.scale (5917 / 64) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-96809279696 / 1000000000000) (-96809231384 / 1000000000000), orderedInterval (76517990989 / 1000000000000) (76518039302 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 2) <| besselDerivativeNearFromState (22004326546863541 / 128000000000000) 2 (IntervalRat.scale (5917 / 64) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (5719365867 / 1000000000000) (5719365883 / 1000000000000), orderedInterval (-60601662117 / 1000000000000) (-60601662101 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 2) <| besselDerivativeNearFromState (14697870363394619 / 128000000000000) 2 (IntervalRat.scale (5917 / 64) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (43716812045 / 1000000000000) (43716828383 / 1000000000000), orderedInterval (-60464860192 / 1000000000000) (-60464843855 / 1000000000000)))) (orderedInterval (14130724767 / 1000000000000) (14130729658 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate205_chunkChecks2 :
    compactCertificate205.chunkChecks (2 : Fin 5) 0 9 = true :=
  compactCertificate205.chunkChecks_nine_of_three (2 : Fin 5) compactCertificate205_chunkChecks2_0
    compactCertificate205_chunkChecks2_1 compactCertificate205_chunkChecks2_2

theorem compactCertificate205_chunkChecks3_0 :
    compactCertificate205.chunkChecks (3 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 3) <| besselDerivativeNearFromState (5917 / 64) 3 (IntervalRat.scale (5917 / 64) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-70297386043 / 1000000000000) (-70297362130 / 1000000000000), orderedInterval (44472111446 / 1000000000000) (44472135359 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 3) <| besselDerivativeNearFromState (8716870838730217 / 128000000000000) 3 (IntervalRat.scale (5917 / 64) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-22128792621 / 1000000000000) (-22128792374 / 1000000000000), orderedInterval (94283523061 / 1000000000000) (94283523307 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 3) <| besselDerivativeNearFromState (2818856929831561 / 25600000000000) 3 (IntervalRat.scale (5917 / 64) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-61409108022 / 1000000000000) (-61409108021 / 1000000000000), orderedInterval (-44559646040 / 1000000000000) (-44559646039 / 1000000000000)))) (orderedInterval (-13915160842 / 1000000000000) (-13915151252 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 3) <| besselDerivativeNearFromState (2543561170556219 / 128000000000000) 3 (IntervalRat.scale (5917 / 64) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (174233452669 / 1000000000000) (174233453151 / 1000000000000), orderedInterval (-45251370276 / 1000000000000) (-45251369794 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 3) <| besselDerivativeNearFromState (6832363085588543 / 128000000000000) 3 (IntervalRat.scale (5917 / 64) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-74744210859 / 1000000000000) (-74744210858 / 1000000000000), orderedInterval (-78924064748 / 1000000000000) (-78924064747 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 3) <| besselDerivativeNearFromState (18551194861273731 / 128000000000000) 3 (IntervalRat.scale (5917 / 64) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (61831491174 / 1000000000000) (61831491175 / 1000000000000), orderedInterval (23649053486 / 1000000000000) (23649053487 / 1000000000000)))) (orderedInterval (6897609335 / 1000000000000) (6897609363 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 3) <| besselDerivativeNearFromState (13664726171183003 / 128000000000000) 3 (IntervalRat.scale (5917 / 64) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (51252135141 / 1000000000000) (51252135142 / 1000000000000), orderedInterval (57522931758 / 1000000000000) (57522931759 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 3) <| besselDerivativeNearFromState (23414741202118919 / 128000000000000) 3 (IntervalRat.scale (5917 / 64) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (58845123449 / 1000000000000) (58845123470 / 1000000000000), orderedInterval (4011777963 / 1000000000000) (4011777984 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 3) <| besselDerivativeNearFromState (17247192393190421 / 128000000000000) 3 (IntervalRat.scale (5917 / 64) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-29257290846 / 1000000000000) (-29257290845 / 1000000000000), orderedInterval (-62090340956 / 1000000000000) (-62090340955 / 1000000000000)))) (orderedInterval (5510233986 / 1000000000000) (5510234021 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate205_chunkChecks3_1 :
    compactCertificate205.chunkChecks (3 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 3) <| besselDerivativeNearFromState (26461628445729083 / 128000000000000) 3 (IntervalRat.scale (5917 / 64) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (9451315445 / 1000000000000) (9451315446 / 1000000000000), orderedInterval (54659256513 / 1000000000000) (54659256514 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 3) <| besselDerivativeNearFromState (15277628306335907 / 128000000000000) 3 (IntervalRat.scale (5917 / 64) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (50329483576 / 1000000000000) (50329483577 / 1000000000000), orderedInterval (52710937575 / 1000000000000) (52710937576 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 3) <| besselDerivativeNearFromState (27110419526358463 / 128000000000000) 3 (IntervalRat.scale (5917 / 64) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-47373503860 / 1000000000000) (-47373473162 / 1000000000000), orderedInterval (27707204459 / 1000000000000) (27707235158 / 1000000000000)))) (orderedInterval (52420162545 / 1000000000000) (52420215619 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 3) <| besselDerivativeNearFromState (25330070592651547 / 128000000000000) 3 (IntervalRat.scale (5917 / 64) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-38893690190 / 1000000000000) (-38893690189 / 1000000000000), orderedInterval (-41184910437 / 1000000000000) (-41184910436 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 3) <| besselDerivativeNearFromState (18076733591363851 / 128000000000000) 3 (IntervalRat.scale (5917 / 64) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-39951712118 / 1000000000000) (-39951712117 / 1000000000000), orderedInterval (-53818965533 / 1000000000000) (-53818965532 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 3) <| besselDerivativeNearFromState (20497089256765629 / 128000000000000) 3 (IntervalRat.scale (5917 / 64) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-40469530730 / 1000000000000) (-40469530729 / 1000000000000), orderedInterval (-48224200122 / 1000000000000) (-48224200121 / 1000000000000)))) (orderedInterval (9524705397 / 1000000000000) (9524705449 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 3) <| besselDerivativeNearFromState (17088336093313901 / 128000000000000) 3 (IntervalRat.scale (5917 / 64) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (49603954472 / 1000000000000) (49604027076 / 1000000000000), orderedInterval (-48227839515 / 1000000000000) (-48227766911 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 3) <| besselDerivativeNearFromState (15098063175683921 / 128000000000000) 3 (IntervalRat.scale (5917 / 64) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-44024104684 / 1000000000000) (-44024086097 / 1000000000000), orderedInterval (59000690659 / 1000000000000) (59000709246 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 3) <| besselDerivativeNearFromState (4376007183592179 / 25600000000000) 3 (IntervalRat.scale (5917 / 64) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (53389885156 / 1000000000000) (53389905863 / 1000000000000), orderedInterval (-29716086583 / 1000000000000) (-29716065876 / 1000000000000)))) (orderedInterval (13603794104 / 1000000000000) (13603802275 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate205_chunkChecks3_2 :
    compactCertificate205.chunkChecks (3 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 3) <| besselDerivativeNearFromState (12104266166456713 / 128000000000000) 3 (IntervalRat.scale (5917 / 64) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (73155168154 / 1000000000000) (73155168155 / 1000000000000), orderedInterval (36766709153 / 1000000000000) (36766709154 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 3) <| besselDerivativeNearFromState (10260920480382593 / 128000000000000) 3 (IntervalRat.scale (5917 / 64) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-59701346792 / 1000000000000) (-59701295856 / 1000000000000), orderedInterval (66533424948 / 1000000000000) (66533475884 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 3) <| besselDerivativeNearFromState (6420807606809579 / 128000000000000) 3 (IntervalRat.scale (5917 / 64) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (70833455031 / 1000000000000) (70833455032 / 1000000000000), orderedInterval (86894759797 / 1000000000000) (86894759798 / 1000000000000)))) (orderedInterval (8194389158 / 1000000000000) (8194391081 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 3) <| besselDerivativeNearFromState (3453131685583893 / 128000000000000) 3 (IntervalRat.scale (5917 / 64) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (75785347141 / 1000000000000) (75785355291 / 1000000000000), orderedInterval (-135033277701 / 1000000000000) (-135033269551 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 3) <| besselDerivativeNearFromState (9375924256150679 / 128000000000000) 3 (IntervalRat.scale (5917 / 64) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-91260289182 / 1000000000000) (-91260288712 / 1000000000000), orderedInterval (19662326055 / 1000000000000) (19662326524 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 3) <| besselDerivativeNearFromState (12802022999353783 / 128000000000000) 3 (IntervalRat.scale (5917 / 64) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (21202465071 / 1000000000000) (21202465072 / 1000000000000), orderedInterval (76807695675 / 1000000000000) (76807695676 / 1000000000000)))) (orderedInterval (7603075633 / 1000000000000) (7603075653 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 3) <| besselDerivativeNearFromState (5413192393190421 / 128000000000000) 3 (IntervalRat.scale (5917 / 64) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-96809279696 / 1000000000000) (-96809231384 / 1000000000000), orderedInterval (76517990989 / 1000000000000) (76518039302 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 3) <| besselDerivativeNearFromState (22004326546863541 / 128000000000000) 3 (IntervalRat.scale (5917 / 64) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (5719365867 / 1000000000000) (5719365883 / 1000000000000), orderedInterval (-60601662117 / 1000000000000) (-60601662101 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 3) <| besselDerivativeNearFromState (14697870363394619 / 128000000000000) 3 (IntervalRat.scale (5917 / 64) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (43716812045 / 1000000000000) (43716828383 / 1000000000000), orderedInterval (-60464860192 / 1000000000000) (-60464843855 / 1000000000000)))) (orderedInterval (-53643332451 / 1000000000000) (-53643326408 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate205_chunkChecks3 :
    compactCertificate205.chunkChecks (3 : Fin 5) 0 9 = true :=
  compactCertificate205.chunkChecks_nine_of_three (3 : Fin 5) compactCertificate205_chunkChecks3_0
    compactCertificate205_chunkChecks3_1 compactCertificate205_chunkChecks3_2

theorem compactCertificate205_chunkChecks4_0 :
    compactCertificate205.chunkChecks (4 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 4) <| besselDerivativeNearFromState (5917 / 64) 4 (IntervalRat.scale (5917 / 64) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-70297386043 / 1000000000000) (-70297362130 / 1000000000000), orderedInterval (44472111446 / 1000000000000) (44472135359 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 4) <| besselDerivativeNearFromState (8716870838730217 / 128000000000000) 4 (IntervalRat.scale (5917 / 64) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-22128792621 / 1000000000000) (-22128792374 / 1000000000000), orderedInterval (94283523061 / 1000000000000) (94283523307 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 4) <| besselDerivativeNearFromState (2818856929831561 / 25600000000000) 4 (IntervalRat.scale (5917 / 64) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-61409108022 / 1000000000000) (-61409108021 / 1000000000000), orderedInterval (-44559646040 / 1000000000000) (-44559646039 / 1000000000000)))) (orderedInterval (-34869925942 / 1000000000000) (-34869916249 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 4) <| besselDerivativeNearFromState (2543561170556219 / 128000000000000) 4 (IntervalRat.scale (5917 / 64) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (174233452669 / 1000000000000) (174233453151 / 1000000000000), orderedInterval (-45251370276 / 1000000000000) (-45251369794 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 4) <| besselDerivativeNearFromState (6832363085588543 / 128000000000000) 4 (IntervalRat.scale (5917 / 64) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-74744210859 / 1000000000000) (-74744210858 / 1000000000000), orderedInterval (-78924064748 / 1000000000000) (-78924064747 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 4) <| besselDerivativeNearFromState (18551194861273731 / 128000000000000) 4 (IntervalRat.scale (5917 / 64) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (61831491174 / 1000000000000) (61831491175 / 1000000000000), orderedInterval (23649053486 / 1000000000000) (23649053487 / 1000000000000)))) (orderedInterval (-26999753376 / 1000000000000) (-26999753334 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 4) <| besselDerivativeNearFromState (13664726171183003 / 128000000000000) 4 (IntervalRat.scale (5917 / 64) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (51252135141 / 1000000000000) (51252135142 / 1000000000000), orderedInterval (57522931758 / 1000000000000) (57522931759 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 4) <| besselDerivativeNearFromState (23414741202118919 / 128000000000000) 4 (IntervalRat.scale (5917 / 64) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (58845123449 / 1000000000000) (58845123470 / 1000000000000), orderedInterval (4011777963 / 1000000000000) (4011777984 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 4) <| besselDerivativeNearFromState (17247192393190421 / 128000000000000) 4 (IntervalRat.scale (5917 / 64) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-29257290846 / 1000000000000) (-29257290845 / 1000000000000), orderedInterval (-62090340956 / 1000000000000) (-62090340955 / 1000000000000)))) (orderedInterval (-31125556014 / 1000000000000) (-31125555949 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate205_chunkChecks4_1 :
    compactCertificate205.chunkChecks (4 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 4) <| besselDerivativeNearFromState (26461628445729083 / 128000000000000) 4 (IntervalRat.scale (5917 / 64) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (9451315445 / 1000000000000) (9451315446 / 1000000000000), orderedInterval (54659256513 / 1000000000000) (54659256514 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 4) <| besselDerivativeNearFromState (15277628306335907 / 128000000000000) 4 (IntervalRat.scale (5917 / 64) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (50329483576 / 1000000000000) (50329483577 / 1000000000000), orderedInterval (52710937575 / 1000000000000) (52710937576 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 4) <| besselDerivativeNearFromState (27110419526358463 / 128000000000000) 4 (IntervalRat.scale (5917 / 64) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-47373503860 / 1000000000000) (-47373473162 / 1000000000000), orderedInterval (27707204459 / 1000000000000) (27707235158 / 1000000000000)))) (orderedInterval (-218245243347 / 1000000000000) (-218245121225 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 4) <| besselDerivativeNearFromState (25330070592651547 / 128000000000000) 4 (IntervalRat.scale (5917 / 64) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-38893690190 / 1000000000000) (-38893690189 / 1000000000000), orderedInterval (-41184910437 / 1000000000000) (-41184910436 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 4) <| besselDerivativeNearFromState (18076733591363851 / 128000000000000) 4 (IntervalRat.scale (5917 / 64) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-39951712118 / 1000000000000) (-39951712117 / 1000000000000), orderedInterval (-53818965533 / 1000000000000) (-53818965532 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 4) <| besselDerivativeNearFromState (20497089256765629 / 128000000000000) 4 (IntervalRat.scale (5917 / 64) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-40469530730 / 1000000000000) (-40469530729 / 1000000000000), orderedInterval (-48224200122 / 1000000000000) (-48224200121 / 1000000000000)))) (orderedInterval (-4192697800 / 1000000000000) (-4192697711 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 4) <| besselDerivativeNearFromState (17088336093313901 / 128000000000000) 4 (IntervalRat.scale (5917 / 64) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (49603954472 / 1000000000000) (49604027076 / 1000000000000), orderedInterval (-48227839515 / 1000000000000) (-48227766911 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 4) <| besselDerivativeNearFromState (15098063175683921 / 128000000000000) 4 (IntervalRat.scale (5917 / 64) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-44024104684 / 1000000000000) (-44024086097 / 1000000000000), orderedInterval (59000690659 / 1000000000000) (59000709246 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 4) <| besselDerivativeNearFromState (4376007183592179 / 25600000000000) 4 (IntervalRat.scale (5917 / 64) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (53389885156 / 1000000000000) (53389905863 / 1000000000000), orderedInterval (-29716086583 / 1000000000000) (-29716065876 / 1000000000000)))) (orderedInterval (24844657845 / 1000000000000) (24844670724 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate205_chunkChecks4_2 :
    compactCertificate205.chunkChecks (4 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 4) <| besselDerivativeNearFromState (12104266166456713 / 128000000000000) 4 (IntervalRat.scale (5917 / 64) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (73155168154 / 1000000000000) (73155168155 / 1000000000000), orderedInterval (36766709153 / 1000000000000) (36766709154 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 4) <| besselDerivativeNearFromState (10260920480382593 / 128000000000000) 4 (IntervalRat.scale (5917 / 64) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-59701346792 / 1000000000000) (-59701295856 / 1000000000000), orderedInterval (66533424948 / 1000000000000) (66533475884 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 4) <| besselDerivativeNearFromState (6420807606809579 / 128000000000000) 4 (IntervalRat.scale (5917 / 64) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (70833455031 / 1000000000000) (70833455032 / 1000000000000), orderedInterval (86894759797 / 1000000000000) (86894759798 / 1000000000000)))) (orderedInterval (-10869080408 / 1000000000000) (-10869078717 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 4) <| besselDerivativeNearFromState (3453131685583893 / 128000000000000) 4 (IntervalRat.scale (5917 / 64) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (75785347141 / 1000000000000) (75785355291 / 1000000000000), orderedInterval (-135033277701 / 1000000000000) (-135033269551 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 4) <| besselDerivativeNearFromState (9375924256150679 / 128000000000000) 4 (IntervalRat.scale (5917 / 64) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-91260289182 / 1000000000000) (-91260288712 / 1000000000000), orderedInterval (19662326055 / 1000000000000) (19662326524 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 4) <| besselDerivativeNearFromState (12802022999353783 / 128000000000000) 4 (IntervalRat.scale (5917 / 64) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (21202465071 / 1000000000000) (21202465072 / 1000000000000), orderedInterval (76807695675 / 1000000000000) (76807695676 / 1000000000000)))) (orderedInterval (-1584194417 / 1000000000000) (-1584194400 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 4) <| besselDerivativeNearFromState (5413192393190421 / 128000000000000) 4 (IntervalRat.scale (5917 / 64) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-96809279696 / 1000000000000) (-96809231384 / 1000000000000), orderedInterval (76517990989 / 1000000000000) (76518039302 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 4) <| besselDerivativeNearFromState (22004326546863541 / 128000000000000) 4 (IntervalRat.scale (5917 / 64) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (5719365867 / 1000000000000) (5719365883 / 1000000000000), orderedInterval (-60601662117 / 1000000000000) (-60601662101 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 4) <| besselDerivativeNearFromState (14697870363394619 / 128000000000000) 4 (IntervalRat.scale (5917 / 64) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (43716812045 / 1000000000000) (43716828383 / 1000000000000), orderedInterval (-60464860192 / 1000000000000) (-60464843855 / 1000000000000)))) (orderedInterval (-23946727249 / 1000000000000) (-23946719668 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate205_chunkChecks4 :
    compactCertificate205.chunkChecks (4 : Fin 5) 0 9 = true :=
  compactCertificate205.chunkChecks_nine_of_three (4 : Fin 5) compactCertificate205_chunkChecks4_0
    compactCertificate205_chunkChecks4_1 compactCertificate205_chunkChecks4_2

theorem compactCertificate205_chunks :
    ∀ r : Fin 5, ∀ b, compactCertificate205.chunkCheck r b = true :=
  compactCertificate205.chunkChecks_all (by
    intro r
    fin_cases r
    · exact compactCertificate205_chunkChecks0
    · exact compactCertificate205_chunkChecks1
    · exact compactCertificate205_chunkChecks2
    · exact compactCertificate205_chunkChecks3
    · exact compactCertificate205_chunkChecks4)

theorem compactCertificate205_coefficient0 :
    compactCertificate205.coefficientCheck (0 : Fin 5) = true := by
  norm_num [CompactCertificate.coefficientCheck, intervalFinSumHull,
    compactCertificate205, rationalIntervalSubset, orderedInterval, Fin.sum_univ_succ]

theorem compactCertificate205_coefficient1 :
    compactCertificate205.coefficientCheck (1 : Fin 5) = true := by
  norm_num [CompactCertificate.coefficientCheck, intervalFinSumHull,
    compactCertificate205, rationalIntervalSubset, orderedInterval, Fin.sum_univ_succ]

theorem compactCertificate205_coefficient2 :
    compactCertificate205.coefficientCheck (2 : Fin 5) = true := by
  norm_num [CompactCertificate.coefficientCheck, intervalFinSumHull,
    compactCertificate205, rationalIntervalSubset, orderedInterval, Fin.sum_univ_succ]

theorem compactCertificate205_coefficient3 :
    compactCertificate205.coefficientCheck (3 : Fin 5) = true := by
  norm_num [CompactCertificate.coefficientCheck, intervalFinSumHull,
    compactCertificate205, rationalIntervalSubset, orderedInterval, Fin.sum_univ_succ]

theorem compactCertificate205_coefficient4 :
    compactCertificate205.coefficientCheck (4 : Fin 5) = true := by
  norm_num [CompactCertificate.coefficientCheck, intervalFinSumHull,
    compactCertificate205, rationalIntervalSubset, orderedInterval, Fin.sum_univ_succ]

theorem compactCertificate205_coefficients : ∀ r : Fin 5,
    compactCertificate205.coefficientCheck r = true := by
  intro r
  fin_cases r
  · exact compactCertificate205_coefficient0
  · exact compactCertificate205_coefficient1
  · exact compactCertificate205_coefficient2
  · exact compactCertificate205_coefficient3
  · exact compactCertificate205_coefficient4

theorem compactCertificate205_lower : (1 : ℚ) ≤ compactCertificate205.output.lo := by
  norm_num [CompactCertificate.output, CompactCertificate.interval,
    CompactCertificate.coefficientTargetNat, compactCertificate205, dualConstant,
    intervalTaylorSum, intervalPow, intervalSub, intervalMaxAbs, widenInterval,
    rationalErrorInterval, orderedInterval, IntervalRat.add, IntervalRat.mul, IntervalRat.scale,
    IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4]

theorem compactCertificate205_proves {t : ℝ} (ht : t ∈ compactCertificate205.interval) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t :=
  compactCertificate205.proves compactCertificate205_states compactCertificate205_chunks
    compactCertificate205_coefficients compactCertificate205_lower ht

end Erdos232
