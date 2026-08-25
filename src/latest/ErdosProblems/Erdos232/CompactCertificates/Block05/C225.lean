/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, OpenAI Codex
-/
import ErdosProblems.Erdos232.CompactBase

open LeanCert.Core
namespace Erdos232

def compactCertificate225 : CompactCertificate where
  left := 104
  right := 209 / 2
  center := 417 / 4
  grid := fun i =>
    match i.val with
    | 0 => 33
    | 1 => 24
    | 2 => 40
    | 3 => 7
    | 4 => 19
    | 5 => 52
    | 6 => 38
    | 7 => 66
    | 8 => 48
    | 9 => 74
    | 10 => 43
    | 11 => 76
    | 12 => 71
    | 13 => 51
    | 14 => 58
    | 15 => 48
    | 16 => 42
    | 17 => 61
    | 18 => 34
    | 19 => 29
    | 20 => 18
    | 21 => 10
    | 22 => 26
    | 23 => 36
    | 24 => 15
    | 25 => 62
    | _ => 41
  point := fun i =>
    match i.val with
    | 0 => 417 / 4
    | 1 => 614320625274717 / 8000000000000
    | 2 => 198658668200061 / 1600000000000
    | 3 => 179257226317719 / 8000000000000
    | 4 => 481510124504043 / 8000000000000
    | 5 => 1307393655087231 / 8000000000000
    | 6 => 963020249008503 / 8000000000000
    | 7 => 1650151610830419 / 8000000000000
    | 8 => 1215494207868921 / 8000000000000
    | 9 => 1864880693234583 / 8000000000000
    | 10 => 1076689370245407 / 8000000000000
    | 11 => 1910604181593963 / 8000000000000
    | 12 => 1785134263501047 / 8000000000000
    | 13 => 1273956043197351 / 8000000000000
    | 14 => 1444530373512129 / 8000000000000
    | 15 => 1204298825572401 / 8000000000000
    | 16 => 1064034535112421 / 8000000000000
    | 17 => 308398681013679 / 1600000000000
    | 18 => 853046981817213 / 8000000000000
    | 19 => 723137373723093 / 8000000000000
    | 20 => 452505792131079 / 8000000000000
    | 21 => 243359119974393 / 8000000000000
    | 22 => 660767350822179 / 8000000000000
    | 23 => 902221326809283 / 8000000000000
    | 24 => 381494207868921 / 8000000000000
    | 25 => 1550752775062041 / 8000000000000
    | _ => 1035830985556119 / 8000000000000
  state := fun i =>
    match i.val with
    | 0 => (orderedInterval (-76441675586 / 1000000000000) (-76441675584 / 1000000000000), orderedInterval (-15858995594 / 1000000000000) (-15858995592 / 1000000000000))
    | 1 => (orderedInterval (74898180799 / 1000000000000) (74898214406 / 1000000000000), orderedInterval (-52262079099 / 1000000000000) (-52262045491 / 1000000000000))
    | 2 => (orderedInterval (-47088589039 / 1000000000000) (-47088552820 / 1000000000000), orderedInterval (54134182530 / 1000000000000) (54134218749 / 1000000000000))
    | 3 => (orderedInterval (-156826167804 / 1000000000000) (-156826167803 / 1000000000000), orderedInterval (-58242423666 / 1000000000000) (-58242423665 / 1000000000000))
    | 4 => (orderedInterval (-98578953729 / 1000000000000) (-98578953728 / 1000000000000), orderedInterval (-28488776893 / 1000000000000) (-28488776892 / 1000000000000))
    | 5 => (orderedInterval (46726064980 / 1000000000000) (46726064981 / 1000000000000), orderedInterval (41235507136 / 1000000000000) (41235507137 / 1000000000000))
    | 6 => (orderedInterval (71115598118 / 1000000000000) (71115598783 / 1000000000000), orderedInterval (-15495926972 / 1000000000000) (-15495926307 / 1000000000000))
    | 7 => (orderedInterval (-15959055169 / 1000000000000) (-15959054948 / 1000000000000), orderedInterval (53252159160 / 1000000000000) (53252159380 / 1000000000000))
    | 8 => (orderedInterval (60714161171 / 1000000000000) (60714165288 / 1000000000000), orderedInterval (-22645378070 / 1000000000000) (-22645373952 / 1000000000000))
    | 9 => (orderedInterval (51642660579 / 1000000000000) (51642660587 / 1000000000000), orderedInterval (7890044169 / 1000000000000) (7890044177 / 1000000000000))
    | 10 => (orderedInterval (-19149200375 / 1000000000000) (-19149200374 / 1000000000000), orderedInterval (-65985938846 / 1000000000000) (-65985938845 / 1000000000000))
    | 11 => (orderedInterval (38766388630 / 1000000000000) (38766388631 / 1000000000000), orderedInterval (34018596654 / 1000000000000) (34018596655 / 1000000000000))
    | 12 => (orderedInterval (-40947054583 / 1000000000000) (-40947054582 / 1000000000000), orderedInterval (-34205781671 / 1000000000000) (-34205781670 / 1000000000000))
    | 13 => (orderedInterval (12071875026 / 1000000000000) (12071875103 / 1000000000000), orderedInterval (-62102695362 / 1000000000000) (-62102695284 / 1000000000000))
    | 14 => (orderedInterval (-45051819893 / 1000000000000) (-45051721143 / 1000000000000), orderedInterval (38803118330 / 1000000000000) (38803217081 / 1000000000000))
    | 15 => (orderedInterval (32620754388 / 1000000000000) (32620754389 / 1000000000000), orderedInterval (56148920325 / 1000000000000) (56148920326 / 1000000000000))
    | 16 => (orderedInterval (66657416163 / 1000000000000) (66657417637 / 1000000000000), orderedInterval (-18776758815 / 1000000000000) (-18776757341 / 1000000000000))
    | 17 => (orderedInterval (-54443766963 / 1000000000000) (-54443763168 / 1000000000000), orderedInterval (18545249189 / 1000000000000) (18545252984 / 1000000000000))
    | 18 => (orderedInterval (43688909905 / 1000000000000) (43688909906 / 1000000000000), orderedInterval (63525957805 / 1000000000000) (63525957806 / 1000000000000))
    | 19 => (orderedInterval (-5869695408 / 1000000000000) (-5869695405 / 1000000000000), orderedInterval (-83684421134 / 1000000000000) (-83684421131 / 1000000000000))
    | 20 => (orderedInterval (75935689668 / 1000000000000) (75935689669 / 1000000000000), orderedInterval (73415055474 / 1000000000000) (73415055475 / 1000000000000))
    | 21 => (orderedInterval (-30825659634 / 1000000000000) (-30825659385 / 1000000000000), orderedInterval (141857486118 / 1000000000000) (141857486367 / 1000000000000))
    | 22 => (orderedInterval (87078652825 / 1000000000000) (87078653004 / 1000000000000), orderedInterval (-11699117025 / 1000000000000) (-11699116845 / 1000000000000))
    | 23 => (orderedInterval (33665501773 / 1000000000000) (33665501774 / 1000000000000), orderedInterval (67019021926 / 1000000000000) (67019021927 / 1000000000000))
    | 24 => (orderedInterval (-112623458072 / 1000000000000) (-112623458071 / 1000000000000), orderedInterval (-24613138597 / 1000000000000) (-24613138596 / 1000000000000))
    | 25 => (orderedInterval (-8557968497 / 1000000000000) (-8557968465 / 1000000000000), orderedInterval (56687372941 / 1000000000000) (56687372973 / 1000000000000))
    | _ => (orderedInterval (-69673992120 / 1000000000000) (-69673992113 / 1000000000000), orderedInterval (-7622971377 / 1000000000000) (-7622971370 / 1000000000000))
  chunkTarget := fun r b =>
    match r.val with
    | 0 =>
      match b.val with
      | 0 => orderedInterval (-32364110556 / 1000000000000) (-32364108108 / 1000000000000)
      | 1 => orderedInterval (-5219576180 / 1000000000000) (-5219576167 / 1000000000000)
      | 2 => orderedInterval (1959582590 / 1000000000000) (1959582703 / 1000000000000)
      | 3 => orderedInterval (-5084204888 / 1000000000000) (-5084204844 / 1000000000000)
      | 4 => orderedInterval (2108759450 / 1000000000000) (2108759971 / 1000000000000)
      | 5 => orderedInterval (-4831864294 / 1000000000000) (-4831864102 / 1000000000000)
      | 6 => orderedInterval (-4181195049 / 1000000000000) (-4181195022 / 1000000000000)
      | 7 => orderedInterval (-3986427997 / 1000000000000) (-3986427975 / 1000000000000)
      | _ => orderedInterval (13090391842 / 1000000000000) (13090391876 / 1000000000000)
    | 1 =>
      match b.val with
      | 0 => orderedInterval (-2861264579 / 1000000000000) (-2861261807 / 1000000000000)
      | 1 => orderedInterval (-5060072699 / 1000000000000) (-5060072684 / 1000000000000)
      | 2 => orderedInterval (-4047509329 / 1000000000000) (-4047509159 / 1000000000000)
      | 3 => orderedInterval (1632045072 / 1000000000000) (1632045162 / 1000000000000)
      | 4 => orderedInterval (-7988905456 / 1000000000000) (-7988904559 / 1000000000000)
      | 5 => orderedInterval (3185108086 / 1000000000000) (3185108388 / 1000000000000)
      | 6 => orderedInterval (-4985607129 / 1000000000000) (-4985607104 / 1000000000000)
      | 7 => orderedInterval (-6110462083 / 1000000000000) (-6110462066 / 1000000000000)
      | _ => orderedInterval (-6871655364 / 1000000000000) (-6871655316 / 1000000000000)
    | 2 =>
      match b.val with
      | 0 => orderedInterval (33867141079 / 1000000000000) (33867144301 / 1000000000000)
      | 1 => orderedInterval (9332629651 / 1000000000000) (9332629672 / 1000000000000)
      | 2 => orderedInterval (-5004998308 / 1000000000000) (-5004998049 / 1000000000000)
      | 3 => orderedInterval (19308312438 / 1000000000000) (19308312631 / 1000000000000)
      | 4 => orderedInterval (-6657706630 / 1000000000000) (-6657705071 / 1000000000000)
      | 5 => orderedInterval (10158328913 / 1000000000000) (10158329408 / 1000000000000)
      | 6 => orderedInterval (6378543396 / 1000000000000) (6378543420 / 1000000000000)
      | 7 => orderedInterval (4269685739 / 1000000000000) (4269685754 / 1000000000000)
      | _ => orderedInterval (-22366162284 / 1000000000000) (-22366162212 / 1000000000000)
    | 3 =>
      match b.val with
      | 0 => orderedInterval (788778575 / 1000000000000) (788782333 / 1000000000000)
      | 1 => orderedInterval (11396641899 / 1000000000000) (11396641930 / 1000000000000)
      | 2 => orderedInterval (14464661278 / 1000000000000) (14464661675 / 1000000000000)
      | 3 => orderedInterval (-32133835533 / 1000000000000) (-32133835112 / 1000000000000)
      | 4 => orderedInterval (15959062897 / 1000000000000) (15959065592 / 1000000000000)
      | 5 => orderedInterval (-7282036421 / 1000000000000) (-7282035593 / 1000000000000)
      | 6 => orderedInterval (7338233631 / 1000000000000) (7338233654 / 1000000000000)
      | 7 => orderedInterval (6394180168 / 1000000000000) (6394180182 / 1000000000000)
      | _ => orderedInterval (27153251944 / 1000000000000) (27153252057 / 1000000000000)
    | _ =>
      match b.val with
      | 0 => orderedInterval (-35665176859 / 1000000000000) (-35665172405 / 1000000000000)
      | 1 => orderedInterval (-20673877400 / 1000000000000) (-20673877353 / 1000000000000)
      | 2 => orderedInterval (13886485532 / 1000000000000) (13886486154 / 1000000000000)
      | 3 => orderedInterval (-80941274311 / 1000000000000) (-80941273376 / 1000000000000)
      | 4 => orderedInterval (23476714807 / 1000000000000) (23476719494 / 1000000000000)
      | 5 => orderedInterval (-24618174966 / 1000000000000) (-24618173538 / 1000000000000)
      | 6 => orderedInterval (-7384037134 / 1000000000000) (-7384037111 / 1000000000000)
      | 7 => orderedInterval (-4430209597 / 1000000000000) (-4430209582 / 1000000000000)
      | _ => orderedInterval (38881591832 / 1000000000000) (38881592016 / 1000000000000)
  coefficientTarget := fun i =>
    match i.val with
    | 0 => orderedInterval (-38508645082 / 1000000000000) (-38508641668 / 1000000000000)
    | 1 => orderedInterval (-33108323481 / 1000000000000) (-33108319145 / 1000000000000)
    | 2 => orderedInterval (49285773994 / 1000000000000) (49285779854 / 1000000000000)
    | 3 => orderedInterval (44078938438 / 1000000000000) (44078946718 / 1000000000000)
    | _ => orderedInterval (-97467958096 / 1000000000000) (-97467945701 / 1000000000000)

theorem compactCertificate225_stateChecks0 :
    compactCertificate225.stateChecks 0 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 33 12 (417 / 4)) (orderedInterval (-76441675586 / 1000000000000) (-76441675584 / 1000000000000), orderedInterval (-15858995594 / 1000000000000) (-15858995592 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 24 12 (614320625274717 / 8000000000000)) (orderedInterval (74898180799 / 1000000000000) (74898214406 / 1000000000000), orderedInterval (-52262079099 / 1000000000000) (-52262045491 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 40 12 (198658668200061 / 1600000000000)) (orderedInterval (-47088589039 / 1000000000000) (-47088552820 / 1000000000000), orderedInterval (54134182530 / 1000000000000) (54134218749 / 1000000000000))) = true
  norm_num [besselStateAtRationalPoint, besselIntervalStepZero,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, besselZeroTransition,
    besselInitial, besselGridStateAt, besselGridStateBlock00, besselGridStateBlock01,
    besselGridStateBlock02, besselGridStateBlock03, besselGridStateBlock04,
    besselGridStateBlock05, besselGridStateBlock06, besselGridStateBlock07,
    besselGridStateBlock08, besselGridStateBlock09, besselGridStateBlock10,
    besselGridStateBlock11, besselGridStateBlock12, besselGridStateBlock13,
    besselGridStateBlock14, besselGridState007, besselGridState010, besselGridState015, besselGridState018, besselGridState019, besselGridState024, besselGridState026, besselGridState029, besselGridState033, besselGridState034, besselGridState036, besselGridState038, besselGridState040, besselGridState041, besselGridState042, besselGridState043, besselGridState048, besselGridState051, besselGridState052, besselGridState058, besselGridState061, besselGridState062, besselGridState066, besselGridState071, besselGridState074, besselGridState076, besselStateSubset, linearInterval, widenInterval,
    rationalErrorInterval, rationalIntervalSubset, orderedInterval, Finset.sum_range_succ,
    IntervalRat.add, IntervalRat.mul, IntervalRat.scale, IntervalRat.singleton]

theorem compactCertificate225_stateChecks1 :
    compactCertificate225.stateChecks 3 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 7 12 (179257226317719 / 8000000000000)) (orderedInterval (-156826167804 / 1000000000000) (-156826167803 / 1000000000000), orderedInterval (-58242423666 / 1000000000000) (-58242423665 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 19 12 (481510124504043 / 8000000000000)) (orderedInterval (-98578953729 / 1000000000000) (-98578953728 / 1000000000000), orderedInterval (-28488776893 / 1000000000000) (-28488776892 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 52 12 (1307393655087231 / 8000000000000)) (orderedInterval (46726064980 / 1000000000000) (46726064981 / 1000000000000), orderedInterval (41235507136 / 1000000000000) (41235507137 / 1000000000000))) = true
  norm_num [besselStateAtRationalPoint, besselIntervalStepZero,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, besselZeroTransition,
    besselInitial, besselGridStateAt, besselGridStateBlock00, besselGridStateBlock01,
    besselGridStateBlock02, besselGridStateBlock03, besselGridStateBlock04,
    besselGridStateBlock05, besselGridStateBlock06, besselGridStateBlock07,
    besselGridStateBlock08, besselGridStateBlock09, besselGridStateBlock10,
    besselGridStateBlock11, besselGridStateBlock12, besselGridStateBlock13,
    besselGridStateBlock14, besselGridState007, besselGridState010, besselGridState015, besselGridState018, besselGridState019, besselGridState024, besselGridState026, besselGridState029, besselGridState033, besselGridState034, besselGridState036, besselGridState038, besselGridState040, besselGridState041, besselGridState042, besselGridState043, besselGridState048, besselGridState051, besselGridState052, besselGridState058, besselGridState061, besselGridState062, besselGridState066, besselGridState071, besselGridState074, besselGridState076, besselStateSubset, linearInterval, widenInterval,
    rationalErrorInterval, rationalIntervalSubset, orderedInterval, Finset.sum_range_succ,
    IntervalRat.add, IntervalRat.mul, IntervalRat.scale, IntervalRat.singleton]

theorem compactCertificate225_stateChecks2 :
    compactCertificate225.stateChecks 6 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 38 12 (963020249008503 / 8000000000000)) (orderedInterval (71115598118 / 1000000000000) (71115598783 / 1000000000000), orderedInterval (-15495926972 / 1000000000000) (-15495926307 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 66 12 (1650151610830419 / 8000000000000)) (orderedInterval (-15959055169 / 1000000000000) (-15959054948 / 1000000000000), orderedInterval (53252159160 / 1000000000000) (53252159380 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 48 12 (1215494207868921 / 8000000000000)) (orderedInterval (60714161171 / 1000000000000) (60714165288 / 1000000000000), orderedInterval (-22645378070 / 1000000000000) (-22645373952 / 1000000000000))) = true
  norm_num [besselStateAtRationalPoint, besselIntervalStepZero,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, besselZeroTransition,
    besselInitial, besselGridStateAt, besselGridStateBlock00, besselGridStateBlock01,
    besselGridStateBlock02, besselGridStateBlock03, besselGridStateBlock04,
    besselGridStateBlock05, besselGridStateBlock06, besselGridStateBlock07,
    besselGridStateBlock08, besselGridStateBlock09, besselGridStateBlock10,
    besselGridStateBlock11, besselGridStateBlock12, besselGridStateBlock13,
    besselGridStateBlock14, besselGridState007, besselGridState010, besselGridState015, besselGridState018, besselGridState019, besselGridState024, besselGridState026, besselGridState029, besselGridState033, besselGridState034, besselGridState036, besselGridState038, besselGridState040, besselGridState041, besselGridState042, besselGridState043, besselGridState048, besselGridState051, besselGridState052, besselGridState058, besselGridState061, besselGridState062, besselGridState066, besselGridState071, besselGridState074, besselGridState076, besselStateSubset, linearInterval, widenInterval,
    rationalErrorInterval, rationalIntervalSubset, orderedInterval, Finset.sum_range_succ,
    IntervalRat.add, IntervalRat.mul, IntervalRat.scale, IntervalRat.singleton]

theorem compactCertificate225_stateChecks3 :
    compactCertificate225.stateChecks 9 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 74 12 (1864880693234583 / 8000000000000)) (orderedInterval (51642660579 / 1000000000000) (51642660587 / 1000000000000), orderedInterval (7890044169 / 1000000000000) (7890044177 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 43 12 (1076689370245407 / 8000000000000)) (orderedInterval (-19149200375 / 1000000000000) (-19149200374 / 1000000000000), orderedInterval (-65985938846 / 1000000000000) (-65985938845 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 76 12 (1910604181593963 / 8000000000000)) (orderedInterval (38766388630 / 1000000000000) (38766388631 / 1000000000000), orderedInterval (34018596654 / 1000000000000) (34018596655 / 1000000000000))) = true
  norm_num [besselStateAtRationalPoint, besselIntervalStepZero,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, besselZeroTransition,
    besselInitial, besselGridStateAt, besselGridStateBlock00, besselGridStateBlock01,
    besselGridStateBlock02, besselGridStateBlock03, besselGridStateBlock04,
    besselGridStateBlock05, besselGridStateBlock06, besselGridStateBlock07,
    besselGridStateBlock08, besselGridStateBlock09, besselGridStateBlock10,
    besselGridStateBlock11, besselGridStateBlock12, besselGridStateBlock13,
    besselGridStateBlock14, besselGridState007, besselGridState010, besselGridState015, besselGridState018, besselGridState019, besselGridState024, besselGridState026, besselGridState029, besselGridState033, besselGridState034, besselGridState036, besselGridState038, besselGridState040, besselGridState041, besselGridState042, besselGridState043, besselGridState048, besselGridState051, besselGridState052, besselGridState058, besselGridState061, besselGridState062, besselGridState066, besselGridState071, besselGridState074, besselGridState076, besselStateSubset, linearInterval, widenInterval,
    rationalErrorInterval, rationalIntervalSubset, orderedInterval, Finset.sum_range_succ,
    IntervalRat.add, IntervalRat.mul, IntervalRat.scale, IntervalRat.singleton]

theorem compactCertificate225_stateChecks4 :
    compactCertificate225.stateChecks 12 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 71 12 (1785134263501047 / 8000000000000)) (orderedInterval (-40947054583 / 1000000000000) (-40947054582 / 1000000000000), orderedInterval (-34205781671 / 1000000000000) (-34205781670 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 51 12 (1273956043197351 / 8000000000000)) (orderedInterval (12071875026 / 1000000000000) (12071875103 / 1000000000000), orderedInterval (-62102695362 / 1000000000000) (-62102695284 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 58 12 (1444530373512129 / 8000000000000)) (orderedInterval (-45051819893 / 1000000000000) (-45051721143 / 1000000000000), orderedInterval (38803118330 / 1000000000000) (38803217081 / 1000000000000))) = true
  norm_num [besselStateAtRationalPoint, besselIntervalStepZero,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, besselZeroTransition,
    besselInitial, besselGridStateAt, besselGridStateBlock00, besselGridStateBlock01,
    besselGridStateBlock02, besselGridStateBlock03, besselGridStateBlock04,
    besselGridStateBlock05, besselGridStateBlock06, besselGridStateBlock07,
    besselGridStateBlock08, besselGridStateBlock09, besselGridStateBlock10,
    besselGridStateBlock11, besselGridStateBlock12, besselGridStateBlock13,
    besselGridStateBlock14, besselGridState007, besselGridState010, besselGridState015, besselGridState018, besselGridState019, besselGridState024, besselGridState026, besselGridState029, besselGridState033, besselGridState034, besselGridState036, besselGridState038, besselGridState040, besselGridState041, besselGridState042, besselGridState043, besselGridState048, besselGridState051, besselGridState052, besselGridState058, besselGridState061, besselGridState062, besselGridState066, besselGridState071, besselGridState074, besselGridState076, besselStateSubset, linearInterval, widenInterval,
    rationalErrorInterval, rationalIntervalSubset, orderedInterval, Finset.sum_range_succ,
    IntervalRat.add, IntervalRat.mul, IntervalRat.scale, IntervalRat.singleton]

theorem compactCertificate225_stateChecks5 :
    compactCertificate225.stateChecks 15 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 48 12 (1204298825572401 / 8000000000000)) (orderedInterval (32620754388 / 1000000000000) (32620754389 / 1000000000000), orderedInterval (56148920325 / 1000000000000) (56148920326 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 42 12 (1064034535112421 / 8000000000000)) (orderedInterval (66657416163 / 1000000000000) (66657417637 / 1000000000000), orderedInterval (-18776758815 / 1000000000000) (-18776757341 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 61 12 (308398681013679 / 1600000000000)) (orderedInterval (-54443766963 / 1000000000000) (-54443763168 / 1000000000000), orderedInterval (18545249189 / 1000000000000) (18545252984 / 1000000000000))) = true
  norm_num [besselStateAtRationalPoint, besselIntervalStepZero,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, besselZeroTransition,
    besselInitial, besselGridStateAt, besselGridStateBlock00, besselGridStateBlock01,
    besselGridStateBlock02, besselGridStateBlock03, besselGridStateBlock04,
    besselGridStateBlock05, besselGridStateBlock06, besselGridStateBlock07,
    besselGridStateBlock08, besselGridStateBlock09, besselGridStateBlock10,
    besselGridStateBlock11, besselGridStateBlock12, besselGridStateBlock13,
    besselGridStateBlock14, besselGridState007, besselGridState010, besselGridState015, besselGridState018, besselGridState019, besselGridState024, besselGridState026, besselGridState029, besselGridState033, besselGridState034, besselGridState036, besselGridState038, besselGridState040, besselGridState041, besselGridState042, besselGridState043, besselGridState048, besselGridState051, besselGridState052, besselGridState058, besselGridState061, besselGridState062, besselGridState066, besselGridState071, besselGridState074, besselGridState076, besselStateSubset, linearInterval, widenInterval,
    rationalErrorInterval, rationalIntervalSubset, orderedInterval, Finset.sum_range_succ,
    IntervalRat.add, IntervalRat.mul, IntervalRat.scale, IntervalRat.singleton]

theorem compactCertificate225_stateChecks6 :
    compactCertificate225.stateChecks 18 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 34 12 (853046981817213 / 8000000000000)) (orderedInterval (43688909905 / 1000000000000) (43688909906 / 1000000000000), orderedInterval (63525957805 / 1000000000000) (63525957806 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 29 12 (723137373723093 / 8000000000000)) (orderedInterval (-5869695408 / 1000000000000) (-5869695405 / 1000000000000), orderedInterval (-83684421134 / 1000000000000) (-83684421131 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 18 12 (452505792131079 / 8000000000000)) (orderedInterval (75935689668 / 1000000000000) (75935689669 / 1000000000000), orderedInterval (73415055474 / 1000000000000) (73415055475 / 1000000000000))) = true
  norm_num [besselStateAtRationalPoint, besselIntervalStepZero,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, besselZeroTransition,
    besselInitial, besselGridStateAt, besselGridStateBlock00, besselGridStateBlock01,
    besselGridStateBlock02, besselGridStateBlock03, besselGridStateBlock04,
    besselGridStateBlock05, besselGridStateBlock06, besselGridStateBlock07,
    besselGridStateBlock08, besselGridStateBlock09, besselGridStateBlock10,
    besselGridStateBlock11, besselGridStateBlock12, besselGridStateBlock13,
    besselGridStateBlock14, besselGridState007, besselGridState010, besselGridState015, besselGridState018, besselGridState019, besselGridState024, besselGridState026, besselGridState029, besselGridState033, besselGridState034, besselGridState036, besselGridState038, besselGridState040, besselGridState041, besselGridState042, besselGridState043, besselGridState048, besselGridState051, besselGridState052, besselGridState058, besselGridState061, besselGridState062, besselGridState066, besselGridState071, besselGridState074, besselGridState076, besselStateSubset, linearInterval, widenInterval,
    rationalErrorInterval, rationalIntervalSubset, orderedInterval, Finset.sum_range_succ,
    IntervalRat.add, IntervalRat.mul, IntervalRat.scale, IntervalRat.singleton]

theorem compactCertificate225_stateChecks7 :
    compactCertificate225.stateChecks 21 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 10 12 (243359119974393 / 8000000000000)) (orderedInterval (-30825659634 / 1000000000000) (-30825659385 / 1000000000000), orderedInterval (141857486118 / 1000000000000) (141857486367 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 26 12 (660767350822179 / 8000000000000)) (orderedInterval (87078652825 / 1000000000000) (87078653004 / 1000000000000), orderedInterval (-11699117025 / 1000000000000) (-11699116845 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 36 12 (902221326809283 / 8000000000000)) (orderedInterval (33665501773 / 1000000000000) (33665501774 / 1000000000000), orderedInterval (67019021926 / 1000000000000) (67019021927 / 1000000000000))) = true
  norm_num [besselStateAtRationalPoint, besselIntervalStepZero,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, besselZeroTransition,
    besselInitial, besselGridStateAt, besselGridStateBlock00, besselGridStateBlock01,
    besselGridStateBlock02, besselGridStateBlock03, besselGridStateBlock04,
    besselGridStateBlock05, besselGridStateBlock06, besselGridStateBlock07,
    besselGridStateBlock08, besselGridStateBlock09, besselGridStateBlock10,
    besselGridStateBlock11, besselGridStateBlock12, besselGridStateBlock13,
    besselGridStateBlock14, besselGridState007, besselGridState010, besselGridState015, besselGridState018, besselGridState019, besselGridState024, besselGridState026, besselGridState029, besselGridState033, besselGridState034, besselGridState036, besselGridState038, besselGridState040, besselGridState041, besselGridState042, besselGridState043, besselGridState048, besselGridState051, besselGridState052, besselGridState058, besselGridState061, besselGridState062, besselGridState066, besselGridState071, besselGridState074, besselGridState076, besselStateSubset, linearInterval, widenInterval,
    rationalErrorInterval, rationalIntervalSubset, orderedInterval, Finset.sum_range_succ,
    IntervalRat.add, IntervalRat.mul, IntervalRat.scale, IntervalRat.singleton]

theorem compactCertificate225_stateChecks8 :
    compactCertificate225.stateChecks 24 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 15 12 (381494207868921 / 8000000000000)) (orderedInterval (-112623458072 / 1000000000000) (-112623458071 / 1000000000000), orderedInterval (-24613138597 / 1000000000000) (-24613138596 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 62 12 (1550752775062041 / 8000000000000)) (orderedInterval (-8557968497 / 1000000000000) (-8557968465 / 1000000000000), orderedInterval (56687372941 / 1000000000000) (56687372973 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 41 12 (1035830985556119 / 8000000000000)) (orderedInterval (-69673992120 / 1000000000000) (-69673992113 / 1000000000000), orderedInterval (-7622971377 / 1000000000000) (-7622971370 / 1000000000000))) = true
  norm_num [besselStateAtRationalPoint, besselIntervalStepZero,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, besselZeroTransition,
    besselInitial, besselGridStateAt, besselGridStateBlock00, besselGridStateBlock01,
    besselGridStateBlock02, besselGridStateBlock03, besselGridStateBlock04,
    besselGridStateBlock05, besselGridStateBlock06, besselGridStateBlock07,
    besselGridStateBlock08, besselGridStateBlock09, besselGridStateBlock10,
    besselGridStateBlock11, besselGridStateBlock12, besselGridStateBlock13,
    besselGridStateBlock14, besselGridState007, besselGridState010, besselGridState015, besselGridState018, besselGridState019, besselGridState024, besselGridState026, besselGridState029, besselGridState033, besselGridState034, besselGridState036, besselGridState038, besselGridState040, besselGridState041, besselGridState042, besselGridState043, besselGridState048, besselGridState051, besselGridState052, besselGridState058, besselGridState061, besselGridState062, besselGridState066, besselGridState071, besselGridState074, besselGridState076, besselStateSubset, linearInterval, widenInterval,
    rationalErrorInterval, rationalIntervalSubset, orderedInterval, Finset.sum_range_succ,
    IntervalRat.add, IntervalRat.mul, IntervalRat.scale, IntervalRat.singleton]

theorem compactCertificate225_states : ∀ j,
    BesselStateValid (compactCertificate225.point j) (compactCertificate225.state j) :=
  compactCertificate225.statesValid_of_checks3 compactCertificate225_stateChecks0
    compactCertificate225_stateChecks1 compactCertificate225_stateChecks2
    compactCertificate225_stateChecks3 compactCertificate225_stateChecks4
    compactCertificate225_stateChecks5 compactCertificate225_stateChecks6
    compactCertificate225_stateChecks7 compactCertificate225_stateChecks8

theorem compactCertificate225_chunkChecks0_0 :
    compactCertificate225.chunkChecks (0 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 0) <| besselDerivativeNearFromState (417 / 4) 0 (IntervalRat.scale (417 / 4) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-76441675586 / 1000000000000) (-76441675584 / 1000000000000), orderedInterval (-15858995594 / 1000000000000) (-15858995592 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 0) <| besselDerivativeNearFromState (614320625274717 / 8000000000000) 0 (IntervalRat.scale (417 / 4) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (74898180799 / 1000000000000) (74898214406 / 1000000000000), orderedInterval (-52262079099 / 1000000000000) (-52262045491 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 0) <| besselDerivativeNearFromState (198658668200061 / 1600000000000) 0 (IntervalRat.scale (417 / 4) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-47088589039 / 1000000000000) (-47088552820 / 1000000000000), orderedInterval (54134182530 / 1000000000000) (54134218749 / 1000000000000)))) (orderedInterval (-32364110556 / 1000000000000) (-32364108108 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 0) <| besselDerivativeNearFromState (179257226317719 / 8000000000000) 0 (IntervalRat.scale (417 / 4) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-156826167804 / 1000000000000) (-156826167803 / 1000000000000), orderedInterval (-58242423666 / 1000000000000) (-58242423665 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 0) <| besselDerivativeNearFromState (481510124504043 / 8000000000000) 0 (IntervalRat.scale (417 / 4) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-98578953729 / 1000000000000) (-98578953728 / 1000000000000), orderedInterval (-28488776893 / 1000000000000) (-28488776892 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 0) <| besselDerivativeNearFromState (1307393655087231 / 8000000000000) 0 (IntervalRat.scale (417 / 4) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (46726064980 / 1000000000000) (46726064981 / 1000000000000), orderedInterval (41235507136 / 1000000000000) (41235507137 / 1000000000000)))) (orderedInterval (-5219576180 / 1000000000000) (-5219576167 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 0) <| besselDerivativeNearFromState (963020249008503 / 8000000000000) 0 (IntervalRat.scale (417 / 4) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (71115598118 / 1000000000000) (71115598783 / 1000000000000), orderedInterval (-15495926972 / 1000000000000) (-15495926307 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 0) <| besselDerivativeNearFromState (1650151610830419 / 8000000000000) 0 (IntervalRat.scale (417 / 4) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-15959055169 / 1000000000000) (-15959054948 / 1000000000000), orderedInterval (53252159160 / 1000000000000) (53252159380 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 0) <| besselDerivativeNearFromState (1215494207868921 / 8000000000000) 0 (IntervalRat.scale (417 / 4) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (60714161171 / 1000000000000) (60714165288 / 1000000000000), orderedInterval (-22645378070 / 1000000000000) (-22645373952 / 1000000000000)))) (orderedInterval (1959582590 / 1000000000000) (1959582703 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate225_chunkChecks0_1 :
    compactCertificate225.chunkChecks (0 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 0) <| besselDerivativeNearFromState (1864880693234583 / 8000000000000) 0 (IntervalRat.scale (417 / 4) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (51642660579 / 1000000000000) (51642660587 / 1000000000000), orderedInterval (7890044169 / 1000000000000) (7890044177 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 0) <| besselDerivativeNearFromState (1076689370245407 / 8000000000000) 0 (IntervalRat.scale (417 / 4) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-19149200375 / 1000000000000) (-19149200374 / 1000000000000), orderedInterval (-65985938846 / 1000000000000) (-65985938845 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 0) <| besselDerivativeNearFromState (1910604181593963 / 8000000000000) 0 (IntervalRat.scale (417 / 4) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (38766388630 / 1000000000000) (38766388631 / 1000000000000), orderedInterval (34018596654 / 1000000000000) (34018596655 / 1000000000000)))) (orderedInterval (-5084204888 / 1000000000000) (-5084204844 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 0) <| besselDerivativeNearFromState (1785134263501047 / 8000000000000) 0 (IntervalRat.scale (417 / 4) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-40947054583 / 1000000000000) (-40947054582 / 1000000000000), orderedInterval (-34205781671 / 1000000000000) (-34205781670 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 0) <| besselDerivativeNearFromState (1273956043197351 / 8000000000000) 0 (IntervalRat.scale (417 / 4) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (12071875026 / 1000000000000) (12071875103 / 1000000000000), orderedInterval (-62102695362 / 1000000000000) (-62102695284 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 0) <| besselDerivativeNearFromState (1444530373512129 / 8000000000000) 0 (IntervalRat.scale (417 / 4) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-45051819893 / 1000000000000) (-45051721143 / 1000000000000), orderedInterval (38803118330 / 1000000000000) (38803217081 / 1000000000000)))) (orderedInterval (2108759450 / 1000000000000) (2108759971 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 0) <| besselDerivativeNearFromState (1204298825572401 / 8000000000000) 0 (IntervalRat.scale (417 / 4) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (32620754388 / 1000000000000) (32620754389 / 1000000000000), orderedInterval (56148920325 / 1000000000000) (56148920326 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 0) <| besselDerivativeNearFromState (1064034535112421 / 8000000000000) 0 (IntervalRat.scale (417 / 4) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (66657416163 / 1000000000000) (66657417637 / 1000000000000), orderedInterval (-18776758815 / 1000000000000) (-18776757341 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 0) <| besselDerivativeNearFromState (308398681013679 / 1600000000000) 0 (IntervalRat.scale (417 / 4) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-54443766963 / 1000000000000) (-54443763168 / 1000000000000), orderedInterval (18545249189 / 1000000000000) (18545252984 / 1000000000000)))) (orderedInterval (-4831864294 / 1000000000000) (-4831864102 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate225_chunkChecks0_2 :
    compactCertificate225.chunkChecks (0 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 0) <| besselDerivativeNearFromState (853046981817213 / 8000000000000) 0 (IntervalRat.scale (417 / 4) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (43688909905 / 1000000000000) (43688909906 / 1000000000000), orderedInterval (63525957805 / 1000000000000) (63525957806 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 0) <| besselDerivativeNearFromState (723137373723093 / 8000000000000) 0 (IntervalRat.scale (417 / 4) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-5869695408 / 1000000000000) (-5869695405 / 1000000000000), orderedInterval (-83684421134 / 1000000000000) (-83684421131 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 0) <| besselDerivativeNearFromState (452505792131079 / 8000000000000) 0 (IntervalRat.scale (417 / 4) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (75935689668 / 1000000000000) (75935689669 / 1000000000000), orderedInterval (73415055474 / 1000000000000) (73415055475 / 1000000000000)))) (orderedInterval (-4181195049 / 1000000000000) (-4181195022 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 0) <| besselDerivativeNearFromState (243359119974393 / 8000000000000) 0 (IntervalRat.scale (417 / 4) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-30825659634 / 1000000000000) (-30825659385 / 1000000000000), orderedInterval (141857486118 / 1000000000000) (141857486367 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 0) <| besselDerivativeNearFromState (660767350822179 / 8000000000000) 0 (IntervalRat.scale (417 / 4) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (87078652825 / 1000000000000) (87078653004 / 1000000000000), orderedInterval (-11699117025 / 1000000000000) (-11699116845 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 0) <| besselDerivativeNearFromState (902221326809283 / 8000000000000) 0 (IntervalRat.scale (417 / 4) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (33665501773 / 1000000000000) (33665501774 / 1000000000000), orderedInterval (67019021926 / 1000000000000) (67019021927 / 1000000000000)))) (orderedInterval (-3986427997 / 1000000000000) (-3986427975 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 0) <| besselDerivativeNearFromState (381494207868921 / 8000000000000) 0 (IntervalRat.scale (417 / 4) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-112623458072 / 1000000000000) (-112623458071 / 1000000000000), orderedInterval (-24613138597 / 1000000000000) (-24613138596 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 0) <| besselDerivativeNearFromState (1550752775062041 / 8000000000000) 0 (IntervalRat.scale (417 / 4) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-8557968497 / 1000000000000) (-8557968465 / 1000000000000), orderedInterval (56687372941 / 1000000000000) (56687372973 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 0) <| besselDerivativeNearFromState (1035830985556119 / 8000000000000) 0 (IntervalRat.scale (417 / 4) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-69673992120 / 1000000000000) (-69673992113 / 1000000000000), orderedInterval (-7622971377 / 1000000000000) (-7622971370 / 1000000000000)))) (orderedInterval (13090391842 / 1000000000000) (13090391876 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate225_chunkChecks0 :
    compactCertificate225.chunkChecks (0 : Fin 5) 0 9 = true :=
  compactCertificate225.chunkChecks_nine_of_three (0 : Fin 5) compactCertificate225_chunkChecks0_0
    compactCertificate225_chunkChecks0_1 compactCertificate225_chunkChecks0_2

theorem compactCertificate225_chunkChecks1_0 :
    compactCertificate225.chunkChecks (1 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 1) <| besselDerivativeNearFromState (417 / 4) 1 (IntervalRat.scale (417 / 4) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-76441675586 / 1000000000000) (-76441675584 / 1000000000000), orderedInterval (-15858995594 / 1000000000000) (-15858995592 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 1) <| besselDerivativeNearFromState (614320625274717 / 8000000000000) 1 (IntervalRat.scale (417 / 4) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (74898180799 / 1000000000000) (74898214406 / 1000000000000), orderedInterval (-52262079099 / 1000000000000) (-52262045491 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 1) <| besselDerivativeNearFromState (198658668200061 / 1600000000000) 1 (IntervalRat.scale (417 / 4) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-47088589039 / 1000000000000) (-47088552820 / 1000000000000), orderedInterval (54134182530 / 1000000000000) (54134218749 / 1000000000000)))) (orderedInterval (-2861264579 / 1000000000000) (-2861261807 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 1) <| besselDerivativeNearFromState (179257226317719 / 8000000000000) 1 (IntervalRat.scale (417 / 4) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-156826167804 / 1000000000000) (-156826167803 / 1000000000000), orderedInterval (-58242423666 / 1000000000000) (-58242423665 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 1) <| besselDerivativeNearFromState (481510124504043 / 8000000000000) 1 (IntervalRat.scale (417 / 4) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-98578953729 / 1000000000000) (-98578953728 / 1000000000000), orderedInterval (-28488776893 / 1000000000000) (-28488776892 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 1) <| besselDerivativeNearFromState (1307393655087231 / 8000000000000) 1 (IntervalRat.scale (417 / 4) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (46726064980 / 1000000000000) (46726064981 / 1000000000000), orderedInterval (41235507136 / 1000000000000) (41235507137 / 1000000000000)))) (orderedInterval (-5060072699 / 1000000000000) (-5060072684 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 1) <| besselDerivativeNearFromState (963020249008503 / 8000000000000) 1 (IntervalRat.scale (417 / 4) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (71115598118 / 1000000000000) (71115598783 / 1000000000000), orderedInterval (-15495926972 / 1000000000000) (-15495926307 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 1) <| besselDerivativeNearFromState (1650151610830419 / 8000000000000) 1 (IntervalRat.scale (417 / 4) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-15959055169 / 1000000000000) (-15959054948 / 1000000000000), orderedInterval (53252159160 / 1000000000000) (53252159380 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 1) <| besselDerivativeNearFromState (1215494207868921 / 8000000000000) 1 (IntervalRat.scale (417 / 4) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (60714161171 / 1000000000000) (60714165288 / 1000000000000), orderedInterval (-22645378070 / 1000000000000) (-22645373952 / 1000000000000)))) (orderedInterval (-4047509329 / 1000000000000) (-4047509159 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate225_chunkChecks1_1 :
    compactCertificate225.chunkChecks (1 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 1) <| besselDerivativeNearFromState (1864880693234583 / 8000000000000) 1 (IntervalRat.scale (417 / 4) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (51642660579 / 1000000000000) (51642660587 / 1000000000000), orderedInterval (7890044169 / 1000000000000) (7890044177 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 1) <| besselDerivativeNearFromState (1076689370245407 / 8000000000000) 1 (IntervalRat.scale (417 / 4) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-19149200375 / 1000000000000) (-19149200374 / 1000000000000), orderedInterval (-65985938846 / 1000000000000) (-65985938845 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 1) <| besselDerivativeNearFromState (1910604181593963 / 8000000000000) 1 (IntervalRat.scale (417 / 4) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (38766388630 / 1000000000000) (38766388631 / 1000000000000), orderedInterval (34018596654 / 1000000000000) (34018596655 / 1000000000000)))) (orderedInterval (1632045072 / 1000000000000) (1632045162 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 1) <| besselDerivativeNearFromState (1785134263501047 / 8000000000000) 1 (IntervalRat.scale (417 / 4) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-40947054583 / 1000000000000) (-40947054582 / 1000000000000), orderedInterval (-34205781671 / 1000000000000) (-34205781670 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 1) <| besselDerivativeNearFromState (1273956043197351 / 8000000000000) 1 (IntervalRat.scale (417 / 4) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (12071875026 / 1000000000000) (12071875103 / 1000000000000), orderedInterval (-62102695362 / 1000000000000) (-62102695284 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 1) <| besselDerivativeNearFromState (1444530373512129 / 8000000000000) 1 (IntervalRat.scale (417 / 4) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-45051819893 / 1000000000000) (-45051721143 / 1000000000000), orderedInterval (38803118330 / 1000000000000) (38803217081 / 1000000000000)))) (orderedInterval (-7988905456 / 1000000000000) (-7988904559 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 1) <| besselDerivativeNearFromState (1204298825572401 / 8000000000000) 1 (IntervalRat.scale (417 / 4) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (32620754388 / 1000000000000) (32620754389 / 1000000000000), orderedInterval (56148920325 / 1000000000000) (56148920326 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 1) <| besselDerivativeNearFromState (1064034535112421 / 8000000000000) 1 (IntervalRat.scale (417 / 4) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (66657416163 / 1000000000000) (66657417637 / 1000000000000), orderedInterval (-18776758815 / 1000000000000) (-18776757341 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 1) <| besselDerivativeNearFromState (308398681013679 / 1600000000000) 1 (IntervalRat.scale (417 / 4) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-54443766963 / 1000000000000) (-54443763168 / 1000000000000), orderedInterval (18545249189 / 1000000000000) (18545252984 / 1000000000000)))) (orderedInterval (3185108086 / 1000000000000) (3185108388 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate225_chunkChecks1_2 :
    compactCertificate225.chunkChecks (1 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 1) <| besselDerivativeNearFromState (853046981817213 / 8000000000000) 1 (IntervalRat.scale (417 / 4) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (43688909905 / 1000000000000) (43688909906 / 1000000000000), orderedInterval (63525957805 / 1000000000000) (63525957806 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 1) <| besselDerivativeNearFromState (723137373723093 / 8000000000000) 1 (IntervalRat.scale (417 / 4) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-5869695408 / 1000000000000) (-5869695405 / 1000000000000), orderedInterval (-83684421134 / 1000000000000) (-83684421131 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 1) <| besselDerivativeNearFromState (452505792131079 / 8000000000000) 1 (IntervalRat.scale (417 / 4) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (75935689668 / 1000000000000) (75935689669 / 1000000000000), orderedInterval (73415055474 / 1000000000000) (73415055475 / 1000000000000)))) (orderedInterval (-4985607129 / 1000000000000) (-4985607104 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 1) <| besselDerivativeNearFromState (243359119974393 / 8000000000000) 1 (IntervalRat.scale (417 / 4) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-30825659634 / 1000000000000) (-30825659385 / 1000000000000), orderedInterval (141857486118 / 1000000000000) (141857486367 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 1) <| besselDerivativeNearFromState (660767350822179 / 8000000000000) 1 (IntervalRat.scale (417 / 4) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (87078652825 / 1000000000000) (87078653004 / 1000000000000), orderedInterval (-11699117025 / 1000000000000) (-11699116845 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 1) <| besselDerivativeNearFromState (902221326809283 / 8000000000000) 1 (IntervalRat.scale (417 / 4) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (33665501773 / 1000000000000) (33665501774 / 1000000000000), orderedInterval (67019021926 / 1000000000000) (67019021927 / 1000000000000)))) (orderedInterval (-6110462083 / 1000000000000) (-6110462066 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 1) <| besselDerivativeNearFromState (381494207868921 / 8000000000000) 1 (IntervalRat.scale (417 / 4) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-112623458072 / 1000000000000) (-112623458071 / 1000000000000), orderedInterval (-24613138597 / 1000000000000) (-24613138596 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 1) <| besselDerivativeNearFromState (1550752775062041 / 8000000000000) 1 (IntervalRat.scale (417 / 4) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-8557968497 / 1000000000000) (-8557968465 / 1000000000000), orderedInterval (56687372941 / 1000000000000) (56687372973 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 1) <| besselDerivativeNearFromState (1035830985556119 / 8000000000000) 1 (IntervalRat.scale (417 / 4) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-69673992120 / 1000000000000) (-69673992113 / 1000000000000), orderedInterval (-7622971377 / 1000000000000) (-7622971370 / 1000000000000)))) (orderedInterval (-6871655364 / 1000000000000) (-6871655316 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate225_chunkChecks1 :
    compactCertificate225.chunkChecks (1 : Fin 5) 0 9 = true :=
  compactCertificate225.chunkChecks_nine_of_three (1 : Fin 5) compactCertificate225_chunkChecks1_0
    compactCertificate225_chunkChecks1_1 compactCertificate225_chunkChecks1_2

theorem compactCertificate225_chunkChecks2_0 :
    compactCertificate225.chunkChecks (2 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 2) <| besselDerivativeNearFromState (417 / 4) 2 (IntervalRat.scale (417 / 4) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-76441675586 / 1000000000000) (-76441675584 / 1000000000000), orderedInterval (-15858995594 / 1000000000000) (-15858995592 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 2) <| besselDerivativeNearFromState (614320625274717 / 8000000000000) 2 (IntervalRat.scale (417 / 4) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (74898180799 / 1000000000000) (74898214406 / 1000000000000), orderedInterval (-52262079099 / 1000000000000) (-52262045491 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 2) <| besselDerivativeNearFromState (198658668200061 / 1600000000000) 2 (IntervalRat.scale (417 / 4) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-47088589039 / 1000000000000) (-47088552820 / 1000000000000), orderedInterval (54134182530 / 1000000000000) (54134218749 / 1000000000000)))) (orderedInterval (33867141079 / 1000000000000) (33867144301 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 2) <| besselDerivativeNearFromState (179257226317719 / 8000000000000) 2 (IntervalRat.scale (417 / 4) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-156826167804 / 1000000000000) (-156826167803 / 1000000000000), orderedInterval (-58242423666 / 1000000000000) (-58242423665 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 2) <| besselDerivativeNearFromState (481510124504043 / 8000000000000) 2 (IntervalRat.scale (417 / 4) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-98578953729 / 1000000000000) (-98578953728 / 1000000000000), orderedInterval (-28488776893 / 1000000000000) (-28488776892 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 2) <| besselDerivativeNearFromState (1307393655087231 / 8000000000000) 2 (IntervalRat.scale (417 / 4) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (46726064980 / 1000000000000) (46726064981 / 1000000000000), orderedInterval (41235507136 / 1000000000000) (41235507137 / 1000000000000)))) (orderedInterval (9332629651 / 1000000000000) (9332629672 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 2) <| besselDerivativeNearFromState (963020249008503 / 8000000000000) 2 (IntervalRat.scale (417 / 4) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (71115598118 / 1000000000000) (71115598783 / 1000000000000), orderedInterval (-15495926972 / 1000000000000) (-15495926307 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 2) <| besselDerivativeNearFromState (1650151610830419 / 8000000000000) 2 (IntervalRat.scale (417 / 4) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-15959055169 / 1000000000000) (-15959054948 / 1000000000000), orderedInterval (53252159160 / 1000000000000) (53252159380 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 2) <| besselDerivativeNearFromState (1215494207868921 / 8000000000000) 2 (IntervalRat.scale (417 / 4) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (60714161171 / 1000000000000) (60714165288 / 1000000000000), orderedInterval (-22645378070 / 1000000000000) (-22645373952 / 1000000000000)))) (orderedInterval (-5004998308 / 1000000000000) (-5004998049 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate225_chunkChecks2_1 :
    compactCertificate225.chunkChecks (2 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 2) <| besselDerivativeNearFromState (1864880693234583 / 8000000000000) 2 (IntervalRat.scale (417 / 4) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (51642660579 / 1000000000000) (51642660587 / 1000000000000), orderedInterval (7890044169 / 1000000000000) (7890044177 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 2) <| besselDerivativeNearFromState (1076689370245407 / 8000000000000) 2 (IntervalRat.scale (417 / 4) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-19149200375 / 1000000000000) (-19149200374 / 1000000000000), orderedInterval (-65985938846 / 1000000000000) (-65985938845 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 2) <| besselDerivativeNearFromState (1910604181593963 / 8000000000000) 2 (IntervalRat.scale (417 / 4) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (38766388630 / 1000000000000) (38766388631 / 1000000000000), orderedInterval (34018596654 / 1000000000000) (34018596655 / 1000000000000)))) (orderedInterval (19308312438 / 1000000000000) (19308312631 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 2) <| besselDerivativeNearFromState (1785134263501047 / 8000000000000) 2 (IntervalRat.scale (417 / 4) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-40947054583 / 1000000000000) (-40947054582 / 1000000000000), orderedInterval (-34205781671 / 1000000000000) (-34205781670 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 2) <| besselDerivativeNearFromState (1273956043197351 / 8000000000000) 2 (IntervalRat.scale (417 / 4) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (12071875026 / 1000000000000) (12071875103 / 1000000000000), orderedInterval (-62102695362 / 1000000000000) (-62102695284 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 2) <| besselDerivativeNearFromState (1444530373512129 / 8000000000000) 2 (IntervalRat.scale (417 / 4) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-45051819893 / 1000000000000) (-45051721143 / 1000000000000), orderedInterval (38803118330 / 1000000000000) (38803217081 / 1000000000000)))) (orderedInterval (-6657706630 / 1000000000000) (-6657705071 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 2) <| besselDerivativeNearFromState (1204298825572401 / 8000000000000) 2 (IntervalRat.scale (417 / 4) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (32620754388 / 1000000000000) (32620754389 / 1000000000000), orderedInterval (56148920325 / 1000000000000) (56148920326 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 2) <| besselDerivativeNearFromState (1064034535112421 / 8000000000000) 2 (IntervalRat.scale (417 / 4) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (66657416163 / 1000000000000) (66657417637 / 1000000000000), orderedInterval (-18776758815 / 1000000000000) (-18776757341 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 2) <| besselDerivativeNearFromState (308398681013679 / 1600000000000) 2 (IntervalRat.scale (417 / 4) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-54443766963 / 1000000000000) (-54443763168 / 1000000000000), orderedInterval (18545249189 / 1000000000000) (18545252984 / 1000000000000)))) (orderedInterval (10158328913 / 1000000000000) (10158329408 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate225_chunkChecks2_2 :
    compactCertificate225.chunkChecks (2 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 2) <| besselDerivativeNearFromState (853046981817213 / 8000000000000) 2 (IntervalRat.scale (417 / 4) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (43688909905 / 1000000000000) (43688909906 / 1000000000000), orderedInterval (63525957805 / 1000000000000) (63525957806 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 2) <| besselDerivativeNearFromState (723137373723093 / 8000000000000) 2 (IntervalRat.scale (417 / 4) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-5869695408 / 1000000000000) (-5869695405 / 1000000000000), orderedInterval (-83684421134 / 1000000000000) (-83684421131 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 2) <| besselDerivativeNearFromState (452505792131079 / 8000000000000) 2 (IntervalRat.scale (417 / 4) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (75935689668 / 1000000000000) (75935689669 / 1000000000000), orderedInterval (73415055474 / 1000000000000) (73415055475 / 1000000000000)))) (orderedInterval (6378543396 / 1000000000000) (6378543420 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 2) <| besselDerivativeNearFromState (243359119974393 / 8000000000000) 2 (IntervalRat.scale (417 / 4) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-30825659634 / 1000000000000) (-30825659385 / 1000000000000), orderedInterval (141857486118 / 1000000000000) (141857486367 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 2) <| besselDerivativeNearFromState (660767350822179 / 8000000000000) 2 (IntervalRat.scale (417 / 4) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (87078652825 / 1000000000000) (87078653004 / 1000000000000), orderedInterval (-11699117025 / 1000000000000) (-11699116845 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 2) <| besselDerivativeNearFromState (902221326809283 / 8000000000000) 2 (IntervalRat.scale (417 / 4) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (33665501773 / 1000000000000) (33665501774 / 1000000000000), orderedInterval (67019021926 / 1000000000000) (67019021927 / 1000000000000)))) (orderedInterval (4269685739 / 1000000000000) (4269685754 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 2) <| besselDerivativeNearFromState (381494207868921 / 8000000000000) 2 (IntervalRat.scale (417 / 4) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-112623458072 / 1000000000000) (-112623458071 / 1000000000000), orderedInterval (-24613138597 / 1000000000000) (-24613138596 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 2) <| besselDerivativeNearFromState (1550752775062041 / 8000000000000) 2 (IntervalRat.scale (417 / 4) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-8557968497 / 1000000000000) (-8557968465 / 1000000000000), orderedInterval (56687372941 / 1000000000000) (56687372973 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 2) <| besselDerivativeNearFromState (1035830985556119 / 8000000000000) 2 (IntervalRat.scale (417 / 4) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-69673992120 / 1000000000000) (-69673992113 / 1000000000000), orderedInterval (-7622971377 / 1000000000000) (-7622971370 / 1000000000000)))) (orderedInterval (-22366162284 / 1000000000000) (-22366162212 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate225_chunkChecks2 :
    compactCertificate225.chunkChecks (2 : Fin 5) 0 9 = true :=
  compactCertificate225.chunkChecks_nine_of_three (2 : Fin 5) compactCertificate225_chunkChecks2_0
    compactCertificate225_chunkChecks2_1 compactCertificate225_chunkChecks2_2

theorem compactCertificate225_chunkChecks3_0 :
    compactCertificate225.chunkChecks (3 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 3) <| besselDerivativeNearFromState (417 / 4) 3 (IntervalRat.scale (417 / 4) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-76441675586 / 1000000000000) (-76441675584 / 1000000000000), orderedInterval (-15858995594 / 1000000000000) (-15858995592 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 3) <| besselDerivativeNearFromState (614320625274717 / 8000000000000) 3 (IntervalRat.scale (417 / 4) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (74898180799 / 1000000000000) (74898214406 / 1000000000000), orderedInterval (-52262079099 / 1000000000000) (-52262045491 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 3) <| besselDerivativeNearFromState (198658668200061 / 1600000000000) 3 (IntervalRat.scale (417 / 4) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-47088589039 / 1000000000000) (-47088552820 / 1000000000000), orderedInterval (54134182530 / 1000000000000) (54134218749 / 1000000000000)))) (orderedInterval (788778575 / 1000000000000) (788782333 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 3) <| besselDerivativeNearFromState (179257226317719 / 8000000000000) 3 (IntervalRat.scale (417 / 4) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-156826167804 / 1000000000000) (-156826167803 / 1000000000000), orderedInterval (-58242423666 / 1000000000000) (-58242423665 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 3) <| besselDerivativeNearFromState (481510124504043 / 8000000000000) 3 (IntervalRat.scale (417 / 4) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-98578953729 / 1000000000000) (-98578953728 / 1000000000000), orderedInterval (-28488776893 / 1000000000000) (-28488776892 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 3) <| besselDerivativeNearFromState (1307393655087231 / 8000000000000) 3 (IntervalRat.scale (417 / 4) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (46726064980 / 1000000000000) (46726064981 / 1000000000000), orderedInterval (41235507136 / 1000000000000) (41235507137 / 1000000000000)))) (orderedInterval (11396641899 / 1000000000000) (11396641930 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 3) <| besselDerivativeNearFromState (963020249008503 / 8000000000000) 3 (IntervalRat.scale (417 / 4) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (71115598118 / 1000000000000) (71115598783 / 1000000000000), orderedInterval (-15495926972 / 1000000000000) (-15495926307 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 3) <| besselDerivativeNearFromState (1650151610830419 / 8000000000000) 3 (IntervalRat.scale (417 / 4) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-15959055169 / 1000000000000) (-15959054948 / 1000000000000), orderedInterval (53252159160 / 1000000000000) (53252159380 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 3) <| besselDerivativeNearFromState (1215494207868921 / 8000000000000) 3 (IntervalRat.scale (417 / 4) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (60714161171 / 1000000000000) (60714165288 / 1000000000000), orderedInterval (-22645378070 / 1000000000000) (-22645373952 / 1000000000000)))) (orderedInterval (14464661278 / 1000000000000) (14464661675 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate225_chunkChecks3_1 :
    compactCertificate225.chunkChecks (3 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 3) <| besselDerivativeNearFromState (1864880693234583 / 8000000000000) 3 (IntervalRat.scale (417 / 4) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (51642660579 / 1000000000000) (51642660587 / 1000000000000), orderedInterval (7890044169 / 1000000000000) (7890044177 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 3) <| besselDerivativeNearFromState (1076689370245407 / 8000000000000) 3 (IntervalRat.scale (417 / 4) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-19149200375 / 1000000000000) (-19149200374 / 1000000000000), orderedInterval (-65985938846 / 1000000000000) (-65985938845 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 3) <| besselDerivativeNearFromState (1910604181593963 / 8000000000000) 3 (IntervalRat.scale (417 / 4) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (38766388630 / 1000000000000) (38766388631 / 1000000000000), orderedInterval (34018596654 / 1000000000000) (34018596655 / 1000000000000)))) (orderedInterval (-32133835533 / 1000000000000) (-32133835112 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 3) <| besselDerivativeNearFromState (1785134263501047 / 8000000000000) 3 (IntervalRat.scale (417 / 4) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-40947054583 / 1000000000000) (-40947054582 / 1000000000000), orderedInterval (-34205781671 / 1000000000000) (-34205781670 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 3) <| besselDerivativeNearFromState (1273956043197351 / 8000000000000) 3 (IntervalRat.scale (417 / 4) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (12071875026 / 1000000000000) (12071875103 / 1000000000000), orderedInterval (-62102695362 / 1000000000000) (-62102695284 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 3) <| besselDerivativeNearFromState (1444530373512129 / 8000000000000) 3 (IntervalRat.scale (417 / 4) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-45051819893 / 1000000000000) (-45051721143 / 1000000000000), orderedInterval (38803118330 / 1000000000000) (38803217081 / 1000000000000)))) (orderedInterval (15959062897 / 1000000000000) (15959065592 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 3) <| besselDerivativeNearFromState (1204298825572401 / 8000000000000) 3 (IntervalRat.scale (417 / 4) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (32620754388 / 1000000000000) (32620754389 / 1000000000000), orderedInterval (56148920325 / 1000000000000) (56148920326 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 3) <| besselDerivativeNearFromState (1064034535112421 / 8000000000000) 3 (IntervalRat.scale (417 / 4) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (66657416163 / 1000000000000) (66657417637 / 1000000000000), orderedInterval (-18776758815 / 1000000000000) (-18776757341 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 3) <| besselDerivativeNearFromState (308398681013679 / 1600000000000) 3 (IntervalRat.scale (417 / 4) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-54443766963 / 1000000000000) (-54443763168 / 1000000000000), orderedInterval (18545249189 / 1000000000000) (18545252984 / 1000000000000)))) (orderedInterval (-7282036421 / 1000000000000) (-7282035593 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate225_chunkChecks3_2 :
    compactCertificate225.chunkChecks (3 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 3) <| besselDerivativeNearFromState (853046981817213 / 8000000000000) 3 (IntervalRat.scale (417 / 4) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (43688909905 / 1000000000000) (43688909906 / 1000000000000), orderedInterval (63525957805 / 1000000000000) (63525957806 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 3) <| besselDerivativeNearFromState (723137373723093 / 8000000000000) 3 (IntervalRat.scale (417 / 4) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-5869695408 / 1000000000000) (-5869695405 / 1000000000000), orderedInterval (-83684421134 / 1000000000000) (-83684421131 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 3) <| besselDerivativeNearFromState (452505792131079 / 8000000000000) 3 (IntervalRat.scale (417 / 4) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (75935689668 / 1000000000000) (75935689669 / 1000000000000), orderedInterval (73415055474 / 1000000000000) (73415055475 / 1000000000000)))) (orderedInterval (7338233631 / 1000000000000) (7338233654 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 3) <| besselDerivativeNearFromState (243359119974393 / 8000000000000) 3 (IntervalRat.scale (417 / 4) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-30825659634 / 1000000000000) (-30825659385 / 1000000000000), orderedInterval (141857486118 / 1000000000000) (141857486367 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 3) <| besselDerivativeNearFromState (660767350822179 / 8000000000000) 3 (IntervalRat.scale (417 / 4) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (87078652825 / 1000000000000) (87078653004 / 1000000000000), orderedInterval (-11699117025 / 1000000000000) (-11699116845 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 3) <| besselDerivativeNearFromState (902221326809283 / 8000000000000) 3 (IntervalRat.scale (417 / 4) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (33665501773 / 1000000000000) (33665501774 / 1000000000000), orderedInterval (67019021926 / 1000000000000) (67019021927 / 1000000000000)))) (orderedInterval (6394180168 / 1000000000000) (6394180182 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 3) <| besselDerivativeNearFromState (381494207868921 / 8000000000000) 3 (IntervalRat.scale (417 / 4) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-112623458072 / 1000000000000) (-112623458071 / 1000000000000), orderedInterval (-24613138597 / 1000000000000) (-24613138596 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 3) <| besselDerivativeNearFromState (1550752775062041 / 8000000000000) 3 (IntervalRat.scale (417 / 4) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-8557968497 / 1000000000000) (-8557968465 / 1000000000000), orderedInterval (56687372941 / 1000000000000) (56687372973 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 3) <| besselDerivativeNearFromState (1035830985556119 / 8000000000000) 3 (IntervalRat.scale (417 / 4) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-69673992120 / 1000000000000) (-69673992113 / 1000000000000), orderedInterval (-7622971377 / 1000000000000) (-7622971370 / 1000000000000)))) (orderedInterval (27153251944 / 1000000000000) (27153252057 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate225_chunkChecks3 :
    compactCertificate225.chunkChecks (3 : Fin 5) 0 9 = true :=
  compactCertificate225.chunkChecks_nine_of_three (3 : Fin 5) compactCertificate225_chunkChecks3_0
    compactCertificate225_chunkChecks3_1 compactCertificate225_chunkChecks3_2

theorem compactCertificate225_chunkChecks4_0 :
    compactCertificate225.chunkChecks (4 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 4) <| besselDerivativeNearFromState (417 / 4) 4 (IntervalRat.scale (417 / 4) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-76441675586 / 1000000000000) (-76441675584 / 1000000000000), orderedInterval (-15858995594 / 1000000000000) (-15858995592 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 4) <| besselDerivativeNearFromState (614320625274717 / 8000000000000) 4 (IntervalRat.scale (417 / 4) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (74898180799 / 1000000000000) (74898214406 / 1000000000000), orderedInterval (-52262079099 / 1000000000000) (-52262045491 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 4) <| besselDerivativeNearFromState (198658668200061 / 1600000000000) 4 (IntervalRat.scale (417 / 4) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-47088589039 / 1000000000000) (-47088552820 / 1000000000000), orderedInterval (54134182530 / 1000000000000) (54134218749 / 1000000000000)))) (orderedInterval (-35665176859 / 1000000000000) (-35665172405 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 4) <| besselDerivativeNearFromState (179257226317719 / 8000000000000) 4 (IntervalRat.scale (417 / 4) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-156826167804 / 1000000000000) (-156826167803 / 1000000000000), orderedInterval (-58242423666 / 1000000000000) (-58242423665 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 4) <| besselDerivativeNearFromState (481510124504043 / 8000000000000) 4 (IntervalRat.scale (417 / 4) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-98578953729 / 1000000000000) (-98578953728 / 1000000000000), orderedInterval (-28488776893 / 1000000000000) (-28488776892 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 4) <| besselDerivativeNearFromState (1307393655087231 / 8000000000000) 4 (IntervalRat.scale (417 / 4) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (46726064980 / 1000000000000) (46726064981 / 1000000000000), orderedInterval (41235507136 / 1000000000000) (41235507137 / 1000000000000)))) (orderedInterval (-20673877400 / 1000000000000) (-20673877353 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 4) <| besselDerivativeNearFromState (963020249008503 / 8000000000000) 4 (IntervalRat.scale (417 / 4) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (71115598118 / 1000000000000) (71115598783 / 1000000000000), orderedInterval (-15495926972 / 1000000000000) (-15495926307 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 4) <| besselDerivativeNearFromState (1650151610830419 / 8000000000000) 4 (IntervalRat.scale (417 / 4) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-15959055169 / 1000000000000) (-15959054948 / 1000000000000), orderedInterval (53252159160 / 1000000000000) (53252159380 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 4) <| besselDerivativeNearFromState (1215494207868921 / 8000000000000) 4 (IntervalRat.scale (417 / 4) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (60714161171 / 1000000000000) (60714165288 / 1000000000000), orderedInterval (-22645378070 / 1000000000000) (-22645373952 / 1000000000000)))) (orderedInterval (13886485532 / 1000000000000) (13886486154 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate225_chunkChecks4_1 :
    compactCertificate225.chunkChecks (4 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 4) <| besselDerivativeNearFromState (1864880693234583 / 8000000000000) 4 (IntervalRat.scale (417 / 4) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (51642660579 / 1000000000000) (51642660587 / 1000000000000), orderedInterval (7890044169 / 1000000000000) (7890044177 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 4) <| besselDerivativeNearFromState (1076689370245407 / 8000000000000) 4 (IntervalRat.scale (417 / 4) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-19149200375 / 1000000000000) (-19149200374 / 1000000000000), orderedInterval (-65985938846 / 1000000000000) (-65985938845 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 4) <| besselDerivativeNearFromState (1910604181593963 / 8000000000000) 4 (IntervalRat.scale (417 / 4) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (38766388630 / 1000000000000) (38766388631 / 1000000000000), orderedInterval (34018596654 / 1000000000000) (34018596655 / 1000000000000)))) (orderedInterval (-80941274311 / 1000000000000) (-80941273376 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 4) <| besselDerivativeNearFromState (1785134263501047 / 8000000000000) 4 (IntervalRat.scale (417 / 4) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-40947054583 / 1000000000000) (-40947054582 / 1000000000000), orderedInterval (-34205781671 / 1000000000000) (-34205781670 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 4) <| besselDerivativeNearFromState (1273956043197351 / 8000000000000) 4 (IntervalRat.scale (417 / 4) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (12071875026 / 1000000000000) (12071875103 / 1000000000000), orderedInterval (-62102695362 / 1000000000000) (-62102695284 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 4) <| besselDerivativeNearFromState (1444530373512129 / 8000000000000) 4 (IntervalRat.scale (417 / 4) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-45051819893 / 1000000000000) (-45051721143 / 1000000000000), orderedInterval (38803118330 / 1000000000000) (38803217081 / 1000000000000)))) (orderedInterval (23476714807 / 1000000000000) (23476719494 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 4) <| besselDerivativeNearFromState (1204298825572401 / 8000000000000) 4 (IntervalRat.scale (417 / 4) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (32620754388 / 1000000000000) (32620754389 / 1000000000000), orderedInterval (56148920325 / 1000000000000) (56148920326 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 4) <| besselDerivativeNearFromState (1064034535112421 / 8000000000000) 4 (IntervalRat.scale (417 / 4) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (66657416163 / 1000000000000) (66657417637 / 1000000000000), orderedInterval (-18776758815 / 1000000000000) (-18776757341 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 4) <| besselDerivativeNearFromState (308398681013679 / 1600000000000) 4 (IntervalRat.scale (417 / 4) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-54443766963 / 1000000000000) (-54443763168 / 1000000000000), orderedInterval (18545249189 / 1000000000000) (18545252984 / 1000000000000)))) (orderedInterval (-24618174966 / 1000000000000) (-24618173538 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate225_chunkChecks4_2 :
    compactCertificate225.chunkChecks (4 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 4) <| besselDerivativeNearFromState (853046981817213 / 8000000000000) 4 (IntervalRat.scale (417 / 4) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (43688909905 / 1000000000000) (43688909906 / 1000000000000), orderedInterval (63525957805 / 1000000000000) (63525957806 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 4) <| besselDerivativeNearFromState (723137373723093 / 8000000000000) 4 (IntervalRat.scale (417 / 4) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-5869695408 / 1000000000000) (-5869695405 / 1000000000000), orderedInterval (-83684421134 / 1000000000000) (-83684421131 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 4) <| besselDerivativeNearFromState (452505792131079 / 8000000000000) 4 (IntervalRat.scale (417 / 4) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (75935689668 / 1000000000000) (75935689669 / 1000000000000), orderedInterval (73415055474 / 1000000000000) (73415055475 / 1000000000000)))) (orderedInterval (-7384037134 / 1000000000000) (-7384037111 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 4) <| besselDerivativeNearFromState (243359119974393 / 8000000000000) 4 (IntervalRat.scale (417 / 4) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-30825659634 / 1000000000000) (-30825659385 / 1000000000000), orderedInterval (141857486118 / 1000000000000) (141857486367 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 4) <| besselDerivativeNearFromState (660767350822179 / 8000000000000) 4 (IntervalRat.scale (417 / 4) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (87078652825 / 1000000000000) (87078653004 / 1000000000000), orderedInterval (-11699117025 / 1000000000000) (-11699116845 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 4) <| besselDerivativeNearFromState (902221326809283 / 8000000000000) 4 (IntervalRat.scale (417 / 4) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (33665501773 / 1000000000000) (33665501774 / 1000000000000), orderedInterval (67019021926 / 1000000000000) (67019021927 / 1000000000000)))) (orderedInterval (-4430209597 / 1000000000000) (-4430209582 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 4) <| besselDerivativeNearFromState (381494207868921 / 8000000000000) 4 (IntervalRat.scale (417 / 4) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-112623458072 / 1000000000000) (-112623458071 / 1000000000000), orderedInterval (-24613138597 / 1000000000000) (-24613138596 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 4) <| besselDerivativeNearFromState (1550752775062041 / 8000000000000) 4 (IntervalRat.scale (417 / 4) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-8557968497 / 1000000000000) (-8557968465 / 1000000000000), orderedInterval (56687372941 / 1000000000000) (56687372973 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 4) <| besselDerivativeNearFromState (1035830985556119 / 8000000000000) 4 (IntervalRat.scale (417 / 4) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-69673992120 / 1000000000000) (-69673992113 / 1000000000000), orderedInterval (-7622971377 / 1000000000000) (-7622971370 / 1000000000000)))) (orderedInterval (38881591832 / 1000000000000) (38881592016 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate225_chunkChecks4 :
    compactCertificate225.chunkChecks (4 : Fin 5) 0 9 = true :=
  compactCertificate225.chunkChecks_nine_of_three (4 : Fin 5) compactCertificate225_chunkChecks4_0
    compactCertificate225_chunkChecks4_1 compactCertificate225_chunkChecks4_2

theorem compactCertificate225_chunks :
    ∀ r : Fin 5, ∀ b, compactCertificate225.chunkCheck r b = true :=
  compactCertificate225.chunkChecks_all (by
    intro r
    fin_cases r
    · exact compactCertificate225_chunkChecks0
    · exact compactCertificate225_chunkChecks1
    · exact compactCertificate225_chunkChecks2
    · exact compactCertificate225_chunkChecks3
    · exact compactCertificate225_chunkChecks4)

theorem compactCertificate225_coefficient0 :
    compactCertificate225.coefficientCheck (0 : Fin 5) = true := by
  norm_num [CompactCertificate.coefficientCheck, intervalFinSumHull,
    compactCertificate225, rationalIntervalSubset, orderedInterval, Fin.sum_univ_succ]

theorem compactCertificate225_coefficient1 :
    compactCertificate225.coefficientCheck (1 : Fin 5) = true := by
  norm_num [CompactCertificate.coefficientCheck, intervalFinSumHull,
    compactCertificate225, rationalIntervalSubset, orderedInterval, Fin.sum_univ_succ]

theorem compactCertificate225_coefficient2 :
    compactCertificate225.coefficientCheck (2 : Fin 5) = true := by
  norm_num [CompactCertificate.coefficientCheck, intervalFinSumHull,
    compactCertificate225, rationalIntervalSubset, orderedInterval, Fin.sum_univ_succ]

theorem compactCertificate225_coefficient3 :
    compactCertificate225.coefficientCheck (3 : Fin 5) = true := by
  norm_num [CompactCertificate.coefficientCheck, intervalFinSumHull,
    compactCertificate225, rationalIntervalSubset, orderedInterval, Fin.sum_univ_succ]

theorem compactCertificate225_coefficient4 :
    compactCertificate225.coefficientCheck (4 : Fin 5) = true := by
  norm_num [CompactCertificate.coefficientCheck, intervalFinSumHull,
    compactCertificate225, rationalIntervalSubset, orderedInterval, Fin.sum_univ_succ]

theorem compactCertificate225_coefficients : ∀ r : Fin 5,
    compactCertificate225.coefficientCheck r = true := by
  intro r
  fin_cases r
  · exact compactCertificate225_coefficient0
  · exact compactCertificate225_coefficient1
  · exact compactCertificate225_coefficient2
  · exact compactCertificate225_coefficient3
  · exact compactCertificate225_coefficient4

theorem compactCertificate225_lower : (1 : ℚ) ≤ compactCertificate225.output.lo := by
  norm_num [CompactCertificate.output, CompactCertificate.interval,
    CompactCertificate.coefficientTargetNat, compactCertificate225, dualConstant,
    intervalTaylorSum, intervalPow, intervalSub, intervalMaxAbs, widenInterval,
    rationalErrorInterval, orderedInterval, IntervalRat.add, IntervalRat.mul, IntervalRat.scale,
    IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4]

theorem compactCertificate225_proves {t : ℝ} (ht : t ∈ compactCertificate225.interval) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t :=
  compactCertificate225.proves compactCertificate225_states compactCertificate225_chunks
    compactCertificate225_coefficients compactCertificate225_lower ht

end Erdos232
