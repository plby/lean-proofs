/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, OpenAI Codex
-/
import ErdosProblems.Erdos232.CompactBase

open LeanCert.Core
namespace Erdos232

def compactCertificate258 : CompactCertificate where
  left := 133
  right := 134
  center := 267 / 2
  grid := fun i =>
    match i.val with
    | 0 => 43
    | 1 => 31
    | 2 => 51
    | 3 => 9
    | 4 => 25
    | 5 => 67
    | 6 => 49
    | 7 => 84
    | 8 => 62
    | 9 => 95
    | 10 => 55
    | 11 => 97
    | 12 => 91
    | 13 => 65
    | 14 => 74
    | 15 => 61
    | 16 => 54
    | 17 => 79
    | 18 => 43
    | 19 => 37
    | 20 => 23
    | 21 => 12
    | 22 => 34
    | 23 => 46
    | 24 => 19
    | 25 => 79
    | _ => 53
  point := fun i =>
    match i.val with
    | 0 => 267 / 2
    | 1 => 393341983089567 / 4000000000000
    | 2 => 127198715610111 / 800000000000
    | 3 => 114776209656669 / 4000000000000
    | 4 => 308305043747193 / 4000000000000
    | 5 => 837108167645781 / 4000000000000
    | 6 => 616610087494653 / 4000000000000
    | 7 => 1056571894704369 / 4000000000000
    | 8 => 778266075541971 / 4000000000000
    | 9 => 1194060299984733 / 4000000000000
    | 10 => 689391035624757 / 4000000000000
    | 11 => 1223336490373113 / 4000000000000
    | 12 => 1142999636342397 / 4000000000000
    | 13 => 815698473701901 / 4000000000000
    | 14 => 924915131241579 / 4000000000000
    | 15 => 771097809179451 / 4000000000000
    | 16 => 681288299460471 / 4000000000000
    | 17 => 197463903670629 / 800000000000
    | 18 => 546195549508863 / 4000000000000
    | 19 => 463016016268743 / 4000000000000
    | 20 => 289733924458029 / 4000000000000
    | 21 => 155819868185043 / 4000000000000
    | 22 => 423081253404129 / 4000000000000
    | 23 => 577681281194433 / 4000000000000
    | 24 => 244266075541971 / 4000000000000
    | 25 => 992928035831091 / 4000000000000
    | _ => 663229911615069 / 4000000000000
  state := fun i =>
    match i.val with
    | 0 => (orderedInterval (49730416851 / 1000000000000) (49730491105 / 1000000000000), orderedInterval (-48098374840 / 1000000000000) (-48098300586 / 1000000000000))
    | 1 => (orderedInterval (-79439670062 / 1000000000000) (-79439669758 / 1000000000000), orderedInterval (13179528503 / 1000000000000) (13179528807 / 1000000000000))
    | 2 => (orderedInterval (26849953242 / 1000000000000) (26849955040 / 1000000000000), orderedInterval (-57382174591 / 1000000000000) (-57382172793 / 1000000000000))
    | 3 => (orderedInterval (-138859004326 / 1000000000000) (-138859004325 / 1000000000000), orderedInterval (-51452840641 / 1000000000000) (-51452840640 / 1000000000000))
    | 4 => (orderedInterval (57129967124 / 1000000000000) (57129998846 / 1000000000000), orderedInterval (-71051652277 / 1000000000000) (-71051620555 / 1000000000000))
    | 5 => (orderedInterval (22734441816 / 1000000000000) (22734442965 / 1000000000000), orderedInterval (-50305149029 / 1000000000000) (-50305147880 / 1000000000000))
    | 6 => (orderedInterval (-54043430132 / 1000000000000) (-54043430131 / 1000000000000), orderedInterval (-34596869854 / 1000000000000) (-34596869853 / 1000000000000))
    | 7 => (orderedInterval (42191098342 / 1000000000000) (42191098343 / 1000000000000), orderedInterval (25020782429 / 1000000000000) (25020782430 / 1000000000000))
    | 8 => (orderedInterval (30989355564 / 1000000000000) (30989355565 / 1000000000000), orderedInterval (48000033472 / 1000000000000) (48000033473 / 1000000000000))
    | 9 => (orderedInterval (-34656290662 / 1000000000000) (-34656290661 / 1000000000000), orderedInterval (-30463469235 / 1000000000000) (-30463469234 / 1000000000000))
    | 10 => (orderedInterval (-20545052212 / 1000000000000) (-20545052211 / 1000000000000), orderedInterval (-57139367498 / 1000000000000) (-57139367497 / 1000000000000))
    | 11 => (orderedInterval (-43396013051 / 1000000000000) (-43396006952 / 1000000000000), orderedInterval (14155304466 / 1000000000000) (14155310565 / 1000000000000))
    | 12 => (orderedInterval (-28562788817 / 1000000000000) (-28562788816 / 1000000000000), orderedInterval (-37527400784 / 1000000000000) (-37527400783 / 1000000000000))
    | 13 => (orderedInterval (-27075010629 / 1000000000000) (-27075010628 / 1000000000000), orderedInterval (-48808839425 / 1000000000000) (-48808839424 / 1000000000000))
    | 14 => (orderedInterval (-23492376191 / 1000000000000) (-23492374595 / 1000000000000), orderedInterval (46968972723 / 1000000000000) (46968974320 / 1000000000000))
    | 15 => (orderedInterval (-53957695501 / 1000000000000) (-53957690535 / 1000000000000), orderedInterval (19912813247 / 1000000000000) (19912818213 / 1000000000000))
    | 16 => (orderedInterval (60767022475 / 1000000000000) (60767022486 / 1000000000000), orderedInterval (6536826010 / 1000000000000) (6536826020 / 1000000000000))
    | 17 => (orderedInterval (27450351662 / 1000000000000) (27450356406 / 1000000000000), orderedInterval (-42783405021 / 1000000000000) (-42783400277 / 1000000000000))
    | 18 => (orderedInterval (-53345651113 / 1000000000000) (-53345571013 / 1000000000000), orderedInterval (42815122005 / 1000000000000) (42815202106 / 1000000000000))
    | 19 => (orderedInterval (-21872871177 / 1000000000000) (-21872871176 / 1000000000000), orderedInterval (-70767249607 / 1000000000000) (-70767249606 / 1000000000000))
    | 20 => (orderedInterval (-76826230037 / 1000000000000) (-76826230036 / 1000000000000), orderedInterval (-53197580644 / 1000000000000) (-53197580643 / 1000000000000))
    | 21 => (orderedInterval (114130081469 / 1000000000000) (114130089025 / 1000000000000), orderedInterval (-59049197793 / 1000000000000) (-59049190236 / 1000000000000))
    | 22 => (orderedInterval (-19916126276 / 1000000000000) (-19916125995 / 1000000000000), orderedInterval (75076112032 / 1000000000000) (75076112314 / 1000000000000))
    | 23 => (orderedInterval (42343247393 / 1000000000000) (42343247394 / 1000000000000), orderedInterval (50992021939 / 1000000000000) (50992021940 / 1000000000000))
    | 24 => (orderedInterval (-84907454679 / 1000000000000) (-84907427598 / 1000000000000), orderedInterval (57401527340 / 1000000000000) (57401554420 / 1000000000000))
    | 25 => (orderedInterval (-37407333852 / 1000000000000) (-37407333851 / 1000000000000), orderedInterval (-34061244017 / 1000000000000) (-34061244016 / 1000000000000))
    | _ => (orderedInterval (-5427962310 / 1000000000000) (-5427962309 / 1000000000000), orderedInterval (-61709365902 / 1000000000000) (-61709365900 / 1000000000000))
  chunkTarget := fun r b =>
    match r.val with
    | 0 =>
      match b.val with
      | 0 => orderedInterval (20546758575 / 1000000000000) (20546788125 / 1000000000000)
      | 1 => orderedInterval (1976253197 / 1000000000000) (1976254454 / 1000000000000)
      | 2 => orderedInterval (-552390702 / 1000000000000) (-552390693 / 1000000000000)
      | 3 => orderedInterval (-1533213865 / 1000000000000) (-1533212944 / 1000000000000)
      | 4 => orderedInterval (-1925759180 / 1000000000000) (-1925759156 / 1000000000000)
      | 5 => orderedInterval (-3397743005 / 1000000000000) (-3397742812 / 1000000000000)
      | 6 => orderedInterval (7266458409 / 1000000000000) (7266471251 / 1000000000000)
      | 7 => orderedInterval (-4900729686 / 1000000000000) (-4900729523 / 1000000000000)
      | _ => orderedInterval (3551603160 / 1000000000000) (3551603361 / 1000000000000)
    | 1 =>
      match b.val with
      | 0 => orderedInterval (-22984446244 / 1000000000000) (-22984416673 / 1000000000000)
      | 1 => orderedInterval (4228287083 / 1000000000000) (4228287899 / 1000000000000)
      | 2 => orderedInterval (163745693 / 1000000000000) (163745707 / 1000000000000)
      | 3 => orderedInterval (11248187334 / 1000000000000) (11248189432 / 1000000000000)
      | 4 => orderedInterval (-6011866935 / 1000000000000) (-6011866894 / 1000000000000)
      | 5 => orderedInterval (-2170560373 / 1000000000000) (-2170560045 / 1000000000000)
      | 6 => orderedInterval (-4468847083 / 1000000000000) (-4468833951 / 1000000000000)
      | 7 => orderedInterval (-5258938098 / 1000000000000) (-5258938037 / 1000000000000)
      | _ => orderedInterval (19694094697 / 1000000000000) (19694094825 / 1000000000000)
    | 2 =>
      match b.val with
      | 0 => orderedInterval (-21372568383 / 1000000000000) (-21372538566 / 1000000000000)
      | 1 => orderedInterval (3175076771 / 1000000000000) (3175077389 / 1000000000000)
      | 2 => orderedInterval (3502495344 / 1000000000000) (3502495368 / 1000000000000)
      | 3 => orderedInterval (4038812801 / 1000000000000) (4038817603 / 1000000000000)
      | 4 => orderedInterval (3299944099 / 1000000000000) (3299944167 / 1000000000000)
      | 5 => orderedInterval (4573230867 / 1000000000000) (4573231434 / 1000000000000)
      | 6 => orderedInterval (-9084598857 / 1000000000000) (-9084585329 / 1000000000000)
      | 7 => orderedInterval (3732964652 / 1000000000000) (3732964684 / 1000000000000)
      | _ => orderedInterval (-12139370805 / 1000000000000) (-12139370692 / 1000000000000)
    | 3 =>
      match b.val with
      | 0 => orderedInterval (24862865598 / 1000000000000) (24862895442 / 1000000000000)
      | 1 => orderedInterval (-13306357841 / 1000000000000) (-13306357261 / 1000000000000)
      | 2 => orderedInterval (2360392489 / 1000000000000) (2360392532 / 1000000000000)
      | 3 => orderedInterval (-75633010672 / 1000000000000) (-75632999696 / 1000000000000)
      | 4 => orderedInterval (11016946290 / 1000000000000) (11016946406 / 1000000000000)
      | 5 => orderedInterval (6973702485 / 1000000000000) (6973703474 / 1000000000000)
      | 6 => orderedInterval (5059030324 / 1000000000000) (5059044157 / 1000000000000)
      | 7 => orderedInterval (5739306867 / 1000000000000) (5739306890 / 1000000000000)
      | _ => orderedInterval (-39948525783 / 1000000000000) (-39948525646 / 1000000000000)
    | _ =>
      match b.val with
      | 0 => orderedInterval (22290027507 / 1000000000000) (22290057607 / 1000000000000)
      | 1 => orderedInterval (-9325541314 / 1000000000000) (-9325540626 / 1000000000000)
      | 2 => orderedInterval (-16600545198 / 1000000000000) (-16600545119 / 1000000000000)
      | 3 => orderedInterval (-19060629802 / 1000000000000) (-19060604617 / 1000000000000)
      | 4 => orderedInterval (-2210663992 / 1000000000000) (-2210663791 / 1000000000000)
      | 5 => orderedInterval (-3813443408 / 1000000000000) (-3813441656 / 1000000000000)
      | 6 => orderedInterval (9742546789 / 1000000000000) (9742561039 / 1000000000000)
      | 7 => orderedInterval (-4367496863 / 1000000000000) (-4367496843 / 1000000000000)
      | _ => orderedInterval (39398374099 / 1000000000000) (39398374298 / 1000000000000)
  coefficientTarget := fun i =>
    match i.val with
    | 0 => orderedInterval (21031236903 / 1000000000000) (21031282063 / 1000000000000)
    | 1 => orderedInterval (-5560343926 / 1000000000000) (-5560297737 / 1000000000000)
    | 2 => orderedInterval (-20274013511 / 1000000000000) (-20273963942 / 1000000000000)
    | 3 => orderedInterval (-72875650243 / 1000000000000) (-72875593702 / 1000000000000)
    | _ => orderedInterval (16052627818 / 1000000000000) (16052700292 / 1000000000000)

theorem compactCertificate258_stateChecks0 :
    compactCertificate258.stateChecks 0 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 43 12 (267 / 2)) (orderedInterval (49730416851 / 1000000000000) (49730491105 / 1000000000000), orderedInterval (-48098374840 / 1000000000000) (-48098300586 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 31 12 (393341983089567 / 4000000000000)) (orderedInterval (-79439670062 / 1000000000000) (-79439669758 / 1000000000000), orderedInterval (13179528503 / 1000000000000) (13179528807 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 51 12 (127198715610111 / 800000000000)) (orderedInterval (26849953242 / 1000000000000) (26849955040 / 1000000000000), orderedInterval (-57382174591 / 1000000000000) (-57382172793 / 1000000000000))) = true
  norm_num [besselStateAtRationalPoint, besselIntervalStepZero,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, besselZeroTransition,
    besselInitial, besselGridStateAt, besselGridStateBlock00, besselGridStateBlock01,
    besselGridStateBlock02, besselGridStateBlock03, besselGridStateBlock04,
    besselGridStateBlock05, besselGridStateBlock06, besselGridStateBlock07,
    besselGridStateBlock08, besselGridStateBlock09, besselGridStateBlock10,
    besselGridStateBlock11, besselGridStateBlock12, besselGridStateBlock13,
    besselGridStateBlock14, besselGridState009, besselGridState012, besselGridState019, besselGridState023, besselGridState025, besselGridState031, besselGridState034, besselGridState037, besselGridState043, besselGridState046, besselGridState049, besselGridState051, besselGridState053, besselGridState054, besselGridState055, besselGridState061, besselGridState062, besselGridState065, besselGridState067, besselGridState074, besselGridState079, besselGridState084, besselGridState091, besselGridState095, besselGridState097, besselStateSubset, linearInterval, widenInterval,
    rationalErrorInterval, rationalIntervalSubset, orderedInterval, Finset.sum_range_succ,
    IntervalRat.add, IntervalRat.mul, IntervalRat.scale, IntervalRat.singleton]

theorem compactCertificate258_stateChecks1 :
    compactCertificate258.stateChecks 3 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 9 12 (114776209656669 / 4000000000000)) (orderedInterval (-138859004326 / 1000000000000) (-138859004325 / 1000000000000), orderedInterval (-51452840641 / 1000000000000) (-51452840640 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 25 12 (308305043747193 / 4000000000000)) (orderedInterval (57129967124 / 1000000000000) (57129998846 / 1000000000000), orderedInterval (-71051652277 / 1000000000000) (-71051620555 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 67 12 (837108167645781 / 4000000000000)) (orderedInterval (22734441816 / 1000000000000) (22734442965 / 1000000000000), orderedInterval (-50305149029 / 1000000000000) (-50305147880 / 1000000000000))) = true
  norm_num [besselStateAtRationalPoint, besselIntervalStepZero,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, besselZeroTransition,
    besselInitial, besselGridStateAt, besselGridStateBlock00, besselGridStateBlock01,
    besselGridStateBlock02, besselGridStateBlock03, besselGridStateBlock04,
    besselGridStateBlock05, besselGridStateBlock06, besselGridStateBlock07,
    besselGridStateBlock08, besselGridStateBlock09, besselGridStateBlock10,
    besselGridStateBlock11, besselGridStateBlock12, besselGridStateBlock13,
    besselGridStateBlock14, besselGridState009, besselGridState012, besselGridState019, besselGridState023, besselGridState025, besselGridState031, besselGridState034, besselGridState037, besselGridState043, besselGridState046, besselGridState049, besselGridState051, besselGridState053, besselGridState054, besselGridState055, besselGridState061, besselGridState062, besselGridState065, besselGridState067, besselGridState074, besselGridState079, besselGridState084, besselGridState091, besselGridState095, besselGridState097, besselStateSubset, linearInterval, widenInterval,
    rationalErrorInterval, rationalIntervalSubset, orderedInterval, Finset.sum_range_succ,
    IntervalRat.add, IntervalRat.mul, IntervalRat.scale, IntervalRat.singleton]

theorem compactCertificate258_stateChecks2 :
    compactCertificate258.stateChecks 6 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 49 12 (616610087494653 / 4000000000000)) (orderedInterval (-54043430132 / 1000000000000) (-54043430131 / 1000000000000), orderedInterval (-34596869854 / 1000000000000) (-34596869853 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 84 12 (1056571894704369 / 4000000000000)) (orderedInterval (42191098342 / 1000000000000) (42191098343 / 1000000000000), orderedInterval (25020782429 / 1000000000000) (25020782430 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 62 12 (778266075541971 / 4000000000000)) (orderedInterval (30989355564 / 1000000000000) (30989355565 / 1000000000000), orderedInterval (48000033472 / 1000000000000) (48000033473 / 1000000000000))) = true
  norm_num [besselStateAtRationalPoint, besselIntervalStepZero,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, besselZeroTransition,
    besselInitial, besselGridStateAt, besselGridStateBlock00, besselGridStateBlock01,
    besselGridStateBlock02, besselGridStateBlock03, besselGridStateBlock04,
    besselGridStateBlock05, besselGridStateBlock06, besselGridStateBlock07,
    besselGridStateBlock08, besselGridStateBlock09, besselGridStateBlock10,
    besselGridStateBlock11, besselGridStateBlock12, besselGridStateBlock13,
    besselGridStateBlock14, besselGridState009, besselGridState012, besselGridState019, besselGridState023, besselGridState025, besselGridState031, besselGridState034, besselGridState037, besselGridState043, besselGridState046, besselGridState049, besselGridState051, besselGridState053, besselGridState054, besselGridState055, besselGridState061, besselGridState062, besselGridState065, besselGridState067, besselGridState074, besselGridState079, besselGridState084, besselGridState091, besselGridState095, besselGridState097, besselStateSubset, linearInterval, widenInterval,
    rationalErrorInterval, rationalIntervalSubset, orderedInterval, Finset.sum_range_succ,
    IntervalRat.add, IntervalRat.mul, IntervalRat.scale, IntervalRat.singleton]

theorem compactCertificate258_stateChecks3 :
    compactCertificate258.stateChecks 9 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 95 12 (1194060299984733 / 4000000000000)) (orderedInterval (-34656290662 / 1000000000000) (-34656290661 / 1000000000000), orderedInterval (-30463469235 / 1000000000000) (-30463469234 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 55 12 (689391035624757 / 4000000000000)) (orderedInterval (-20545052212 / 1000000000000) (-20545052211 / 1000000000000), orderedInterval (-57139367498 / 1000000000000) (-57139367497 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 97 12 (1223336490373113 / 4000000000000)) (orderedInterval (-43396013051 / 1000000000000) (-43396006952 / 1000000000000), orderedInterval (14155304466 / 1000000000000) (14155310565 / 1000000000000))) = true
  norm_num [besselStateAtRationalPoint, besselIntervalStepZero,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, besselZeroTransition,
    besselInitial, besselGridStateAt, besselGridStateBlock00, besselGridStateBlock01,
    besselGridStateBlock02, besselGridStateBlock03, besselGridStateBlock04,
    besselGridStateBlock05, besselGridStateBlock06, besselGridStateBlock07,
    besselGridStateBlock08, besselGridStateBlock09, besselGridStateBlock10,
    besselGridStateBlock11, besselGridStateBlock12, besselGridStateBlock13,
    besselGridStateBlock14, besselGridState009, besselGridState012, besselGridState019, besselGridState023, besselGridState025, besselGridState031, besselGridState034, besselGridState037, besselGridState043, besselGridState046, besselGridState049, besselGridState051, besselGridState053, besselGridState054, besselGridState055, besselGridState061, besselGridState062, besselGridState065, besselGridState067, besselGridState074, besselGridState079, besselGridState084, besselGridState091, besselGridState095, besselGridState097, besselStateSubset, linearInterval, widenInterval,
    rationalErrorInterval, rationalIntervalSubset, orderedInterval, Finset.sum_range_succ,
    IntervalRat.add, IntervalRat.mul, IntervalRat.scale, IntervalRat.singleton]

theorem compactCertificate258_stateChecks4 :
    compactCertificate258.stateChecks 12 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 91 12 (1142999636342397 / 4000000000000)) (orderedInterval (-28562788817 / 1000000000000) (-28562788816 / 1000000000000), orderedInterval (-37527400784 / 1000000000000) (-37527400783 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 65 12 (815698473701901 / 4000000000000)) (orderedInterval (-27075010629 / 1000000000000) (-27075010628 / 1000000000000), orderedInterval (-48808839425 / 1000000000000) (-48808839424 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 74 12 (924915131241579 / 4000000000000)) (orderedInterval (-23492376191 / 1000000000000) (-23492374595 / 1000000000000), orderedInterval (46968972723 / 1000000000000) (46968974320 / 1000000000000))) = true
  norm_num [besselStateAtRationalPoint, besselIntervalStepZero,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, besselZeroTransition,
    besselInitial, besselGridStateAt, besselGridStateBlock00, besselGridStateBlock01,
    besselGridStateBlock02, besselGridStateBlock03, besselGridStateBlock04,
    besselGridStateBlock05, besselGridStateBlock06, besselGridStateBlock07,
    besselGridStateBlock08, besselGridStateBlock09, besselGridStateBlock10,
    besselGridStateBlock11, besselGridStateBlock12, besselGridStateBlock13,
    besselGridStateBlock14, besselGridState009, besselGridState012, besselGridState019, besselGridState023, besselGridState025, besselGridState031, besselGridState034, besselGridState037, besselGridState043, besselGridState046, besselGridState049, besselGridState051, besselGridState053, besselGridState054, besselGridState055, besselGridState061, besselGridState062, besselGridState065, besselGridState067, besselGridState074, besselGridState079, besselGridState084, besselGridState091, besselGridState095, besselGridState097, besselStateSubset, linearInterval, widenInterval,
    rationalErrorInterval, rationalIntervalSubset, orderedInterval, Finset.sum_range_succ,
    IntervalRat.add, IntervalRat.mul, IntervalRat.scale, IntervalRat.singleton]

theorem compactCertificate258_stateChecks5 :
    compactCertificate258.stateChecks 15 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 61 12 (771097809179451 / 4000000000000)) (orderedInterval (-53957695501 / 1000000000000) (-53957690535 / 1000000000000), orderedInterval (19912813247 / 1000000000000) (19912818213 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 54 12 (681288299460471 / 4000000000000)) (orderedInterval (60767022475 / 1000000000000) (60767022486 / 1000000000000), orderedInterval (6536826010 / 1000000000000) (6536826020 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 79 12 (197463903670629 / 800000000000)) (orderedInterval (27450351662 / 1000000000000) (27450356406 / 1000000000000), orderedInterval (-42783405021 / 1000000000000) (-42783400277 / 1000000000000))) = true
  norm_num [besselStateAtRationalPoint, besselIntervalStepZero,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, besselZeroTransition,
    besselInitial, besselGridStateAt, besselGridStateBlock00, besselGridStateBlock01,
    besselGridStateBlock02, besselGridStateBlock03, besselGridStateBlock04,
    besselGridStateBlock05, besselGridStateBlock06, besselGridStateBlock07,
    besselGridStateBlock08, besselGridStateBlock09, besselGridStateBlock10,
    besselGridStateBlock11, besselGridStateBlock12, besselGridStateBlock13,
    besselGridStateBlock14, besselGridState009, besselGridState012, besselGridState019, besselGridState023, besselGridState025, besselGridState031, besselGridState034, besselGridState037, besselGridState043, besselGridState046, besselGridState049, besselGridState051, besselGridState053, besselGridState054, besselGridState055, besselGridState061, besselGridState062, besselGridState065, besselGridState067, besselGridState074, besselGridState079, besselGridState084, besselGridState091, besselGridState095, besselGridState097, besselStateSubset, linearInterval, widenInterval,
    rationalErrorInterval, rationalIntervalSubset, orderedInterval, Finset.sum_range_succ,
    IntervalRat.add, IntervalRat.mul, IntervalRat.scale, IntervalRat.singleton]

theorem compactCertificate258_stateChecks6 :
    compactCertificate258.stateChecks 18 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 43 12 (546195549508863 / 4000000000000)) (orderedInterval (-53345651113 / 1000000000000) (-53345571013 / 1000000000000), orderedInterval (42815122005 / 1000000000000) (42815202106 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 37 12 (463016016268743 / 4000000000000)) (orderedInterval (-21872871177 / 1000000000000) (-21872871176 / 1000000000000), orderedInterval (-70767249607 / 1000000000000) (-70767249606 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 23 12 (289733924458029 / 4000000000000)) (orderedInterval (-76826230037 / 1000000000000) (-76826230036 / 1000000000000), orderedInterval (-53197580644 / 1000000000000) (-53197580643 / 1000000000000))) = true
  norm_num [besselStateAtRationalPoint, besselIntervalStepZero,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, besselZeroTransition,
    besselInitial, besselGridStateAt, besselGridStateBlock00, besselGridStateBlock01,
    besselGridStateBlock02, besselGridStateBlock03, besselGridStateBlock04,
    besselGridStateBlock05, besselGridStateBlock06, besselGridStateBlock07,
    besselGridStateBlock08, besselGridStateBlock09, besselGridStateBlock10,
    besselGridStateBlock11, besselGridStateBlock12, besselGridStateBlock13,
    besselGridStateBlock14, besselGridState009, besselGridState012, besselGridState019, besselGridState023, besselGridState025, besselGridState031, besselGridState034, besselGridState037, besselGridState043, besselGridState046, besselGridState049, besselGridState051, besselGridState053, besselGridState054, besselGridState055, besselGridState061, besselGridState062, besselGridState065, besselGridState067, besselGridState074, besselGridState079, besselGridState084, besselGridState091, besselGridState095, besselGridState097, besselStateSubset, linearInterval, widenInterval,
    rationalErrorInterval, rationalIntervalSubset, orderedInterval, Finset.sum_range_succ,
    IntervalRat.add, IntervalRat.mul, IntervalRat.scale, IntervalRat.singleton]

theorem compactCertificate258_stateChecks7 :
    compactCertificate258.stateChecks 21 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 12 12 (155819868185043 / 4000000000000)) (orderedInterval (114130081469 / 1000000000000) (114130089025 / 1000000000000), orderedInterval (-59049197793 / 1000000000000) (-59049190236 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 34 12 (423081253404129 / 4000000000000)) (orderedInterval (-19916126276 / 1000000000000) (-19916125995 / 1000000000000), orderedInterval (75076112032 / 1000000000000) (75076112314 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 46 12 (577681281194433 / 4000000000000)) (orderedInterval (42343247393 / 1000000000000) (42343247394 / 1000000000000), orderedInterval (50992021939 / 1000000000000) (50992021940 / 1000000000000))) = true
  norm_num [besselStateAtRationalPoint, besselIntervalStepZero,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, besselZeroTransition,
    besselInitial, besselGridStateAt, besselGridStateBlock00, besselGridStateBlock01,
    besselGridStateBlock02, besselGridStateBlock03, besselGridStateBlock04,
    besselGridStateBlock05, besselGridStateBlock06, besselGridStateBlock07,
    besselGridStateBlock08, besselGridStateBlock09, besselGridStateBlock10,
    besselGridStateBlock11, besselGridStateBlock12, besselGridStateBlock13,
    besselGridStateBlock14, besselGridState009, besselGridState012, besselGridState019, besselGridState023, besselGridState025, besselGridState031, besselGridState034, besselGridState037, besselGridState043, besselGridState046, besselGridState049, besselGridState051, besselGridState053, besselGridState054, besselGridState055, besselGridState061, besselGridState062, besselGridState065, besselGridState067, besselGridState074, besselGridState079, besselGridState084, besselGridState091, besselGridState095, besselGridState097, besselStateSubset, linearInterval, widenInterval,
    rationalErrorInterval, rationalIntervalSubset, orderedInterval, Finset.sum_range_succ,
    IntervalRat.add, IntervalRat.mul, IntervalRat.scale, IntervalRat.singleton]

theorem compactCertificate258_stateChecks8 :
    compactCertificate258.stateChecks 24 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 19 12 (244266075541971 / 4000000000000)) (orderedInterval (-84907454679 / 1000000000000) (-84907427598 / 1000000000000), orderedInterval (57401527340 / 1000000000000) (57401554420 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 79 12 (992928035831091 / 4000000000000)) (orderedInterval (-37407333852 / 1000000000000) (-37407333851 / 1000000000000), orderedInterval (-34061244017 / 1000000000000) (-34061244016 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 53 12 (663229911615069 / 4000000000000)) (orderedInterval (-5427962310 / 1000000000000) (-5427962309 / 1000000000000), orderedInterval (-61709365902 / 1000000000000) (-61709365900 / 1000000000000))) = true
  norm_num [besselStateAtRationalPoint, besselIntervalStepZero,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, besselZeroTransition,
    besselInitial, besselGridStateAt, besselGridStateBlock00, besselGridStateBlock01,
    besselGridStateBlock02, besselGridStateBlock03, besselGridStateBlock04,
    besselGridStateBlock05, besselGridStateBlock06, besselGridStateBlock07,
    besselGridStateBlock08, besselGridStateBlock09, besselGridStateBlock10,
    besselGridStateBlock11, besselGridStateBlock12, besselGridStateBlock13,
    besselGridStateBlock14, besselGridState009, besselGridState012, besselGridState019, besselGridState023, besselGridState025, besselGridState031, besselGridState034, besselGridState037, besselGridState043, besselGridState046, besselGridState049, besselGridState051, besselGridState053, besselGridState054, besselGridState055, besselGridState061, besselGridState062, besselGridState065, besselGridState067, besselGridState074, besselGridState079, besselGridState084, besselGridState091, besselGridState095, besselGridState097, besselStateSubset, linearInterval, widenInterval,
    rationalErrorInterval, rationalIntervalSubset, orderedInterval, Finset.sum_range_succ,
    IntervalRat.add, IntervalRat.mul, IntervalRat.scale, IntervalRat.singleton]

theorem compactCertificate258_states : ∀ j,
    BesselStateValid (compactCertificate258.point j) (compactCertificate258.state j) :=
  compactCertificate258.statesValid_of_checks3 compactCertificate258_stateChecks0
    compactCertificate258_stateChecks1 compactCertificate258_stateChecks2
    compactCertificate258_stateChecks3 compactCertificate258_stateChecks4
    compactCertificate258_stateChecks5 compactCertificate258_stateChecks6
    compactCertificate258_stateChecks7 compactCertificate258_stateChecks8

theorem compactCertificate258_chunkChecks0_0 :
    compactCertificate258.chunkChecks (0 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 0) <| besselDerivativeNearFromState (267 / 2) 0 (IntervalRat.scale (267 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (49730416851 / 1000000000000) (49730491105 / 1000000000000), orderedInterval (-48098374840 / 1000000000000) (-48098300586 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 0) <| besselDerivativeNearFromState (393341983089567 / 4000000000000) 0 (IntervalRat.scale (267 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-79439670062 / 1000000000000) (-79439669758 / 1000000000000), orderedInterval (13179528503 / 1000000000000) (13179528807 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 0) <| besselDerivativeNearFromState (127198715610111 / 800000000000) 0 (IntervalRat.scale (267 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (26849953242 / 1000000000000) (26849955040 / 1000000000000), orderedInterval (-57382174591 / 1000000000000) (-57382172793 / 1000000000000)))) (orderedInterval (20546758575 / 1000000000000) (20546788125 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 0) <| besselDerivativeNearFromState (114776209656669 / 4000000000000) 0 (IntervalRat.scale (267 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-138859004326 / 1000000000000) (-138859004325 / 1000000000000), orderedInterval (-51452840641 / 1000000000000) (-51452840640 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 0) <| besselDerivativeNearFromState (308305043747193 / 4000000000000) 0 (IntervalRat.scale (267 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (57129967124 / 1000000000000) (57129998846 / 1000000000000), orderedInterval (-71051652277 / 1000000000000) (-71051620555 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 0) <| besselDerivativeNearFromState (837108167645781 / 4000000000000) 0 (IntervalRat.scale (267 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (22734441816 / 1000000000000) (22734442965 / 1000000000000), orderedInterval (-50305149029 / 1000000000000) (-50305147880 / 1000000000000)))) (orderedInterval (1976253197 / 1000000000000) (1976254454 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 0) <| besselDerivativeNearFromState (616610087494653 / 4000000000000) 0 (IntervalRat.scale (267 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-54043430132 / 1000000000000) (-54043430131 / 1000000000000), orderedInterval (-34596869854 / 1000000000000) (-34596869853 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 0) <| besselDerivativeNearFromState (1056571894704369 / 4000000000000) 0 (IntervalRat.scale (267 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (42191098342 / 1000000000000) (42191098343 / 1000000000000), orderedInterval (25020782429 / 1000000000000) (25020782430 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 0) <| besselDerivativeNearFromState (778266075541971 / 4000000000000) 0 (IntervalRat.scale (267 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (30989355564 / 1000000000000) (30989355565 / 1000000000000), orderedInterval (48000033472 / 1000000000000) (48000033473 / 1000000000000)))) (orderedInterval (-552390702 / 1000000000000) (-552390693 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate258_chunkChecks0_1 :
    compactCertificate258.chunkChecks (0 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 0) <| besselDerivativeNearFromState (1194060299984733 / 4000000000000) 0 (IntervalRat.scale (267 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-34656290662 / 1000000000000) (-34656290661 / 1000000000000), orderedInterval (-30463469235 / 1000000000000) (-30463469234 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 0) <| besselDerivativeNearFromState (689391035624757 / 4000000000000) 0 (IntervalRat.scale (267 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-20545052212 / 1000000000000) (-20545052211 / 1000000000000), orderedInterval (-57139367498 / 1000000000000) (-57139367497 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 0) <| besselDerivativeNearFromState (1223336490373113 / 4000000000000) 0 (IntervalRat.scale (267 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-43396013051 / 1000000000000) (-43396006952 / 1000000000000), orderedInterval (14155304466 / 1000000000000) (14155310565 / 1000000000000)))) (orderedInterval (-1533213865 / 1000000000000) (-1533212944 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 0) <| besselDerivativeNearFromState (1142999636342397 / 4000000000000) 0 (IntervalRat.scale (267 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-28562788817 / 1000000000000) (-28562788816 / 1000000000000), orderedInterval (-37527400784 / 1000000000000) (-37527400783 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 0) <| besselDerivativeNearFromState (815698473701901 / 4000000000000) 0 (IntervalRat.scale (267 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-27075010629 / 1000000000000) (-27075010628 / 1000000000000), orderedInterval (-48808839425 / 1000000000000) (-48808839424 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 0) <| besselDerivativeNearFromState (924915131241579 / 4000000000000) 0 (IntervalRat.scale (267 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-23492376191 / 1000000000000) (-23492374595 / 1000000000000), orderedInterval (46968972723 / 1000000000000) (46968974320 / 1000000000000)))) (orderedInterval (-1925759180 / 1000000000000) (-1925759156 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 0) <| besselDerivativeNearFromState (771097809179451 / 4000000000000) 0 (IntervalRat.scale (267 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-53957695501 / 1000000000000) (-53957690535 / 1000000000000), orderedInterval (19912813247 / 1000000000000) (19912818213 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 0) <| besselDerivativeNearFromState (681288299460471 / 4000000000000) 0 (IntervalRat.scale (267 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (60767022475 / 1000000000000) (60767022486 / 1000000000000), orderedInterval (6536826010 / 1000000000000) (6536826020 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 0) <| besselDerivativeNearFromState (197463903670629 / 800000000000) 0 (IntervalRat.scale (267 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (27450351662 / 1000000000000) (27450356406 / 1000000000000), orderedInterval (-42783405021 / 1000000000000) (-42783400277 / 1000000000000)))) (orderedInterval (-3397743005 / 1000000000000) (-3397742812 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate258_chunkChecks0_2 :
    compactCertificate258.chunkChecks (0 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 0) <| besselDerivativeNearFromState (546195549508863 / 4000000000000) 0 (IntervalRat.scale (267 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-53345651113 / 1000000000000) (-53345571013 / 1000000000000), orderedInterval (42815122005 / 1000000000000) (42815202106 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 0) <| besselDerivativeNearFromState (463016016268743 / 4000000000000) 0 (IntervalRat.scale (267 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-21872871177 / 1000000000000) (-21872871176 / 1000000000000), orderedInterval (-70767249607 / 1000000000000) (-70767249606 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 0) <| besselDerivativeNearFromState (289733924458029 / 4000000000000) 0 (IntervalRat.scale (267 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-76826230037 / 1000000000000) (-76826230036 / 1000000000000), orderedInterval (-53197580644 / 1000000000000) (-53197580643 / 1000000000000)))) (orderedInterval (7266458409 / 1000000000000) (7266471251 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 0) <| besselDerivativeNearFromState (155819868185043 / 4000000000000) 0 (IntervalRat.scale (267 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (114130081469 / 1000000000000) (114130089025 / 1000000000000), orderedInterval (-59049197793 / 1000000000000) (-59049190236 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 0) <| besselDerivativeNearFromState (423081253404129 / 4000000000000) 0 (IntervalRat.scale (267 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-19916126276 / 1000000000000) (-19916125995 / 1000000000000), orderedInterval (75076112032 / 1000000000000) (75076112314 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 0) <| besselDerivativeNearFromState (577681281194433 / 4000000000000) 0 (IntervalRat.scale (267 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (42343247393 / 1000000000000) (42343247394 / 1000000000000), orderedInterval (50992021939 / 1000000000000) (50992021940 / 1000000000000)))) (orderedInterval (-4900729686 / 1000000000000) (-4900729523 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 0) <| besselDerivativeNearFromState (244266075541971 / 4000000000000) 0 (IntervalRat.scale (267 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-84907454679 / 1000000000000) (-84907427598 / 1000000000000), orderedInterval (57401527340 / 1000000000000) (57401554420 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 0) <| besselDerivativeNearFromState (992928035831091 / 4000000000000) 0 (IntervalRat.scale (267 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-37407333852 / 1000000000000) (-37407333851 / 1000000000000), orderedInterval (-34061244017 / 1000000000000) (-34061244016 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 0) <| besselDerivativeNearFromState (663229911615069 / 4000000000000) 0 (IntervalRat.scale (267 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-5427962310 / 1000000000000) (-5427962309 / 1000000000000), orderedInterval (-61709365902 / 1000000000000) (-61709365900 / 1000000000000)))) (orderedInterval (3551603160 / 1000000000000) (3551603361 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate258_chunkChecks0 :
    compactCertificate258.chunkChecks (0 : Fin 5) 0 9 = true :=
  compactCertificate258.chunkChecks_nine_of_three (0 : Fin 5) compactCertificate258_chunkChecks0_0
    compactCertificate258_chunkChecks0_1 compactCertificate258_chunkChecks0_2

theorem compactCertificate258_chunkChecks1_0 :
    compactCertificate258.chunkChecks (1 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 1) <| besselDerivativeNearFromState (267 / 2) 1 (IntervalRat.scale (267 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (49730416851 / 1000000000000) (49730491105 / 1000000000000), orderedInterval (-48098374840 / 1000000000000) (-48098300586 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 1) <| besselDerivativeNearFromState (393341983089567 / 4000000000000) 1 (IntervalRat.scale (267 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-79439670062 / 1000000000000) (-79439669758 / 1000000000000), orderedInterval (13179528503 / 1000000000000) (13179528807 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 1) <| besselDerivativeNearFromState (127198715610111 / 800000000000) 1 (IntervalRat.scale (267 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (26849953242 / 1000000000000) (26849955040 / 1000000000000), orderedInterval (-57382174591 / 1000000000000) (-57382172793 / 1000000000000)))) (orderedInterval (-22984446244 / 1000000000000) (-22984416673 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 1) <| besselDerivativeNearFromState (114776209656669 / 4000000000000) 1 (IntervalRat.scale (267 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-138859004326 / 1000000000000) (-138859004325 / 1000000000000), orderedInterval (-51452840641 / 1000000000000) (-51452840640 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 1) <| besselDerivativeNearFromState (308305043747193 / 4000000000000) 1 (IntervalRat.scale (267 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (57129967124 / 1000000000000) (57129998846 / 1000000000000), orderedInterval (-71051652277 / 1000000000000) (-71051620555 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 1) <| besselDerivativeNearFromState (837108167645781 / 4000000000000) 1 (IntervalRat.scale (267 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (22734441816 / 1000000000000) (22734442965 / 1000000000000), orderedInterval (-50305149029 / 1000000000000) (-50305147880 / 1000000000000)))) (orderedInterval (4228287083 / 1000000000000) (4228287899 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 1) <| besselDerivativeNearFromState (616610087494653 / 4000000000000) 1 (IntervalRat.scale (267 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-54043430132 / 1000000000000) (-54043430131 / 1000000000000), orderedInterval (-34596869854 / 1000000000000) (-34596869853 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 1) <| besselDerivativeNearFromState (1056571894704369 / 4000000000000) 1 (IntervalRat.scale (267 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (42191098342 / 1000000000000) (42191098343 / 1000000000000), orderedInterval (25020782429 / 1000000000000) (25020782430 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 1) <| besselDerivativeNearFromState (778266075541971 / 4000000000000) 1 (IntervalRat.scale (267 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (30989355564 / 1000000000000) (30989355565 / 1000000000000), orderedInterval (48000033472 / 1000000000000) (48000033473 / 1000000000000)))) (orderedInterval (163745693 / 1000000000000) (163745707 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate258_chunkChecks1_1 :
    compactCertificate258.chunkChecks (1 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 1) <| besselDerivativeNearFromState (1194060299984733 / 4000000000000) 1 (IntervalRat.scale (267 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-34656290662 / 1000000000000) (-34656290661 / 1000000000000), orderedInterval (-30463469235 / 1000000000000) (-30463469234 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 1) <| besselDerivativeNearFromState (689391035624757 / 4000000000000) 1 (IntervalRat.scale (267 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-20545052212 / 1000000000000) (-20545052211 / 1000000000000), orderedInterval (-57139367498 / 1000000000000) (-57139367497 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 1) <| besselDerivativeNearFromState (1223336490373113 / 4000000000000) 1 (IntervalRat.scale (267 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-43396013051 / 1000000000000) (-43396006952 / 1000000000000), orderedInterval (14155304466 / 1000000000000) (14155310565 / 1000000000000)))) (orderedInterval (11248187334 / 1000000000000) (11248189432 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 1) <| besselDerivativeNearFromState (1142999636342397 / 4000000000000) 1 (IntervalRat.scale (267 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-28562788817 / 1000000000000) (-28562788816 / 1000000000000), orderedInterval (-37527400784 / 1000000000000) (-37527400783 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 1) <| besselDerivativeNearFromState (815698473701901 / 4000000000000) 1 (IntervalRat.scale (267 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-27075010629 / 1000000000000) (-27075010628 / 1000000000000), orderedInterval (-48808839425 / 1000000000000) (-48808839424 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 1) <| besselDerivativeNearFromState (924915131241579 / 4000000000000) 1 (IntervalRat.scale (267 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-23492376191 / 1000000000000) (-23492374595 / 1000000000000), orderedInterval (46968972723 / 1000000000000) (46968974320 / 1000000000000)))) (orderedInterval (-6011866935 / 1000000000000) (-6011866894 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 1) <| besselDerivativeNearFromState (771097809179451 / 4000000000000) 1 (IntervalRat.scale (267 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-53957695501 / 1000000000000) (-53957690535 / 1000000000000), orderedInterval (19912813247 / 1000000000000) (19912818213 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 1) <| besselDerivativeNearFromState (681288299460471 / 4000000000000) 1 (IntervalRat.scale (267 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (60767022475 / 1000000000000) (60767022486 / 1000000000000), orderedInterval (6536826010 / 1000000000000) (6536826020 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 1) <| besselDerivativeNearFromState (197463903670629 / 800000000000) 1 (IntervalRat.scale (267 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (27450351662 / 1000000000000) (27450356406 / 1000000000000), orderedInterval (-42783405021 / 1000000000000) (-42783400277 / 1000000000000)))) (orderedInterval (-2170560373 / 1000000000000) (-2170560045 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate258_chunkChecks1_2 :
    compactCertificate258.chunkChecks (1 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 1) <| besselDerivativeNearFromState (546195549508863 / 4000000000000) 1 (IntervalRat.scale (267 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-53345651113 / 1000000000000) (-53345571013 / 1000000000000), orderedInterval (42815122005 / 1000000000000) (42815202106 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 1) <| besselDerivativeNearFromState (463016016268743 / 4000000000000) 1 (IntervalRat.scale (267 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-21872871177 / 1000000000000) (-21872871176 / 1000000000000), orderedInterval (-70767249607 / 1000000000000) (-70767249606 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 1) <| besselDerivativeNearFromState (289733924458029 / 4000000000000) 1 (IntervalRat.scale (267 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-76826230037 / 1000000000000) (-76826230036 / 1000000000000), orderedInterval (-53197580644 / 1000000000000) (-53197580643 / 1000000000000)))) (orderedInterval (-4468847083 / 1000000000000) (-4468833951 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 1) <| besselDerivativeNearFromState (155819868185043 / 4000000000000) 1 (IntervalRat.scale (267 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (114130081469 / 1000000000000) (114130089025 / 1000000000000), orderedInterval (-59049197793 / 1000000000000) (-59049190236 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 1) <| besselDerivativeNearFromState (423081253404129 / 4000000000000) 1 (IntervalRat.scale (267 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-19916126276 / 1000000000000) (-19916125995 / 1000000000000), orderedInterval (75076112032 / 1000000000000) (75076112314 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 1) <| besselDerivativeNearFromState (577681281194433 / 4000000000000) 1 (IntervalRat.scale (267 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (42343247393 / 1000000000000) (42343247394 / 1000000000000), orderedInterval (50992021939 / 1000000000000) (50992021940 / 1000000000000)))) (orderedInterval (-5258938098 / 1000000000000) (-5258938037 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 1) <| besselDerivativeNearFromState (244266075541971 / 4000000000000) 1 (IntervalRat.scale (267 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-84907454679 / 1000000000000) (-84907427598 / 1000000000000), orderedInterval (57401527340 / 1000000000000) (57401554420 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 1) <| besselDerivativeNearFromState (992928035831091 / 4000000000000) 1 (IntervalRat.scale (267 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-37407333852 / 1000000000000) (-37407333851 / 1000000000000), orderedInterval (-34061244017 / 1000000000000) (-34061244016 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 1) <| besselDerivativeNearFromState (663229911615069 / 4000000000000) 1 (IntervalRat.scale (267 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-5427962310 / 1000000000000) (-5427962309 / 1000000000000), orderedInterval (-61709365902 / 1000000000000) (-61709365900 / 1000000000000)))) (orderedInterval (19694094697 / 1000000000000) (19694094825 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate258_chunkChecks1 :
    compactCertificate258.chunkChecks (1 : Fin 5) 0 9 = true :=
  compactCertificate258.chunkChecks_nine_of_three (1 : Fin 5) compactCertificate258_chunkChecks1_0
    compactCertificate258_chunkChecks1_1 compactCertificate258_chunkChecks1_2

theorem compactCertificate258_chunkChecks2_0 :
    compactCertificate258.chunkChecks (2 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 2) <| besselDerivativeNearFromState (267 / 2) 2 (IntervalRat.scale (267 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (49730416851 / 1000000000000) (49730491105 / 1000000000000), orderedInterval (-48098374840 / 1000000000000) (-48098300586 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 2) <| besselDerivativeNearFromState (393341983089567 / 4000000000000) 2 (IntervalRat.scale (267 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-79439670062 / 1000000000000) (-79439669758 / 1000000000000), orderedInterval (13179528503 / 1000000000000) (13179528807 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 2) <| besselDerivativeNearFromState (127198715610111 / 800000000000) 2 (IntervalRat.scale (267 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (26849953242 / 1000000000000) (26849955040 / 1000000000000), orderedInterval (-57382174591 / 1000000000000) (-57382172793 / 1000000000000)))) (orderedInterval (-21372568383 / 1000000000000) (-21372538566 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 2) <| besselDerivativeNearFromState (114776209656669 / 4000000000000) 2 (IntervalRat.scale (267 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-138859004326 / 1000000000000) (-138859004325 / 1000000000000), orderedInterval (-51452840641 / 1000000000000) (-51452840640 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 2) <| besselDerivativeNearFromState (308305043747193 / 4000000000000) 2 (IntervalRat.scale (267 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (57129967124 / 1000000000000) (57129998846 / 1000000000000), orderedInterval (-71051652277 / 1000000000000) (-71051620555 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 2) <| besselDerivativeNearFromState (837108167645781 / 4000000000000) 2 (IntervalRat.scale (267 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (22734441816 / 1000000000000) (22734442965 / 1000000000000), orderedInterval (-50305149029 / 1000000000000) (-50305147880 / 1000000000000)))) (orderedInterval (3175076771 / 1000000000000) (3175077389 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 2) <| besselDerivativeNearFromState (616610087494653 / 4000000000000) 2 (IntervalRat.scale (267 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-54043430132 / 1000000000000) (-54043430131 / 1000000000000), orderedInterval (-34596869854 / 1000000000000) (-34596869853 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 2) <| besselDerivativeNearFromState (1056571894704369 / 4000000000000) 2 (IntervalRat.scale (267 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (42191098342 / 1000000000000) (42191098343 / 1000000000000), orderedInterval (25020782429 / 1000000000000) (25020782430 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 2) <| besselDerivativeNearFromState (778266075541971 / 4000000000000) 2 (IntervalRat.scale (267 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (30989355564 / 1000000000000) (30989355565 / 1000000000000), orderedInterval (48000033472 / 1000000000000) (48000033473 / 1000000000000)))) (orderedInterval (3502495344 / 1000000000000) (3502495368 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate258_chunkChecks2_1 :
    compactCertificate258.chunkChecks (2 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 2) <| besselDerivativeNearFromState (1194060299984733 / 4000000000000) 2 (IntervalRat.scale (267 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-34656290662 / 1000000000000) (-34656290661 / 1000000000000), orderedInterval (-30463469235 / 1000000000000) (-30463469234 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 2) <| besselDerivativeNearFromState (689391035624757 / 4000000000000) 2 (IntervalRat.scale (267 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-20545052212 / 1000000000000) (-20545052211 / 1000000000000), orderedInterval (-57139367498 / 1000000000000) (-57139367497 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 2) <| besselDerivativeNearFromState (1223336490373113 / 4000000000000) 2 (IntervalRat.scale (267 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-43396013051 / 1000000000000) (-43396006952 / 1000000000000), orderedInterval (14155304466 / 1000000000000) (14155310565 / 1000000000000)))) (orderedInterval (4038812801 / 1000000000000) (4038817603 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 2) <| besselDerivativeNearFromState (1142999636342397 / 4000000000000) 2 (IntervalRat.scale (267 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-28562788817 / 1000000000000) (-28562788816 / 1000000000000), orderedInterval (-37527400784 / 1000000000000) (-37527400783 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 2) <| besselDerivativeNearFromState (815698473701901 / 4000000000000) 2 (IntervalRat.scale (267 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-27075010629 / 1000000000000) (-27075010628 / 1000000000000), orderedInterval (-48808839425 / 1000000000000) (-48808839424 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 2) <| besselDerivativeNearFromState (924915131241579 / 4000000000000) 2 (IntervalRat.scale (267 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-23492376191 / 1000000000000) (-23492374595 / 1000000000000), orderedInterval (46968972723 / 1000000000000) (46968974320 / 1000000000000)))) (orderedInterval (3299944099 / 1000000000000) (3299944167 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 2) <| besselDerivativeNearFromState (771097809179451 / 4000000000000) 2 (IntervalRat.scale (267 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-53957695501 / 1000000000000) (-53957690535 / 1000000000000), orderedInterval (19912813247 / 1000000000000) (19912818213 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 2) <| besselDerivativeNearFromState (681288299460471 / 4000000000000) 2 (IntervalRat.scale (267 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (60767022475 / 1000000000000) (60767022486 / 1000000000000), orderedInterval (6536826010 / 1000000000000) (6536826020 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 2) <| besselDerivativeNearFromState (197463903670629 / 800000000000) 2 (IntervalRat.scale (267 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (27450351662 / 1000000000000) (27450356406 / 1000000000000), orderedInterval (-42783405021 / 1000000000000) (-42783400277 / 1000000000000)))) (orderedInterval (4573230867 / 1000000000000) (4573231434 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate258_chunkChecks2_2 :
    compactCertificate258.chunkChecks (2 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 2) <| besselDerivativeNearFromState (546195549508863 / 4000000000000) 2 (IntervalRat.scale (267 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-53345651113 / 1000000000000) (-53345571013 / 1000000000000), orderedInterval (42815122005 / 1000000000000) (42815202106 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 2) <| besselDerivativeNearFromState (463016016268743 / 4000000000000) 2 (IntervalRat.scale (267 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-21872871177 / 1000000000000) (-21872871176 / 1000000000000), orderedInterval (-70767249607 / 1000000000000) (-70767249606 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 2) <| besselDerivativeNearFromState (289733924458029 / 4000000000000) 2 (IntervalRat.scale (267 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-76826230037 / 1000000000000) (-76826230036 / 1000000000000), orderedInterval (-53197580644 / 1000000000000) (-53197580643 / 1000000000000)))) (orderedInterval (-9084598857 / 1000000000000) (-9084585329 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 2) <| besselDerivativeNearFromState (155819868185043 / 4000000000000) 2 (IntervalRat.scale (267 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (114130081469 / 1000000000000) (114130089025 / 1000000000000), orderedInterval (-59049197793 / 1000000000000) (-59049190236 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 2) <| besselDerivativeNearFromState (423081253404129 / 4000000000000) 2 (IntervalRat.scale (267 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-19916126276 / 1000000000000) (-19916125995 / 1000000000000), orderedInterval (75076112032 / 1000000000000) (75076112314 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 2) <| besselDerivativeNearFromState (577681281194433 / 4000000000000) 2 (IntervalRat.scale (267 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (42343247393 / 1000000000000) (42343247394 / 1000000000000), orderedInterval (50992021939 / 1000000000000) (50992021940 / 1000000000000)))) (orderedInterval (3732964652 / 1000000000000) (3732964684 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 2) <| besselDerivativeNearFromState (244266075541971 / 4000000000000) 2 (IntervalRat.scale (267 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-84907454679 / 1000000000000) (-84907427598 / 1000000000000), orderedInterval (57401527340 / 1000000000000) (57401554420 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 2) <| besselDerivativeNearFromState (992928035831091 / 4000000000000) 2 (IntervalRat.scale (267 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-37407333852 / 1000000000000) (-37407333851 / 1000000000000), orderedInterval (-34061244017 / 1000000000000) (-34061244016 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 2) <| besselDerivativeNearFromState (663229911615069 / 4000000000000) 2 (IntervalRat.scale (267 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-5427962310 / 1000000000000) (-5427962309 / 1000000000000), orderedInterval (-61709365902 / 1000000000000) (-61709365900 / 1000000000000)))) (orderedInterval (-12139370805 / 1000000000000) (-12139370692 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate258_chunkChecks2 :
    compactCertificate258.chunkChecks (2 : Fin 5) 0 9 = true :=
  compactCertificate258.chunkChecks_nine_of_three (2 : Fin 5) compactCertificate258_chunkChecks2_0
    compactCertificate258_chunkChecks2_1 compactCertificate258_chunkChecks2_2

theorem compactCertificate258_chunkChecks3_0 :
    compactCertificate258.chunkChecks (3 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 3) <| besselDerivativeNearFromState (267 / 2) 3 (IntervalRat.scale (267 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (49730416851 / 1000000000000) (49730491105 / 1000000000000), orderedInterval (-48098374840 / 1000000000000) (-48098300586 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 3) <| besselDerivativeNearFromState (393341983089567 / 4000000000000) 3 (IntervalRat.scale (267 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-79439670062 / 1000000000000) (-79439669758 / 1000000000000), orderedInterval (13179528503 / 1000000000000) (13179528807 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 3) <| besselDerivativeNearFromState (127198715610111 / 800000000000) 3 (IntervalRat.scale (267 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (26849953242 / 1000000000000) (26849955040 / 1000000000000), orderedInterval (-57382174591 / 1000000000000) (-57382172793 / 1000000000000)))) (orderedInterval (24862865598 / 1000000000000) (24862895442 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 3) <| besselDerivativeNearFromState (114776209656669 / 4000000000000) 3 (IntervalRat.scale (267 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-138859004326 / 1000000000000) (-138859004325 / 1000000000000), orderedInterval (-51452840641 / 1000000000000) (-51452840640 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 3) <| besselDerivativeNearFromState (308305043747193 / 4000000000000) 3 (IntervalRat.scale (267 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (57129967124 / 1000000000000) (57129998846 / 1000000000000), orderedInterval (-71051652277 / 1000000000000) (-71051620555 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 3) <| besselDerivativeNearFromState (837108167645781 / 4000000000000) 3 (IntervalRat.scale (267 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (22734441816 / 1000000000000) (22734442965 / 1000000000000), orderedInterval (-50305149029 / 1000000000000) (-50305147880 / 1000000000000)))) (orderedInterval (-13306357841 / 1000000000000) (-13306357261 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 3) <| besselDerivativeNearFromState (616610087494653 / 4000000000000) 3 (IntervalRat.scale (267 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-54043430132 / 1000000000000) (-54043430131 / 1000000000000), orderedInterval (-34596869854 / 1000000000000) (-34596869853 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 3) <| besselDerivativeNearFromState (1056571894704369 / 4000000000000) 3 (IntervalRat.scale (267 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (42191098342 / 1000000000000) (42191098343 / 1000000000000), orderedInterval (25020782429 / 1000000000000) (25020782430 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 3) <| besselDerivativeNearFromState (778266075541971 / 4000000000000) 3 (IntervalRat.scale (267 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (30989355564 / 1000000000000) (30989355565 / 1000000000000), orderedInterval (48000033472 / 1000000000000) (48000033473 / 1000000000000)))) (orderedInterval (2360392489 / 1000000000000) (2360392532 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate258_chunkChecks3_1 :
    compactCertificate258.chunkChecks (3 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 3) <| besselDerivativeNearFromState (1194060299984733 / 4000000000000) 3 (IntervalRat.scale (267 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-34656290662 / 1000000000000) (-34656290661 / 1000000000000), orderedInterval (-30463469235 / 1000000000000) (-30463469234 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 3) <| besselDerivativeNearFromState (689391035624757 / 4000000000000) 3 (IntervalRat.scale (267 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-20545052212 / 1000000000000) (-20545052211 / 1000000000000), orderedInterval (-57139367498 / 1000000000000) (-57139367497 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 3) <| besselDerivativeNearFromState (1223336490373113 / 4000000000000) 3 (IntervalRat.scale (267 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-43396013051 / 1000000000000) (-43396006952 / 1000000000000), orderedInterval (14155304466 / 1000000000000) (14155310565 / 1000000000000)))) (orderedInterval (-75633010672 / 1000000000000) (-75632999696 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 3) <| besselDerivativeNearFromState (1142999636342397 / 4000000000000) 3 (IntervalRat.scale (267 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-28562788817 / 1000000000000) (-28562788816 / 1000000000000), orderedInterval (-37527400784 / 1000000000000) (-37527400783 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 3) <| besselDerivativeNearFromState (815698473701901 / 4000000000000) 3 (IntervalRat.scale (267 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-27075010629 / 1000000000000) (-27075010628 / 1000000000000), orderedInterval (-48808839425 / 1000000000000) (-48808839424 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 3) <| besselDerivativeNearFromState (924915131241579 / 4000000000000) 3 (IntervalRat.scale (267 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-23492376191 / 1000000000000) (-23492374595 / 1000000000000), orderedInterval (46968972723 / 1000000000000) (46968974320 / 1000000000000)))) (orderedInterval (11016946290 / 1000000000000) (11016946406 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 3) <| besselDerivativeNearFromState (771097809179451 / 4000000000000) 3 (IntervalRat.scale (267 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-53957695501 / 1000000000000) (-53957690535 / 1000000000000), orderedInterval (19912813247 / 1000000000000) (19912818213 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 3) <| besselDerivativeNearFromState (681288299460471 / 4000000000000) 3 (IntervalRat.scale (267 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (60767022475 / 1000000000000) (60767022486 / 1000000000000), orderedInterval (6536826010 / 1000000000000) (6536826020 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 3) <| besselDerivativeNearFromState (197463903670629 / 800000000000) 3 (IntervalRat.scale (267 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (27450351662 / 1000000000000) (27450356406 / 1000000000000), orderedInterval (-42783405021 / 1000000000000) (-42783400277 / 1000000000000)))) (orderedInterval (6973702485 / 1000000000000) (6973703474 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate258_chunkChecks3_2 :
    compactCertificate258.chunkChecks (3 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 3) <| besselDerivativeNearFromState (546195549508863 / 4000000000000) 3 (IntervalRat.scale (267 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-53345651113 / 1000000000000) (-53345571013 / 1000000000000), orderedInterval (42815122005 / 1000000000000) (42815202106 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 3) <| besselDerivativeNearFromState (463016016268743 / 4000000000000) 3 (IntervalRat.scale (267 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-21872871177 / 1000000000000) (-21872871176 / 1000000000000), orderedInterval (-70767249607 / 1000000000000) (-70767249606 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 3) <| besselDerivativeNearFromState (289733924458029 / 4000000000000) 3 (IntervalRat.scale (267 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-76826230037 / 1000000000000) (-76826230036 / 1000000000000), orderedInterval (-53197580644 / 1000000000000) (-53197580643 / 1000000000000)))) (orderedInterval (5059030324 / 1000000000000) (5059044157 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 3) <| besselDerivativeNearFromState (155819868185043 / 4000000000000) 3 (IntervalRat.scale (267 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (114130081469 / 1000000000000) (114130089025 / 1000000000000), orderedInterval (-59049197793 / 1000000000000) (-59049190236 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 3) <| besselDerivativeNearFromState (423081253404129 / 4000000000000) 3 (IntervalRat.scale (267 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-19916126276 / 1000000000000) (-19916125995 / 1000000000000), orderedInterval (75076112032 / 1000000000000) (75076112314 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 3) <| besselDerivativeNearFromState (577681281194433 / 4000000000000) 3 (IntervalRat.scale (267 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (42343247393 / 1000000000000) (42343247394 / 1000000000000), orderedInterval (50992021939 / 1000000000000) (50992021940 / 1000000000000)))) (orderedInterval (5739306867 / 1000000000000) (5739306890 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 3) <| besselDerivativeNearFromState (244266075541971 / 4000000000000) 3 (IntervalRat.scale (267 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-84907454679 / 1000000000000) (-84907427598 / 1000000000000), orderedInterval (57401527340 / 1000000000000) (57401554420 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 3) <| besselDerivativeNearFromState (992928035831091 / 4000000000000) 3 (IntervalRat.scale (267 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-37407333852 / 1000000000000) (-37407333851 / 1000000000000), orderedInterval (-34061244017 / 1000000000000) (-34061244016 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 3) <| besselDerivativeNearFromState (663229911615069 / 4000000000000) 3 (IntervalRat.scale (267 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-5427962310 / 1000000000000) (-5427962309 / 1000000000000), orderedInterval (-61709365902 / 1000000000000) (-61709365900 / 1000000000000)))) (orderedInterval (-39948525783 / 1000000000000) (-39948525646 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate258_chunkChecks3 :
    compactCertificate258.chunkChecks (3 : Fin 5) 0 9 = true :=
  compactCertificate258.chunkChecks_nine_of_three (3 : Fin 5) compactCertificate258_chunkChecks3_0
    compactCertificate258_chunkChecks3_1 compactCertificate258_chunkChecks3_2

theorem compactCertificate258_chunkChecks4_0 :
    compactCertificate258.chunkChecks (4 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 4) <| besselDerivativeNearFromState (267 / 2) 4 (IntervalRat.scale (267 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (49730416851 / 1000000000000) (49730491105 / 1000000000000), orderedInterval (-48098374840 / 1000000000000) (-48098300586 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 4) <| besselDerivativeNearFromState (393341983089567 / 4000000000000) 4 (IntervalRat.scale (267 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-79439670062 / 1000000000000) (-79439669758 / 1000000000000), orderedInterval (13179528503 / 1000000000000) (13179528807 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 4) <| besselDerivativeNearFromState (127198715610111 / 800000000000) 4 (IntervalRat.scale (267 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (26849953242 / 1000000000000) (26849955040 / 1000000000000), orderedInterval (-57382174591 / 1000000000000) (-57382172793 / 1000000000000)))) (orderedInterval (22290027507 / 1000000000000) (22290057607 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 4) <| besselDerivativeNearFromState (114776209656669 / 4000000000000) 4 (IntervalRat.scale (267 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-138859004326 / 1000000000000) (-138859004325 / 1000000000000), orderedInterval (-51452840641 / 1000000000000) (-51452840640 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 4) <| besselDerivativeNearFromState (308305043747193 / 4000000000000) 4 (IntervalRat.scale (267 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (57129967124 / 1000000000000) (57129998846 / 1000000000000), orderedInterval (-71051652277 / 1000000000000) (-71051620555 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 4) <| besselDerivativeNearFromState (837108167645781 / 4000000000000) 4 (IntervalRat.scale (267 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (22734441816 / 1000000000000) (22734442965 / 1000000000000), orderedInterval (-50305149029 / 1000000000000) (-50305147880 / 1000000000000)))) (orderedInterval (-9325541314 / 1000000000000) (-9325540626 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 4) <| besselDerivativeNearFromState (616610087494653 / 4000000000000) 4 (IntervalRat.scale (267 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-54043430132 / 1000000000000) (-54043430131 / 1000000000000), orderedInterval (-34596869854 / 1000000000000) (-34596869853 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 4) <| besselDerivativeNearFromState (1056571894704369 / 4000000000000) 4 (IntervalRat.scale (267 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (42191098342 / 1000000000000) (42191098343 / 1000000000000), orderedInterval (25020782429 / 1000000000000) (25020782430 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 4) <| besselDerivativeNearFromState (778266075541971 / 4000000000000) 4 (IntervalRat.scale (267 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (30989355564 / 1000000000000) (30989355565 / 1000000000000), orderedInterval (48000033472 / 1000000000000) (48000033473 / 1000000000000)))) (orderedInterval (-16600545198 / 1000000000000) (-16600545119 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate258_chunkChecks4_1 :
    compactCertificate258.chunkChecks (4 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 4) <| besselDerivativeNearFromState (1194060299984733 / 4000000000000) 4 (IntervalRat.scale (267 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-34656290662 / 1000000000000) (-34656290661 / 1000000000000), orderedInterval (-30463469235 / 1000000000000) (-30463469234 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 4) <| besselDerivativeNearFromState (689391035624757 / 4000000000000) 4 (IntervalRat.scale (267 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-20545052212 / 1000000000000) (-20545052211 / 1000000000000), orderedInterval (-57139367498 / 1000000000000) (-57139367497 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 4) <| besselDerivativeNearFromState (1223336490373113 / 4000000000000) 4 (IntervalRat.scale (267 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-43396013051 / 1000000000000) (-43396006952 / 1000000000000), orderedInterval (14155304466 / 1000000000000) (14155310565 / 1000000000000)))) (orderedInterval (-19060629802 / 1000000000000) (-19060604617 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 4) <| besselDerivativeNearFromState (1142999636342397 / 4000000000000) 4 (IntervalRat.scale (267 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-28562788817 / 1000000000000) (-28562788816 / 1000000000000), orderedInterval (-37527400784 / 1000000000000) (-37527400783 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 4) <| besselDerivativeNearFromState (815698473701901 / 4000000000000) 4 (IntervalRat.scale (267 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-27075010629 / 1000000000000) (-27075010628 / 1000000000000), orderedInterval (-48808839425 / 1000000000000) (-48808839424 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 4) <| besselDerivativeNearFromState (924915131241579 / 4000000000000) 4 (IntervalRat.scale (267 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-23492376191 / 1000000000000) (-23492374595 / 1000000000000), orderedInterval (46968972723 / 1000000000000) (46968974320 / 1000000000000)))) (orderedInterval (-2210663992 / 1000000000000) (-2210663791 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 4) <| besselDerivativeNearFromState (771097809179451 / 4000000000000) 4 (IntervalRat.scale (267 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-53957695501 / 1000000000000) (-53957690535 / 1000000000000), orderedInterval (19912813247 / 1000000000000) (19912818213 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 4) <| besselDerivativeNearFromState (681288299460471 / 4000000000000) 4 (IntervalRat.scale (267 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (60767022475 / 1000000000000) (60767022486 / 1000000000000), orderedInterval (6536826010 / 1000000000000) (6536826020 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 4) <| besselDerivativeNearFromState (197463903670629 / 800000000000) 4 (IntervalRat.scale (267 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (27450351662 / 1000000000000) (27450356406 / 1000000000000), orderedInterval (-42783405021 / 1000000000000) (-42783400277 / 1000000000000)))) (orderedInterval (-3813443408 / 1000000000000) (-3813441656 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate258_chunkChecks4_2 :
    compactCertificate258.chunkChecks (4 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 4) <| besselDerivativeNearFromState (546195549508863 / 4000000000000) 4 (IntervalRat.scale (267 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-53345651113 / 1000000000000) (-53345571013 / 1000000000000), orderedInterval (42815122005 / 1000000000000) (42815202106 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 4) <| besselDerivativeNearFromState (463016016268743 / 4000000000000) 4 (IntervalRat.scale (267 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-21872871177 / 1000000000000) (-21872871176 / 1000000000000), orderedInterval (-70767249607 / 1000000000000) (-70767249606 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 4) <| besselDerivativeNearFromState (289733924458029 / 4000000000000) 4 (IntervalRat.scale (267 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-76826230037 / 1000000000000) (-76826230036 / 1000000000000), orderedInterval (-53197580644 / 1000000000000) (-53197580643 / 1000000000000)))) (orderedInterval (9742546789 / 1000000000000) (9742561039 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 4) <| besselDerivativeNearFromState (155819868185043 / 4000000000000) 4 (IntervalRat.scale (267 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (114130081469 / 1000000000000) (114130089025 / 1000000000000), orderedInterval (-59049197793 / 1000000000000) (-59049190236 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 4) <| besselDerivativeNearFromState (423081253404129 / 4000000000000) 4 (IntervalRat.scale (267 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-19916126276 / 1000000000000) (-19916125995 / 1000000000000), orderedInterval (75076112032 / 1000000000000) (75076112314 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 4) <| besselDerivativeNearFromState (577681281194433 / 4000000000000) 4 (IntervalRat.scale (267 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (42343247393 / 1000000000000) (42343247394 / 1000000000000), orderedInterval (50992021939 / 1000000000000) (50992021940 / 1000000000000)))) (orderedInterval (-4367496863 / 1000000000000) (-4367496843 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 4) <| besselDerivativeNearFromState (244266075541971 / 4000000000000) 4 (IntervalRat.scale (267 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-84907454679 / 1000000000000) (-84907427598 / 1000000000000), orderedInterval (57401527340 / 1000000000000) (57401554420 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 4) <| besselDerivativeNearFromState (992928035831091 / 4000000000000) 4 (IntervalRat.scale (267 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-37407333852 / 1000000000000) (-37407333851 / 1000000000000), orderedInterval (-34061244017 / 1000000000000) (-34061244016 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 4) <| besselDerivativeNearFromState (663229911615069 / 4000000000000) 4 (IntervalRat.scale (267 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-5427962310 / 1000000000000) (-5427962309 / 1000000000000), orderedInterval (-61709365902 / 1000000000000) (-61709365900 / 1000000000000)))) (orderedInterval (39398374099 / 1000000000000) (39398374298 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate258_chunkChecks4 :
    compactCertificate258.chunkChecks (4 : Fin 5) 0 9 = true :=
  compactCertificate258.chunkChecks_nine_of_three (4 : Fin 5) compactCertificate258_chunkChecks4_0
    compactCertificate258_chunkChecks4_1 compactCertificate258_chunkChecks4_2

theorem compactCertificate258_chunks :
    ∀ r : Fin 5, ∀ b, compactCertificate258.chunkCheck r b = true :=
  compactCertificate258.chunkChecks_all (by
    intro r
    fin_cases r
    · exact compactCertificate258_chunkChecks0
    · exact compactCertificate258_chunkChecks1
    · exact compactCertificate258_chunkChecks2
    · exact compactCertificate258_chunkChecks3
    · exact compactCertificate258_chunkChecks4)

theorem compactCertificate258_coefficient0 :
    compactCertificate258.coefficientCheck (0 : Fin 5) = true := by
  norm_num [CompactCertificate.coefficientCheck, intervalFinSumHull,
    compactCertificate258, rationalIntervalSubset, orderedInterval, Fin.sum_univ_succ]

theorem compactCertificate258_coefficient1 :
    compactCertificate258.coefficientCheck (1 : Fin 5) = true := by
  norm_num [CompactCertificate.coefficientCheck, intervalFinSumHull,
    compactCertificate258, rationalIntervalSubset, orderedInterval, Fin.sum_univ_succ]

theorem compactCertificate258_coefficient2 :
    compactCertificate258.coefficientCheck (2 : Fin 5) = true := by
  norm_num [CompactCertificate.coefficientCheck, intervalFinSumHull,
    compactCertificate258, rationalIntervalSubset, orderedInterval, Fin.sum_univ_succ]

theorem compactCertificate258_coefficient3 :
    compactCertificate258.coefficientCheck (3 : Fin 5) = true := by
  norm_num [CompactCertificate.coefficientCheck, intervalFinSumHull,
    compactCertificate258, rationalIntervalSubset, orderedInterval, Fin.sum_univ_succ]

theorem compactCertificate258_coefficient4 :
    compactCertificate258.coefficientCheck (4 : Fin 5) = true := by
  norm_num [CompactCertificate.coefficientCheck, intervalFinSumHull,
    compactCertificate258, rationalIntervalSubset, orderedInterval, Fin.sum_univ_succ]

theorem compactCertificate258_coefficients : ∀ r : Fin 5,
    compactCertificate258.coefficientCheck r = true := by
  intro r
  fin_cases r
  · exact compactCertificate258_coefficient0
  · exact compactCertificate258_coefficient1
  · exact compactCertificate258_coefficient2
  · exact compactCertificate258_coefficient3
  · exact compactCertificate258_coefficient4

theorem compactCertificate258_lower : (1 : ℚ) ≤ compactCertificate258.output.lo := by
  norm_num [CompactCertificate.output, CompactCertificate.interval,
    CompactCertificate.coefficientTargetNat, compactCertificate258, dualConstant,
    intervalTaylorSum, intervalPow, intervalSub, intervalMaxAbs, widenInterval,
    rationalErrorInterval, orderedInterval, IntervalRat.add, IntervalRat.mul, IntervalRat.scale,
    IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4]

theorem compactCertificate258_proves {t : ℝ} (ht : t ∈ compactCertificate258.interval) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t :=
  compactCertificate258.proves compactCertificate258_states compactCertificate258_chunks
    compactCertificate258_coefficients compactCertificate258_lower ht

end Erdos232
