/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, OpenAI Codex
-/
import ErdosProblems.Erdos232.CompactBase

open LeanCert.Core
namespace Erdos232

def compactCertificate249 : CompactCertificate where
  left := 124
  right := 125
  center := 249 / 2
  grid := fun i =>
    match i.val with
    | 0 => 40
    | 1 => 29
    | 2 => 47
    | 3 => 9
    | 4 => 23
    | 5 => 62
    | 6 => 46
    | 7 => 78
    | 8 => 58
    | 9 => 89
    | 10 => 51
    | 11 => 91
    | 12 => 85
    | 13 => 61
    | 14 => 69
    | 15 => 57
    | 16 => 51
    | 17 => 73
    | 18 => 41
    | 19 => 34
    | 20 => 22
    | 21 => 12
    | 22 => 31
    | 23 => 43
    | 24 => 18
    | 25 => 74
    | _ => 49
  point := fun i =>
    match i.val with
    | 0 => 249 / 2
    | 1 => 366824546027349 / 4000000000000
    | 2 => 118623521299317 / 800000000000
    | 3 => 107038487657343 / 4000000000000
    | 4 => 287520434056371 / 4000000000000
    | 5 => 780673909152807 / 4000000000000
    | 6 => 575040868112991 / 4000000000000
    | 7 => 985342328769243 / 4000000000000
    | 8 => 725798699662737 / 4000000000000
    | 9 => 1113561852794751 / 4000000000000
    | 10 => 642915235470279 / 4000000000000
    | 11 => 1140864367426611 / 4000000000000
    | 12 => 1065943481083359 / 4000000000000
    | 13 => 760707565362447 / 4000000000000
    | 14 => 862561302169113 / 4000000000000
    | 15 => 719113687212297 / 4000000000000
    | 16 => 635358751182237 / 4000000000000
    | 17 => 184151730389463 / 800000000000
    | 18 => 509373377631861 / 4000000000000
    | 19 => 431801453374221 / 4000000000000
    | 20 => 270201300337263 / 4000000000000
    | 21 => 145315157970321 / 4000000000000
    | 22 => 394558921713963 / 4000000000000
    | 23 => 538736475720651 / 4000000000000
    | 24 => 227798699662737 / 4000000000000
    | 25 => 925989067123377 / 4000000000000
    | _ => 618517782742143 / 4000000000000
  state := fun i =>
    match i.val with
    | 0 => (orderedInterval (-26478023941 / 1000000000000) (-26478022831 / 1000000000000), orderedInterval (66531902726 / 1000000000000) (66531903836 / 1000000000000))
    | 1 => (orderedInterval (-81868157540 / 1000000000000) (-81868157538 / 1000000000000), orderedInterval (-15028232422 / 1000000000000) (-15028232420 / 1000000000000))
    | 2 => (orderedInterval (-64669005345 / 1000000000000) (-64669005341 / 1000000000000), orderedInterval (-10330696138 / 1000000000000) (-10330696134 / 1000000000000))
    | 3 => (orderedInterval (103306485014 / 1000000000000) (103306547729 / 1000000000000), orderedInterval (-116465652565 / 1000000000000) (-116465589851 / 1000000000000))
    | 4 => (orderedInterval (-37265391105 / 1000000000000) (-37265391104 / 1000000000000), orderedInterval (-86159117557 / 1000000000000) (-86159117556 / 1000000000000))
    | 5 => (orderedInterval (52686302271 / 1000000000000) (52686302272 / 1000000000000), orderedInterval (21911443299 / 1000000000000) (21911443300 / 1000000000000))
    | 6 => (orderedInterval (2094752154 / 1000000000000) (2094752157 / 1000000000000), orderedInterval (66505745442 / 1000000000000) (66505745445 / 1000000000000))
    | 7 => (orderedInterval (44479769804 / 1000000000000) (44479799243 / 1000000000000), orderedInterval (-24705448160 / 1000000000000) (-24705418721 / 1000000000000))
    | 8 => (orderedInterval (1303622205 / 1000000000000) (1303622208 / 1000000000000), orderedInterval (59214932333 / 1000000000000) (59214932336 / 1000000000000))
    | 9 => (orderedInterval (19775405501 / 1000000000000) (19775406272 / 1000000000000), orderedInterval (-43575419308 / 1000000000000) (-43575418538 / 1000000000000))
    | 10 => (orderedInterval (-60508434686 / 1000000000000) (-60508434684 / 1000000000000), orderedInterval (-17119134000 / 1000000000000) (-17119133998 / 1000000000000))
    | 11 => (orderedInterval (-5473742456 / 1000000000000) (-5473742455 / 1000000000000), orderedInterval (-46916971155 / 1000000000000) (-46916971154 / 1000000000000))
    | 12 => (orderedInterval (-11400759664 / 1000000000000) (-11400759663 / 1000000000000), orderedInterval (-47507234675 / 1000000000000) (-47507234674 / 1000000000000))
    | 13 => (orderedInterval (36178518684 / 1000000000000) (36178536700 / 1000000000000), orderedInterval (-45246321562 / 1000000000000) (-45246303546 / 1000000000000))
    | 14 => (orderedInterval (18362864832 / 1000000000000) (18362865247 / 1000000000000), orderedInterval (-51180049130 / 1000000000000) (-51180048715 / 1000000000000))
    | 15 => (orderedInterval (-59324290955 / 1000000000000) (-59324290937 / 1000000000000), orderedInterval (-4498761566 / 1000000000000) (-4498761548 / 1000000000000))
    | 16 => (orderedInterval (35585682939 / 1000000000000) (35585692698 / 1000000000000), orderedInterval (-52472359907 / 1000000000000) (-52472350148 / 1000000000000))
    | 17 => (orderedInterval (-52469598673 / 1000000000000) (-52469598457 / 1000000000000), orderedInterval (3658855511 / 1000000000000) (3658855727 / 1000000000000))
    | 18 => (orderedInterval (44323308996 / 1000000000000) (44323333709 / 1000000000000), orderedInterval (-55262060816 / 1000000000000) (-55262036103 / 1000000000000))
    | 19 => (orderedInterval (72146944795 / 1000000000000) (72146947891 / 1000000000000), orderedInterval (-26642100420 / 1000000000000) (-26642097324 / 1000000000000))
    | 20 => (orderedInterval (-68353311809 / 1000000000000) (-68353231170 / 1000000000000), orderedInterval (69442145510 / 1000000000000) (69442226149 / 1000000000000))
    | 21 => (orderedInterval (-73466189585 / 1000000000000) (-73466173509 / 1000000000000), orderedInterval (111134465438 / 1000000000000) (111134481514 / 1000000000000))
    | 22 => (orderedInterval (-71853269475 / 1000000000000) (-71853259772 / 1000000000000), orderedInterval (36295362189 / 1000000000000) (36295371892 / 1000000000000))
    | 23 => (orderedInterval (-25507931083 / 1000000000000) (-25507931082 / 1000000000000), orderedInterval (-63749890899 / 1000000000000) (-63749890898 / 1000000000000))
    | 24 => (orderedInterval (97924573159 / 1000000000000) (97924573160 / 1000000000000), orderedInterval (39003928308 / 1000000000000) (39003928309 / 1000000000000))
    | 25 => (orderedInterval (-10198833519 / 1000000000000) (-10198833471 / 1000000000000), orderedInterval (51461308667 / 1000000000000) (51461308715 / 1000000000000))
    | _ => (orderedInterval (-63876093791 / 1000000000000) (-63876093779 / 1000000000000), orderedInterval (-5867203656 / 1000000000000) (-5867203644 / 1000000000000))
  chunkTarget := fun r b =>
    match r.val with
    | 0 =>
      match b.val with
      | 0 => orderedInterval (-15052665139 / 1000000000000) (-15052664689 / 1000000000000)
      | 1 => orderedInterval (-6226877615 / 1000000000000) (-6226876919 / 1000000000000)
      | 2 => orderedInterval (-1340429000 / 1000000000000) (-1340428084 / 1000000000000)
      | 3 => orderedInterval (-8775152779 / 1000000000000) (-8775152592 / 1000000000000)
      | 4 => orderedInterval (3534036626 / 1000000000000) (3534038347 / 1000000000000)
      | 5 => orderedInterval (-4064937264 / 1000000000000) (-4064936687 / 1000000000000)
      | 6 => orderedInterval (-13395740746 / 1000000000000) (-13395733962 / 1000000000000)
      | 7 => orderedInterval (4941585484 / 1000000000000) (4941586017 / 1000000000000)
      | _ => orderedInterval (13405374231 / 1000000000000) (13405374272 / 1000000000000)
    | 1 =>
      match b.val with
      | 0 => orderedInterval (25545764764 / 1000000000000) (25545765215 / 1000000000000)
      | 1 => orderedInterval (-3986494921 / 1000000000000) (-3986494757 / 1000000000000)
      | 2 => orderedInterval (3593455808 / 1000000000000) (3593457618 / 1000000000000)
      | 3 => orderedInterval (396843194 / 1000000000000) (396843603 / 1000000000000)
      | 4 => orderedInterval (-4251340193 / 1000000000000) (-4251337562 / 1000000000000)
      | 5 => orderedInterval (3929249922 / 1000000000000) (3929250663 / 1000000000000)
      | 6 => orderedInterval (11571870464 / 1000000000000) (11571876111 / 1000000000000)
      | 7 => orderedInterval (4034179902 / 1000000000000) (4034180178 / 1000000000000)
      | _ => orderedInterval (-6314365714 / 1000000000000) (-6314365654 / 1000000000000)
    | 2 =>
      match b.val with
      | 0 => orderedInterval (16086594331 / 1000000000000) (16086594786 / 1000000000000)
      | 1 => orderedInterval (9741511243 / 1000000000000) (9741511300 / 1000000000000)
      | 2 => orderedInterval (5275137082 / 1000000000000) (5275140673 / 1000000000000)
      | 3 => orderedInterval (29121772727 / 1000000000000) (29121773635 / 1000000000000)
      | 4 => orderedInterval (-8612710551 / 1000000000000) (-8612706508 / 1000000000000)
      | 5 => orderedInterval (9304136376 / 1000000000000) (9304137337 / 1000000000000)
      | 6 => orderedInterval (11046537248 / 1000000000000) (11046542360 / 1000000000000)
      | 7 => orderedInterval (-3458970452 / 1000000000000) (-3458970272 / 1000000000000)
      | _ => orderedInterval (-21430671956 / 1000000000000) (-21430671867 / 1000000000000)
    | 3 =>
      match b.val with
      | 0 => orderedInterval (-25418365999 / 1000000000000) (-25418365541 / 1000000000000)
      | 1 => orderedInterval (6515013964 / 1000000000000) (6515014008 / 1000000000000)
      | 2 => orderedInterval (-10374948464 / 1000000000000) (-10374941362 / 1000000000000)
      | 3 => orderedInterval (-3884273118 / 1000000000000) (-3884271099 / 1000000000000)
      | 4 => orderedInterval (5562489621 / 1000000000000) (5562495804 / 1000000000000)
      | 5 => orderedInterval (-6746053331 / 1000000000000) (-6746052088 / 1000000000000)
      | 6 => orderedInterval (-10887371905 / 1000000000000) (-10887367075 / 1000000000000)
      | 7 => orderedInterval (-5696879878 / 1000000000000) (-5696879745 / 1000000000000)
      | _ => orderedInterval (24970627907 / 1000000000000) (24970628047 / 1000000000000)
    | _ =>
      match b.val with
      | 0 => orderedInterval (-17945737727 / 1000000000000) (-17945737264 / 1000000000000)
      | 1 => orderedInterval (-22876180550 / 1000000000000) (-22876180493 / 1000000000000)
      | 2 => orderedInterval (-20717237971 / 1000000000000) (-20717223869 / 1000000000000)
      | 3 => orderedInterval (-121667524307 / 1000000000000) (-121667519786 / 1000000000000)
      | 4 => orderedInterval (22020187016 / 1000000000000) (22020196526 / 1000000000000)
      | 5 => orderedInterval (-23964368504 / 1000000000000) (-23964366876 / 1000000000000)
      | 6 => orderedInterval (-10082230601 / 1000000000000) (-10082225847 / 1000000000000)
      | 7 => orderedInterval (3420840242 / 1000000000000) (3420840348 / 1000000000000)
      | _ => orderedInterval (38065738199 / 1000000000000) (38065738429 / 1000000000000)
  coefficientTarget := fun i =>
    match i.val with
    | 0 => orderedInterval (-26974806202 / 1000000000000) (-26974794297 / 1000000000000)
    | 1 => orderedInterval (34519163226 / 1000000000000) (34519175415 / 1000000000000)
    | 2 => orderedInterval (47073336048 / 1000000000000) (47073351444 / 1000000000000)
    | 3 => orderedInterval (-25959761203 / 1000000000000) (-25959739051 / 1000000000000)
    | _ => orderedInterval (-153746514203 / 1000000000000) (-153746478832 / 1000000000000)

theorem compactCertificate249_stateChecks0 :
    compactCertificate249.stateChecks 0 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 40 12 (249 / 2)) (orderedInterval (-26478023941 / 1000000000000) (-26478022831 / 1000000000000), orderedInterval (66531902726 / 1000000000000) (66531903836 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 29 12 (366824546027349 / 4000000000000)) (orderedInterval (-81868157540 / 1000000000000) (-81868157538 / 1000000000000), orderedInterval (-15028232422 / 1000000000000) (-15028232420 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 47 12 (118623521299317 / 800000000000)) (orderedInterval (-64669005345 / 1000000000000) (-64669005341 / 1000000000000), orderedInterval (-10330696138 / 1000000000000) (-10330696134 / 1000000000000))) = true
  norm_num [besselStateAtRationalPoint, besselIntervalStepZero,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, besselZeroTransition,
    besselInitial, besselGridStateAt, besselGridStateBlock00, besselGridStateBlock01,
    besselGridStateBlock02, besselGridStateBlock03, besselGridStateBlock04,
    besselGridStateBlock05, besselGridStateBlock06, besselGridStateBlock07,
    besselGridStateBlock08, besselGridStateBlock09, besselGridStateBlock10,
    besselGridStateBlock11, besselGridStateBlock12, besselGridStateBlock13,
    besselGridStateBlock14, besselGridState009, besselGridState012, besselGridState018, besselGridState022, besselGridState023, besselGridState029, besselGridState031, besselGridState034, besselGridState040, besselGridState041, besselGridState043, besselGridState046, besselGridState047, besselGridState049, besselGridState051, besselGridState057, besselGridState058, besselGridState061, besselGridState062, besselGridState069, besselGridState073, besselGridState074, besselGridState078, besselGridState085, besselGridState089, besselGridState091, besselStateSubset, linearInterval, widenInterval,
    rationalErrorInterval, rationalIntervalSubset, orderedInterval, Finset.sum_range_succ,
    IntervalRat.add, IntervalRat.mul, IntervalRat.scale, IntervalRat.singleton]

theorem compactCertificate249_stateChecks1 :
    compactCertificate249.stateChecks 3 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 9 12 (107038487657343 / 4000000000000)) (orderedInterval (103306485014 / 1000000000000) (103306547729 / 1000000000000), orderedInterval (-116465652565 / 1000000000000) (-116465589851 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 23 12 (287520434056371 / 4000000000000)) (orderedInterval (-37265391105 / 1000000000000) (-37265391104 / 1000000000000), orderedInterval (-86159117557 / 1000000000000) (-86159117556 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 62 12 (780673909152807 / 4000000000000)) (orderedInterval (52686302271 / 1000000000000) (52686302272 / 1000000000000), orderedInterval (21911443299 / 1000000000000) (21911443300 / 1000000000000))) = true
  norm_num [besselStateAtRationalPoint, besselIntervalStepZero,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, besselZeroTransition,
    besselInitial, besselGridStateAt, besselGridStateBlock00, besselGridStateBlock01,
    besselGridStateBlock02, besselGridStateBlock03, besselGridStateBlock04,
    besselGridStateBlock05, besselGridStateBlock06, besselGridStateBlock07,
    besselGridStateBlock08, besselGridStateBlock09, besselGridStateBlock10,
    besselGridStateBlock11, besselGridStateBlock12, besselGridStateBlock13,
    besselGridStateBlock14, besselGridState009, besselGridState012, besselGridState018, besselGridState022, besselGridState023, besselGridState029, besselGridState031, besselGridState034, besselGridState040, besselGridState041, besselGridState043, besselGridState046, besselGridState047, besselGridState049, besselGridState051, besselGridState057, besselGridState058, besselGridState061, besselGridState062, besselGridState069, besselGridState073, besselGridState074, besselGridState078, besselGridState085, besselGridState089, besselGridState091, besselStateSubset, linearInterval, widenInterval,
    rationalErrorInterval, rationalIntervalSubset, orderedInterval, Finset.sum_range_succ,
    IntervalRat.add, IntervalRat.mul, IntervalRat.scale, IntervalRat.singleton]

theorem compactCertificate249_stateChecks2 :
    compactCertificate249.stateChecks 6 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 46 12 (575040868112991 / 4000000000000)) (orderedInterval (2094752154 / 1000000000000) (2094752157 / 1000000000000), orderedInterval (66505745442 / 1000000000000) (66505745445 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 78 12 (985342328769243 / 4000000000000)) (orderedInterval (44479769804 / 1000000000000) (44479799243 / 1000000000000), orderedInterval (-24705448160 / 1000000000000) (-24705418721 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 58 12 (725798699662737 / 4000000000000)) (orderedInterval (1303622205 / 1000000000000) (1303622208 / 1000000000000), orderedInterval (59214932333 / 1000000000000) (59214932336 / 1000000000000))) = true
  norm_num [besselStateAtRationalPoint, besselIntervalStepZero,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, besselZeroTransition,
    besselInitial, besselGridStateAt, besselGridStateBlock00, besselGridStateBlock01,
    besselGridStateBlock02, besselGridStateBlock03, besselGridStateBlock04,
    besselGridStateBlock05, besselGridStateBlock06, besselGridStateBlock07,
    besselGridStateBlock08, besselGridStateBlock09, besselGridStateBlock10,
    besselGridStateBlock11, besselGridStateBlock12, besselGridStateBlock13,
    besselGridStateBlock14, besselGridState009, besselGridState012, besselGridState018, besselGridState022, besselGridState023, besselGridState029, besselGridState031, besselGridState034, besselGridState040, besselGridState041, besselGridState043, besselGridState046, besselGridState047, besselGridState049, besselGridState051, besselGridState057, besselGridState058, besselGridState061, besselGridState062, besselGridState069, besselGridState073, besselGridState074, besselGridState078, besselGridState085, besselGridState089, besselGridState091, besselStateSubset, linearInterval, widenInterval,
    rationalErrorInterval, rationalIntervalSubset, orderedInterval, Finset.sum_range_succ,
    IntervalRat.add, IntervalRat.mul, IntervalRat.scale, IntervalRat.singleton]

theorem compactCertificate249_stateChecks3 :
    compactCertificate249.stateChecks 9 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 89 12 (1113561852794751 / 4000000000000)) (orderedInterval (19775405501 / 1000000000000) (19775406272 / 1000000000000), orderedInterval (-43575419308 / 1000000000000) (-43575418538 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 51 12 (642915235470279 / 4000000000000)) (orderedInterval (-60508434686 / 1000000000000) (-60508434684 / 1000000000000), orderedInterval (-17119134000 / 1000000000000) (-17119133998 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 91 12 (1140864367426611 / 4000000000000)) (orderedInterval (-5473742456 / 1000000000000) (-5473742455 / 1000000000000), orderedInterval (-46916971155 / 1000000000000) (-46916971154 / 1000000000000))) = true
  norm_num [besselStateAtRationalPoint, besselIntervalStepZero,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, besselZeroTransition,
    besselInitial, besselGridStateAt, besselGridStateBlock00, besselGridStateBlock01,
    besselGridStateBlock02, besselGridStateBlock03, besselGridStateBlock04,
    besselGridStateBlock05, besselGridStateBlock06, besselGridStateBlock07,
    besselGridStateBlock08, besselGridStateBlock09, besselGridStateBlock10,
    besselGridStateBlock11, besselGridStateBlock12, besselGridStateBlock13,
    besselGridStateBlock14, besselGridState009, besselGridState012, besselGridState018, besselGridState022, besselGridState023, besselGridState029, besselGridState031, besselGridState034, besselGridState040, besselGridState041, besselGridState043, besselGridState046, besselGridState047, besselGridState049, besselGridState051, besselGridState057, besselGridState058, besselGridState061, besselGridState062, besselGridState069, besselGridState073, besselGridState074, besselGridState078, besselGridState085, besselGridState089, besselGridState091, besselStateSubset, linearInterval, widenInterval,
    rationalErrorInterval, rationalIntervalSubset, orderedInterval, Finset.sum_range_succ,
    IntervalRat.add, IntervalRat.mul, IntervalRat.scale, IntervalRat.singleton]

theorem compactCertificate249_stateChecks4 :
    compactCertificate249.stateChecks 12 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 85 12 (1065943481083359 / 4000000000000)) (orderedInterval (-11400759664 / 1000000000000) (-11400759663 / 1000000000000), orderedInterval (-47507234675 / 1000000000000) (-47507234674 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 61 12 (760707565362447 / 4000000000000)) (orderedInterval (36178518684 / 1000000000000) (36178536700 / 1000000000000), orderedInterval (-45246321562 / 1000000000000) (-45246303546 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 69 12 (862561302169113 / 4000000000000)) (orderedInterval (18362864832 / 1000000000000) (18362865247 / 1000000000000), orderedInterval (-51180049130 / 1000000000000) (-51180048715 / 1000000000000))) = true
  norm_num [besselStateAtRationalPoint, besselIntervalStepZero,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, besselZeroTransition,
    besselInitial, besselGridStateAt, besselGridStateBlock00, besselGridStateBlock01,
    besselGridStateBlock02, besselGridStateBlock03, besselGridStateBlock04,
    besselGridStateBlock05, besselGridStateBlock06, besselGridStateBlock07,
    besselGridStateBlock08, besselGridStateBlock09, besselGridStateBlock10,
    besselGridStateBlock11, besselGridStateBlock12, besselGridStateBlock13,
    besselGridStateBlock14, besselGridState009, besselGridState012, besselGridState018, besselGridState022, besselGridState023, besselGridState029, besselGridState031, besselGridState034, besselGridState040, besselGridState041, besselGridState043, besselGridState046, besselGridState047, besselGridState049, besselGridState051, besselGridState057, besselGridState058, besselGridState061, besselGridState062, besselGridState069, besselGridState073, besselGridState074, besselGridState078, besselGridState085, besselGridState089, besselGridState091, besselStateSubset, linearInterval, widenInterval,
    rationalErrorInterval, rationalIntervalSubset, orderedInterval, Finset.sum_range_succ,
    IntervalRat.add, IntervalRat.mul, IntervalRat.scale, IntervalRat.singleton]

theorem compactCertificate249_stateChecks5 :
    compactCertificate249.stateChecks 15 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 57 12 (719113687212297 / 4000000000000)) (orderedInterval (-59324290955 / 1000000000000) (-59324290937 / 1000000000000), orderedInterval (-4498761566 / 1000000000000) (-4498761548 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 51 12 (635358751182237 / 4000000000000)) (orderedInterval (35585682939 / 1000000000000) (35585692698 / 1000000000000), orderedInterval (-52472359907 / 1000000000000) (-52472350148 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 73 12 (184151730389463 / 800000000000)) (orderedInterval (-52469598673 / 1000000000000) (-52469598457 / 1000000000000), orderedInterval (3658855511 / 1000000000000) (3658855727 / 1000000000000))) = true
  norm_num [besselStateAtRationalPoint, besselIntervalStepZero,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, besselZeroTransition,
    besselInitial, besselGridStateAt, besselGridStateBlock00, besselGridStateBlock01,
    besselGridStateBlock02, besselGridStateBlock03, besselGridStateBlock04,
    besselGridStateBlock05, besselGridStateBlock06, besselGridStateBlock07,
    besselGridStateBlock08, besselGridStateBlock09, besselGridStateBlock10,
    besselGridStateBlock11, besselGridStateBlock12, besselGridStateBlock13,
    besselGridStateBlock14, besselGridState009, besselGridState012, besselGridState018, besselGridState022, besselGridState023, besselGridState029, besselGridState031, besselGridState034, besselGridState040, besselGridState041, besselGridState043, besselGridState046, besselGridState047, besselGridState049, besselGridState051, besselGridState057, besselGridState058, besselGridState061, besselGridState062, besselGridState069, besselGridState073, besselGridState074, besselGridState078, besselGridState085, besselGridState089, besselGridState091, besselStateSubset, linearInterval, widenInterval,
    rationalErrorInterval, rationalIntervalSubset, orderedInterval, Finset.sum_range_succ,
    IntervalRat.add, IntervalRat.mul, IntervalRat.scale, IntervalRat.singleton]

theorem compactCertificate249_stateChecks6 :
    compactCertificate249.stateChecks 18 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 41 12 (509373377631861 / 4000000000000)) (orderedInterval (44323308996 / 1000000000000) (44323333709 / 1000000000000), orderedInterval (-55262060816 / 1000000000000) (-55262036103 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 34 12 (431801453374221 / 4000000000000)) (orderedInterval (72146944795 / 1000000000000) (72146947891 / 1000000000000), orderedInterval (-26642100420 / 1000000000000) (-26642097324 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 22 12 (270201300337263 / 4000000000000)) (orderedInterval (-68353311809 / 1000000000000) (-68353231170 / 1000000000000), orderedInterval (69442145510 / 1000000000000) (69442226149 / 1000000000000))) = true
  norm_num [besselStateAtRationalPoint, besselIntervalStepZero,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, besselZeroTransition,
    besselInitial, besselGridStateAt, besselGridStateBlock00, besselGridStateBlock01,
    besselGridStateBlock02, besselGridStateBlock03, besselGridStateBlock04,
    besselGridStateBlock05, besselGridStateBlock06, besselGridStateBlock07,
    besselGridStateBlock08, besselGridStateBlock09, besselGridStateBlock10,
    besselGridStateBlock11, besselGridStateBlock12, besselGridStateBlock13,
    besselGridStateBlock14, besselGridState009, besselGridState012, besselGridState018, besselGridState022, besselGridState023, besselGridState029, besselGridState031, besselGridState034, besselGridState040, besselGridState041, besselGridState043, besselGridState046, besselGridState047, besselGridState049, besselGridState051, besselGridState057, besselGridState058, besselGridState061, besselGridState062, besselGridState069, besselGridState073, besselGridState074, besselGridState078, besselGridState085, besselGridState089, besselGridState091, besselStateSubset, linearInterval, widenInterval,
    rationalErrorInterval, rationalIntervalSubset, orderedInterval, Finset.sum_range_succ,
    IntervalRat.add, IntervalRat.mul, IntervalRat.scale, IntervalRat.singleton]

theorem compactCertificate249_stateChecks7 :
    compactCertificate249.stateChecks 21 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 12 12 (145315157970321 / 4000000000000)) (orderedInterval (-73466189585 / 1000000000000) (-73466173509 / 1000000000000), orderedInterval (111134465438 / 1000000000000) (111134481514 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 31 12 (394558921713963 / 4000000000000)) (orderedInterval (-71853269475 / 1000000000000) (-71853259772 / 1000000000000), orderedInterval (36295362189 / 1000000000000) (36295371892 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 43 12 (538736475720651 / 4000000000000)) (orderedInterval (-25507931083 / 1000000000000) (-25507931082 / 1000000000000), orderedInterval (-63749890899 / 1000000000000) (-63749890898 / 1000000000000))) = true
  norm_num [besselStateAtRationalPoint, besselIntervalStepZero,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, besselZeroTransition,
    besselInitial, besselGridStateAt, besselGridStateBlock00, besselGridStateBlock01,
    besselGridStateBlock02, besselGridStateBlock03, besselGridStateBlock04,
    besselGridStateBlock05, besselGridStateBlock06, besselGridStateBlock07,
    besselGridStateBlock08, besselGridStateBlock09, besselGridStateBlock10,
    besselGridStateBlock11, besselGridStateBlock12, besselGridStateBlock13,
    besselGridStateBlock14, besselGridState009, besselGridState012, besselGridState018, besselGridState022, besselGridState023, besselGridState029, besselGridState031, besselGridState034, besselGridState040, besselGridState041, besselGridState043, besselGridState046, besselGridState047, besselGridState049, besselGridState051, besselGridState057, besselGridState058, besselGridState061, besselGridState062, besselGridState069, besselGridState073, besselGridState074, besselGridState078, besselGridState085, besselGridState089, besselGridState091, besselStateSubset, linearInterval, widenInterval,
    rationalErrorInterval, rationalIntervalSubset, orderedInterval, Finset.sum_range_succ,
    IntervalRat.add, IntervalRat.mul, IntervalRat.scale, IntervalRat.singleton]

theorem compactCertificate249_stateChecks8 :
    compactCertificate249.stateChecks 24 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 18 12 (227798699662737 / 4000000000000)) (orderedInterval (97924573159 / 1000000000000) (97924573160 / 1000000000000), orderedInterval (39003928308 / 1000000000000) (39003928309 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 74 12 (925989067123377 / 4000000000000)) (orderedInterval (-10198833519 / 1000000000000) (-10198833471 / 1000000000000), orderedInterval (51461308667 / 1000000000000) (51461308715 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 49 12 (618517782742143 / 4000000000000)) (orderedInterval (-63876093791 / 1000000000000) (-63876093779 / 1000000000000), orderedInterval (-5867203656 / 1000000000000) (-5867203644 / 1000000000000))) = true
  norm_num [besselStateAtRationalPoint, besselIntervalStepZero,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, besselZeroTransition,
    besselInitial, besselGridStateAt, besselGridStateBlock00, besselGridStateBlock01,
    besselGridStateBlock02, besselGridStateBlock03, besselGridStateBlock04,
    besselGridStateBlock05, besselGridStateBlock06, besselGridStateBlock07,
    besselGridStateBlock08, besselGridStateBlock09, besselGridStateBlock10,
    besselGridStateBlock11, besselGridStateBlock12, besselGridStateBlock13,
    besselGridStateBlock14, besselGridState009, besselGridState012, besselGridState018, besselGridState022, besselGridState023, besselGridState029, besselGridState031, besselGridState034, besselGridState040, besselGridState041, besselGridState043, besselGridState046, besselGridState047, besselGridState049, besselGridState051, besselGridState057, besselGridState058, besselGridState061, besselGridState062, besselGridState069, besselGridState073, besselGridState074, besselGridState078, besselGridState085, besselGridState089, besselGridState091, besselStateSubset, linearInterval, widenInterval,
    rationalErrorInterval, rationalIntervalSubset, orderedInterval, Finset.sum_range_succ,
    IntervalRat.add, IntervalRat.mul, IntervalRat.scale, IntervalRat.singleton]

theorem compactCertificate249_states : ∀ j,
    BesselStateValid (compactCertificate249.point j) (compactCertificate249.state j) :=
  compactCertificate249.statesValid_of_checks3 compactCertificate249_stateChecks0
    compactCertificate249_stateChecks1 compactCertificate249_stateChecks2
    compactCertificate249_stateChecks3 compactCertificate249_stateChecks4
    compactCertificate249_stateChecks5 compactCertificate249_stateChecks6
    compactCertificate249_stateChecks7 compactCertificate249_stateChecks8

theorem compactCertificate249_chunkChecks0_0 :
    compactCertificate249.chunkChecks (0 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 0) <| besselDerivativeNearFromState (249 / 2) 0 (IntervalRat.scale (249 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-26478023941 / 1000000000000) (-26478022831 / 1000000000000), orderedInterval (66531902726 / 1000000000000) (66531903836 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 0) <| besselDerivativeNearFromState (366824546027349 / 4000000000000) 0 (IntervalRat.scale (249 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-81868157540 / 1000000000000) (-81868157538 / 1000000000000), orderedInterval (-15028232422 / 1000000000000) (-15028232420 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 0) <| besselDerivativeNearFromState (118623521299317 / 800000000000) 0 (IntervalRat.scale (249 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-64669005345 / 1000000000000) (-64669005341 / 1000000000000), orderedInterval (-10330696138 / 1000000000000) (-10330696134 / 1000000000000)))) (orderedInterval (-15052665139 / 1000000000000) (-15052664689 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 0) <| besselDerivativeNearFromState (107038487657343 / 4000000000000) 0 (IntervalRat.scale (249 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (103306485014 / 1000000000000) (103306547729 / 1000000000000), orderedInterval (-116465652565 / 1000000000000) (-116465589851 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 0) <| besselDerivativeNearFromState (287520434056371 / 4000000000000) 0 (IntervalRat.scale (249 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-37265391105 / 1000000000000) (-37265391104 / 1000000000000), orderedInterval (-86159117557 / 1000000000000) (-86159117556 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 0) <| besselDerivativeNearFromState (780673909152807 / 4000000000000) 0 (IntervalRat.scale (249 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (52686302271 / 1000000000000) (52686302272 / 1000000000000), orderedInterval (21911443299 / 1000000000000) (21911443300 / 1000000000000)))) (orderedInterval (-6226877615 / 1000000000000) (-6226876919 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 0) <| besselDerivativeNearFromState (575040868112991 / 4000000000000) 0 (IntervalRat.scale (249 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (2094752154 / 1000000000000) (2094752157 / 1000000000000), orderedInterval (66505745442 / 1000000000000) (66505745445 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 0) <| besselDerivativeNearFromState (985342328769243 / 4000000000000) 0 (IntervalRat.scale (249 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (44479769804 / 1000000000000) (44479799243 / 1000000000000), orderedInterval (-24705448160 / 1000000000000) (-24705418721 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 0) <| besselDerivativeNearFromState (725798699662737 / 4000000000000) 0 (IntervalRat.scale (249 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (1303622205 / 1000000000000) (1303622208 / 1000000000000), orderedInterval (59214932333 / 1000000000000) (59214932336 / 1000000000000)))) (orderedInterval (-1340429000 / 1000000000000) (-1340428084 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate249_chunkChecks0_1 :
    compactCertificate249.chunkChecks (0 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 0) <| besselDerivativeNearFromState (1113561852794751 / 4000000000000) 0 (IntervalRat.scale (249 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (19775405501 / 1000000000000) (19775406272 / 1000000000000), orderedInterval (-43575419308 / 1000000000000) (-43575418538 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 0) <| besselDerivativeNearFromState (642915235470279 / 4000000000000) 0 (IntervalRat.scale (249 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-60508434686 / 1000000000000) (-60508434684 / 1000000000000), orderedInterval (-17119134000 / 1000000000000) (-17119133998 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 0) <| besselDerivativeNearFromState (1140864367426611 / 4000000000000) 0 (IntervalRat.scale (249 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-5473742456 / 1000000000000) (-5473742455 / 1000000000000), orderedInterval (-46916971155 / 1000000000000) (-46916971154 / 1000000000000)))) (orderedInterval (-8775152779 / 1000000000000) (-8775152592 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 0) <| besselDerivativeNearFromState (1065943481083359 / 4000000000000) 0 (IntervalRat.scale (249 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-11400759664 / 1000000000000) (-11400759663 / 1000000000000), orderedInterval (-47507234675 / 1000000000000) (-47507234674 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 0) <| besselDerivativeNearFromState (760707565362447 / 4000000000000) 0 (IntervalRat.scale (249 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (36178518684 / 1000000000000) (36178536700 / 1000000000000), orderedInterval (-45246321562 / 1000000000000) (-45246303546 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 0) <| besselDerivativeNearFromState (862561302169113 / 4000000000000) 0 (IntervalRat.scale (249 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (18362864832 / 1000000000000) (18362865247 / 1000000000000), orderedInterval (-51180049130 / 1000000000000) (-51180048715 / 1000000000000)))) (orderedInterval (3534036626 / 1000000000000) (3534038347 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 0) <| besselDerivativeNearFromState (719113687212297 / 4000000000000) 0 (IntervalRat.scale (249 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-59324290955 / 1000000000000) (-59324290937 / 1000000000000), orderedInterval (-4498761566 / 1000000000000) (-4498761548 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 0) <| besselDerivativeNearFromState (635358751182237 / 4000000000000) 0 (IntervalRat.scale (249 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (35585682939 / 1000000000000) (35585692698 / 1000000000000), orderedInterval (-52472359907 / 1000000000000) (-52472350148 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 0) <| besselDerivativeNearFromState (184151730389463 / 800000000000) 0 (IntervalRat.scale (249 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-52469598673 / 1000000000000) (-52469598457 / 1000000000000), orderedInterval (3658855511 / 1000000000000) (3658855727 / 1000000000000)))) (orderedInterval (-4064937264 / 1000000000000) (-4064936687 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate249_chunkChecks0_2 :
    compactCertificate249.chunkChecks (0 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 0) <| besselDerivativeNearFromState (509373377631861 / 4000000000000) 0 (IntervalRat.scale (249 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (44323308996 / 1000000000000) (44323333709 / 1000000000000), orderedInterval (-55262060816 / 1000000000000) (-55262036103 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 0) <| besselDerivativeNearFromState (431801453374221 / 4000000000000) 0 (IntervalRat.scale (249 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (72146944795 / 1000000000000) (72146947891 / 1000000000000), orderedInterval (-26642100420 / 1000000000000) (-26642097324 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 0) <| besselDerivativeNearFromState (270201300337263 / 4000000000000) 0 (IntervalRat.scale (249 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-68353311809 / 1000000000000) (-68353231170 / 1000000000000), orderedInterval (69442145510 / 1000000000000) (69442226149 / 1000000000000)))) (orderedInterval (-13395740746 / 1000000000000) (-13395733962 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 0) <| besselDerivativeNearFromState (145315157970321 / 4000000000000) 0 (IntervalRat.scale (249 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-73466189585 / 1000000000000) (-73466173509 / 1000000000000), orderedInterval (111134465438 / 1000000000000) (111134481514 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 0) <| besselDerivativeNearFromState (394558921713963 / 4000000000000) 0 (IntervalRat.scale (249 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-71853269475 / 1000000000000) (-71853259772 / 1000000000000), orderedInterval (36295362189 / 1000000000000) (36295371892 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 0) <| besselDerivativeNearFromState (538736475720651 / 4000000000000) 0 (IntervalRat.scale (249 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-25507931083 / 1000000000000) (-25507931082 / 1000000000000), orderedInterval (-63749890899 / 1000000000000) (-63749890898 / 1000000000000)))) (orderedInterval (4941585484 / 1000000000000) (4941586017 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 0) <| besselDerivativeNearFromState (227798699662737 / 4000000000000) 0 (IntervalRat.scale (249 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (97924573159 / 1000000000000) (97924573160 / 1000000000000), orderedInterval (39003928308 / 1000000000000) (39003928309 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 0) <| besselDerivativeNearFromState (925989067123377 / 4000000000000) 0 (IntervalRat.scale (249 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-10198833519 / 1000000000000) (-10198833471 / 1000000000000), orderedInterval (51461308667 / 1000000000000) (51461308715 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 0) <| besselDerivativeNearFromState (618517782742143 / 4000000000000) 0 (IntervalRat.scale (249 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-63876093791 / 1000000000000) (-63876093779 / 1000000000000), orderedInterval (-5867203656 / 1000000000000) (-5867203644 / 1000000000000)))) (orderedInterval (13405374231 / 1000000000000) (13405374272 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate249_chunkChecks0 :
    compactCertificate249.chunkChecks (0 : Fin 5) 0 9 = true :=
  compactCertificate249.chunkChecks_nine_of_three (0 : Fin 5) compactCertificate249_chunkChecks0_0
    compactCertificate249_chunkChecks0_1 compactCertificate249_chunkChecks0_2

theorem compactCertificate249_chunkChecks1_0 :
    compactCertificate249.chunkChecks (1 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 1) <| besselDerivativeNearFromState (249 / 2) 1 (IntervalRat.scale (249 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-26478023941 / 1000000000000) (-26478022831 / 1000000000000), orderedInterval (66531902726 / 1000000000000) (66531903836 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 1) <| besselDerivativeNearFromState (366824546027349 / 4000000000000) 1 (IntervalRat.scale (249 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-81868157540 / 1000000000000) (-81868157538 / 1000000000000), orderedInterval (-15028232422 / 1000000000000) (-15028232420 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 1) <| besselDerivativeNearFromState (118623521299317 / 800000000000) 1 (IntervalRat.scale (249 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-64669005345 / 1000000000000) (-64669005341 / 1000000000000), orderedInterval (-10330696138 / 1000000000000) (-10330696134 / 1000000000000)))) (orderedInterval (25545764764 / 1000000000000) (25545765215 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 1) <| besselDerivativeNearFromState (107038487657343 / 4000000000000) 1 (IntervalRat.scale (249 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (103306485014 / 1000000000000) (103306547729 / 1000000000000), orderedInterval (-116465652565 / 1000000000000) (-116465589851 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 1) <| besselDerivativeNearFromState (287520434056371 / 4000000000000) 1 (IntervalRat.scale (249 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-37265391105 / 1000000000000) (-37265391104 / 1000000000000), orderedInterval (-86159117557 / 1000000000000) (-86159117556 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 1) <| besselDerivativeNearFromState (780673909152807 / 4000000000000) 1 (IntervalRat.scale (249 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (52686302271 / 1000000000000) (52686302272 / 1000000000000), orderedInterval (21911443299 / 1000000000000) (21911443300 / 1000000000000)))) (orderedInterval (-3986494921 / 1000000000000) (-3986494757 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 1) <| besselDerivativeNearFromState (575040868112991 / 4000000000000) 1 (IntervalRat.scale (249 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (2094752154 / 1000000000000) (2094752157 / 1000000000000), orderedInterval (66505745442 / 1000000000000) (66505745445 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 1) <| besselDerivativeNearFromState (985342328769243 / 4000000000000) 1 (IntervalRat.scale (249 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (44479769804 / 1000000000000) (44479799243 / 1000000000000), orderedInterval (-24705448160 / 1000000000000) (-24705418721 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 1) <| besselDerivativeNearFromState (725798699662737 / 4000000000000) 1 (IntervalRat.scale (249 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (1303622205 / 1000000000000) (1303622208 / 1000000000000), orderedInterval (59214932333 / 1000000000000) (59214932336 / 1000000000000)))) (orderedInterval (3593455808 / 1000000000000) (3593457618 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate249_chunkChecks1_1 :
    compactCertificate249.chunkChecks (1 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 1) <| besselDerivativeNearFromState (1113561852794751 / 4000000000000) 1 (IntervalRat.scale (249 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (19775405501 / 1000000000000) (19775406272 / 1000000000000), orderedInterval (-43575419308 / 1000000000000) (-43575418538 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 1) <| besselDerivativeNearFromState (642915235470279 / 4000000000000) 1 (IntervalRat.scale (249 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-60508434686 / 1000000000000) (-60508434684 / 1000000000000), orderedInterval (-17119134000 / 1000000000000) (-17119133998 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 1) <| besselDerivativeNearFromState (1140864367426611 / 4000000000000) 1 (IntervalRat.scale (249 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-5473742456 / 1000000000000) (-5473742455 / 1000000000000), orderedInterval (-46916971155 / 1000000000000) (-46916971154 / 1000000000000)))) (orderedInterval (396843194 / 1000000000000) (396843603 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 1) <| besselDerivativeNearFromState (1065943481083359 / 4000000000000) 1 (IntervalRat.scale (249 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-11400759664 / 1000000000000) (-11400759663 / 1000000000000), orderedInterval (-47507234675 / 1000000000000) (-47507234674 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 1) <| besselDerivativeNearFromState (760707565362447 / 4000000000000) 1 (IntervalRat.scale (249 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (36178518684 / 1000000000000) (36178536700 / 1000000000000), orderedInterval (-45246321562 / 1000000000000) (-45246303546 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 1) <| besselDerivativeNearFromState (862561302169113 / 4000000000000) 1 (IntervalRat.scale (249 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (18362864832 / 1000000000000) (18362865247 / 1000000000000), orderedInterval (-51180049130 / 1000000000000) (-51180048715 / 1000000000000)))) (orderedInterval (-4251340193 / 1000000000000) (-4251337562 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 1) <| besselDerivativeNearFromState (719113687212297 / 4000000000000) 1 (IntervalRat.scale (249 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-59324290955 / 1000000000000) (-59324290937 / 1000000000000), orderedInterval (-4498761566 / 1000000000000) (-4498761548 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 1) <| besselDerivativeNearFromState (635358751182237 / 4000000000000) 1 (IntervalRat.scale (249 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (35585682939 / 1000000000000) (35585692698 / 1000000000000), orderedInterval (-52472359907 / 1000000000000) (-52472350148 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 1) <| besselDerivativeNearFromState (184151730389463 / 800000000000) 1 (IntervalRat.scale (249 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-52469598673 / 1000000000000) (-52469598457 / 1000000000000), orderedInterval (3658855511 / 1000000000000) (3658855727 / 1000000000000)))) (orderedInterval (3929249922 / 1000000000000) (3929250663 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate249_chunkChecks1_2 :
    compactCertificate249.chunkChecks (1 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 1) <| besselDerivativeNearFromState (509373377631861 / 4000000000000) 1 (IntervalRat.scale (249 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (44323308996 / 1000000000000) (44323333709 / 1000000000000), orderedInterval (-55262060816 / 1000000000000) (-55262036103 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 1) <| besselDerivativeNearFromState (431801453374221 / 4000000000000) 1 (IntervalRat.scale (249 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (72146944795 / 1000000000000) (72146947891 / 1000000000000), orderedInterval (-26642100420 / 1000000000000) (-26642097324 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 1) <| besselDerivativeNearFromState (270201300337263 / 4000000000000) 1 (IntervalRat.scale (249 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-68353311809 / 1000000000000) (-68353231170 / 1000000000000), orderedInterval (69442145510 / 1000000000000) (69442226149 / 1000000000000)))) (orderedInterval (11571870464 / 1000000000000) (11571876111 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 1) <| besselDerivativeNearFromState (145315157970321 / 4000000000000) 1 (IntervalRat.scale (249 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-73466189585 / 1000000000000) (-73466173509 / 1000000000000), orderedInterval (111134465438 / 1000000000000) (111134481514 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 1) <| besselDerivativeNearFromState (394558921713963 / 4000000000000) 1 (IntervalRat.scale (249 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-71853269475 / 1000000000000) (-71853259772 / 1000000000000), orderedInterval (36295362189 / 1000000000000) (36295371892 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 1) <| besselDerivativeNearFromState (538736475720651 / 4000000000000) 1 (IntervalRat.scale (249 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-25507931083 / 1000000000000) (-25507931082 / 1000000000000), orderedInterval (-63749890899 / 1000000000000) (-63749890898 / 1000000000000)))) (orderedInterval (4034179902 / 1000000000000) (4034180178 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 1) <| besselDerivativeNearFromState (227798699662737 / 4000000000000) 1 (IntervalRat.scale (249 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (97924573159 / 1000000000000) (97924573160 / 1000000000000), orderedInterval (39003928308 / 1000000000000) (39003928309 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 1) <| besselDerivativeNearFromState (925989067123377 / 4000000000000) 1 (IntervalRat.scale (249 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-10198833519 / 1000000000000) (-10198833471 / 1000000000000), orderedInterval (51461308667 / 1000000000000) (51461308715 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 1) <| besselDerivativeNearFromState (618517782742143 / 4000000000000) 1 (IntervalRat.scale (249 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-63876093791 / 1000000000000) (-63876093779 / 1000000000000), orderedInterval (-5867203656 / 1000000000000) (-5867203644 / 1000000000000)))) (orderedInterval (-6314365714 / 1000000000000) (-6314365654 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate249_chunkChecks1 :
    compactCertificate249.chunkChecks (1 : Fin 5) 0 9 = true :=
  compactCertificate249.chunkChecks_nine_of_three (1 : Fin 5) compactCertificate249_chunkChecks1_0
    compactCertificate249_chunkChecks1_1 compactCertificate249_chunkChecks1_2

theorem compactCertificate249_chunkChecks2_0 :
    compactCertificate249.chunkChecks (2 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 2) <| besselDerivativeNearFromState (249 / 2) 2 (IntervalRat.scale (249 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-26478023941 / 1000000000000) (-26478022831 / 1000000000000), orderedInterval (66531902726 / 1000000000000) (66531903836 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 2) <| besselDerivativeNearFromState (366824546027349 / 4000000000000) 2 (IntervalRat.scale (249 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-81868157540 / 1000000000000) (-81868157538 / 1000000000000), orderedInterval (-15028232422 / 1000000000000) (-15028232420 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 2) <| besselDerivativeNearFromState (118623521299317 / 800000000000) 2 (IntervalRat.scale (249 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-64669005345 / 1000000000000) (-64669005341 / 1000000000000), orderedInterval (-10330696138 / 1000000000000) (-10330696134 / 1000000000000)))) (orderedInterval (16086594331 / 1000000000000) (16086594786 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 2) <| besselDerivativeNearFromState (107038487657343 / 4000000000000) 2 (IntervalRat.scale (249 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (103306485014 / 1000000000000) (103306547729 / 1000000000000), orderedInterval (-116465652565 / 1000000000000) (-116465589851 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 2) <| besselDerivativeNearFromState (287520434056371 / 4000000000000) 2 (IntervalRat.scale (249 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-37265391105 / 1000000000000) (-37265391104 / 1000000000000), orderedInterval (-86159117557 / 1000000000000) (-86159117556 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 2) <| besselDerivativeNearFromState (780673909152807 / 4000000000000) 2 (IntervalRat.scale (249 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (52686302271 / 1000000000000) (52686302272 / 1000000000000), orderedInterval (21911443299 / 1000000000000) (21911443300 / 1000000000000)))) (orderedInterval (9741511243 / 1000000000000) (9741511300 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 2) <| besselDerivativeNearFromState (575040868112991 / 4000000000000) 2 (IntervalRat.scale (249 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (2094752154 / 1000000000000) (2094752157 / 1000000000000), orderedInterval (66505745442 / 1000000000000) (66505745445 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 2) <| besselDerivativeNearFromState (985342328769243 / 4000000000000) 2 (IntervalRat.scale (249 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (44479769804 / 1000000000000) (44479799243 / 1000000000000), orderedInterval (-24705448160 / 1000000000000) (-24705418721 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 2) <| besselDerivativeNearFromState (725798699662737 / 4000000000000) 2 (IntervalRat.scale (249 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (1303622205 / 1000000000000) (1303622208 / 1000000000000), orderedInterval (59214932333 / 1000000000000) (59214932336 / 1000000000000)))) (orderedInterval (5275137082 / 1000000000000) (5275140673 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate249_chunkChecks2_1 :
    compactCertificate249.chunkChecks (2 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 2) <| besselDerivativeNearFromState (1113561852794751 / 4000000000000) 2 (IntervalRat.scale (249 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (19775405501 / 1000000000000) (19775406272 / 1000000000000), orderedInterval (-43575419308 / 1000000000000) (-43575418538 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 2) <| besselDerivativeNearFromState (642915235470279 / 4000000000000) 2 (IntervalRat.scale (249 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-60508434686 / 1000000000000) (-60508434684 / 1000000000000), orderedInterval (-17119134000 / 1000000000000) (-17119133998 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 2) <| besselDerivativeNearFromState (1140864367426611 / 4000000000000) 2 (IntervalRat.scale (249 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-5473742456 / 1000000000000) (-5473742455 / 1000000000000), orderedInterval (-46916971155 / 1000000000000) (-46916971154 / 1000000000000)))) (orderedInterval (29121772727 / 1000000000000) (29121773635 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 2) <| besselDerivativeNearFromState (1065943481083359 / 4000000000000) 2 (IntervalRat.scale (249 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-11400759664 / 1000000000000) (-11400759663 / 1000000000000), orderedInterval (-47507234675 / 1000000000000) (-47507234674 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 2) <| besselDerivativeNearFromState (760707565362447 / 4000000000000) 2 (IntervalRat.scale (249 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (36178518684 / 1000000000000) (36178536700 / 1000000000000), orderedInterval (-45246321562 / 1000000000000) (-45246303546 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 2) <| besselDerivativeNearFromState (862561302169113 / 4000000000000) 2 (IntervalRat.scale (249 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (18362864832 / 1000000000000) (18362865247 / 1000000000000), orderedInterval (-51180049130 / 1000000000000) (-51180048715 / 1000000000000)))) (orderedInterval (-8612710551 / 1000000000000) (-8612706508 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 2) <| besselDerivativeNearFromState (719113687212297 / 4000000000000) 2 (IntervalRat.scale (249 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-59324290955 / 1000000000000) (-59324290937 / 1000000000000), orderedInterval (-4498761566 / 1000000000000) (-4498761548 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 2) <| besselDerivativeNearFromState (635358751182237 / 4000000000000) 2 (IntervalRat.scale (249 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (35585682939 / 1000000000000) (35585692698 / 1000000000000), orderedInterval (-52472359907 / 1000000000000) (-52472350148 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 2) <| besselDerivativeNearFromState (184151730389463 / 800000000000) 2 (IntervalRat.scale (249 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-52469598673 / 1000000000000) (-52469598457 / 1000000000000), orderedInterval (3658855511 / 1000000000000) (3658855727 / 1000000000000)))) (orderedInterval (9304136376 / 1000000000000) (9304137337 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate249_chunkChecks2_2 :
    compactCertificate249.chunkChecks (2 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 2) <| besselDerivativeNearFromState (509373377631861 / 4000000000000) 2 (IntervalRat.scale (249 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (44323308996 / 1000000000000) (44323333709 / 1000000000000), orderedInterval (-55262060816 / 1000000000000) (-55262036103 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 2) <| besselDerivativeNearFromState (431801453374221 / 4000000000000) 2 (IntervalRat.scale (249 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (72146944795 / 1000000000000) (72146947891 / 1000000000000), orderedInterval (-26642100420 / 1000000000000) (-26642097324 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 2) <| besselDerivativeNearFromState (270201300337263 / 4000000000000) 2 (IntervalRat.scale (249 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-68353311809 / 1000000000000) (-68353231170 / 1000000000000), orderedInterval (69442145510 / 1000000000000) (69442226149 / 1000000000000)))) (orderedInterval (11046537248 / 1000000000000) (11046542360 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 2) <| besselDerivativeNearFromState (145315157970321 / 4000000000000) 2 (IntervalRat.scale (249 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-73466189585 / 1000000000000) (-73466173509 / 1000000000000), orderedInterval (111134465438 / 1000000000000) (111134481514 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 2) <| besselDerivativeNearFromState (394558921713963 / 4000000000000) 2 (IntervalRat.scale (249 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-71853269475 / 1000000000000) (-71853259772 / 1000000000000), orderedInterval (36295362189 / 1000000000000) (36295371892 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 2) <| besselDerivativeNearFromState (538736475720651 / 4000000000000) 2 (IntervalRat.scale (249 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-25507931083 / 1000000000000) (-25507931082 / 1000000000000), orderedInterval (-63749890899 / 1000000000000) (-63749890898 / 1000000000000)))) (orderedInterval (-3458970452 / 1000000000000) (-3458970272 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 2) <| besselDerivativeNearFromState (227798699662737 / 4000000000000) 2 (IntervalRat.scale (249 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (97924573159 / 1000000000000) (97924573160 / 1000000000000), orderedInterval (39003928308 / 1000000000000) (39003928309 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 2) <| besselDerivativeNearFromState (925989067123377 / 4000000000000) 2 (IntervalRat.scale (249 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-10198833519 / 1000000000000) (-10198833471 / 1000000000000), orderedInterval (51461308667 / 1000000000000) (51461308715 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 2) <| besselDerivativeNearFromState (618517782742143 / 4000000000000) 2 (IntervalRat.scale (249 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-63876093791 / 1000000000000) (-63876093779 / 1000000000000), orderedInterval (-5867203656 / 1000000000000) (-5867203644 / 1000000000000)))) (orderedInterval (-21430671956 / 1000000000000) (-21430671867 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate249_chunkChecks2 :
    compactCertificate249.chunkChecks (2 : Fin 5) 0 9 = true :=
  compactCertificate249.chunkChecks_nine_of_three (2 : Fin 5) compactCertificate249_chunkChecks2_0
    compactCertificate249_chunkChecks2_1 compactCertificate249_chunkChecks2_2

theorem compactCertificate249_chunkChecks3_0 :
    compactCertificate249.chunkChecks (3 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 3) <| besselDerivativeNearFromState (249 / 2) 3 (IntervalRat.scale (249 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-26478023941 / 1000000000000) (-26478022831 / 1000000000000), orderedInterval (66531902726 / 1000000000000) (66531903836 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 3) <| besselDerivativeNearFromState (366824546027349 / 4000000000000) 3 (IntervalRat.scale (249 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-81868157540 / 1000000000000) (-81868157538 / 1000000000000), orderedInterval (-15028232422 / 1000000000000) (-15028232420 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 3) <| besselDerivativeNearFromState (118623521299317 / 800000000000) 3 (IntervalRat.scale (249 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-64669005345 / 1000000000000) (-64669005341 / 1000000000000), orderedInterval (-10330696138 / 1000000000000) (-10330696134 / 1000000000000)))) (orderedInterval (-25418365999 / 1000000000000) (-25418365541 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 3) <| besselDerivativeNearFromState (107038487657343 / 4000000000000) 3 (IntervalRat.scale (249 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (103306485014 / 1000000000000) (103306547729 / 1000000000000), orderedInterval (-116465652565 / 1000000000000) (-116465589851 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 3) <| besselDerivativeNearFromState (287520434056371 / 4000000000000) 3 (IntervalRat.scale (249 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-37265391105 / 1000000000000) (-37265391104 / 1000000000000), orderedInterval (-86159117557 / 1000000000000) (-86159117556 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 3) <| besselDerivativeNearFromState (780673909152807 / 4000000000000) 3 (IntervalRat.scale (249 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (52686302271 / 1000000000000) (52686302272 / 1000000000000), orderedInterval (21911443299 / 1000000000000) (21911443300 / 1000000000000)))) (orderedInterval (6515013964 / 1000000000000) (6515014008 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 3) <| besselDerivativeNearFromState (575040868112991 / 4000000000000) 3 (IntervalRat.scale (249 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (2094752154 / 1000000000000) (2094752157 / 1000000000000), orderedInterval (66505745442 / 1000000000000) (66505745445 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 3) <| besselDerivativeNearFromState (985342328769243 / 4000000000000) 3 (IntervalRat.scale (249 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (44479769804 / 1000000000000) (44479799243 / 1000000000000), orderedInterval (-24705448160 / 1000000000000) (-24705418721 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 3) <| besselDerivativeNearFromState (725798699662737 / 4000000000000) 3 (IntervalRat.scale (249 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (1303622205 / 1000000000000) (1303622208 / 1000000000000), orderedInterval (59214932333 / 1000000000000) (59214932336 / 1000000000000)))) (orderedInterval (-10374948464 / 1000000000000) (-10374941362 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate249_chunkChecks3_1 :
    compactCertificate249.chunkChecks (3 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 3) <| besselDerivativeNearFromState (1113561852794751 / 4000000000000) 3 (IntervalRat.scale (249 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (19775405501 / 1000000000000) (19775406272 / 1000000000000), orderedInterval (-43575419308 / 1000000000000) (-43575418538 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 3) <| besselDerivativeNearFromState (642915235470279 / 4000000000000) 3 (IntervalRat.scale (249 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-60508434686 / 1000000000000) (-60508434684 / 1000000000000), orderedInterval (-17119134000 / 1000000000000) (-17119133998 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 3) <| besselDerivativeNearFromState (1140864367426611 / 4000000000000) 3 (IntervalRat.scale (249 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-5473742456 / 1000000000000) (-5473742455 / 1000000000000), orderedInterval (-46916971155 / 1000000000000) (-46916971154 / 1000000000000)))) (orderedInterval (-3884273118 / 1000000000000) (-3884271099 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 3) <| besselDerivativeNearFromState (1065943481083359 / 4000000000000) 3 (IntervalRat.scale (249 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-11400759664 / 1000000000000) (-11400759663 / 1000000000000), orderedInterval (-47507234675 / 1000000000000) (-47507234674 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 3) <| besselDerivativeNearFromState (760707565362447 / 4000000000000) 3 (IntervalRat.scale (249 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (36178518684 / 1000000000000) (36178536700 / 1000000000000), orderedInterval (-45246321562 / 1000000000000) (-45246303546 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 3) <| besselDerivativeNearFromState (862561302169113 / 4000000000000) 3 (IntervalRat.scale (249 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (18362864832 / 1000000000000) (18362865247 / 1000000000000), orderedInterval (-51180049130 / 1000000000000) (-51180048715 / 1000000000000)))) (orderedInterval (5562489621 / 1000000000000) (5562495804 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 3) <| besselDerivativeNearFromState (719113687212297 / 4000000000000) 3 (IntervalRat.scale (249 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-59324290955 / 1000000000000) (-59324290937 / 1000000000000), orderedInterval (-4498761566 / 1000000000000) (-4498761548 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 3) <| besselDerivativeNearFromState (635358751182237 / 4000000000000) 3 (IntervalRat.scale (249 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (35585682939 / 1000000000000) (35585692698 / 1000000000000), orderedInterval (-52472359907 / 1000000000000) (-52472350148 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 3) <| besselDerivativeNearFromState (184151730389463 / 800000000000) 3 (IntervalRat.scale (249 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-52469598673 / 1000000000000) (-52469598457 / 1000000000000), orderedInterval (3658855511 / 1000000000000) (3658855727 / 1000000000000)))) (orderedInterval (-6746053331 / 1000000000000) (-6746052088 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate249_chunkChecks3_2 :
    compactCertificate249.chunkChecks (3 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 3) <| besselDerivativeNearFromState (509373377631861 / 4000000000000) 3 (IntervalRat.scale (249 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (44323308996 / 1000000000000) (44323333709 / 1000000000000), orderedInterval (-55262060816 / 1000000000000) (-55262036103 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 3) <| besselDerivativeNearFromState (431801453374221 / 4000000000000) 3 (IntervalRat.scale (249 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (72146944795 / 1000000000000) (72146947891 / 1000000000000), orderedInterval (-26642100420 / 1000000000000) (-26642097324 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 3) <| besselDerivativeNearFromState (270201300337263 / 4000000000000) 3 (IntervalRat.scale (249 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-68353311809 / 1000000000000) (-68353231170 / 1000000000000), orderedInterval (69442145510 / 1000000000000) (69442226149 / 1000000000000)))) (orderedInterval (-10887371905 / 1000000000000) (-10887367075 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 3) <| besselDerivativeNearFromState (145315157970321 / 4000000000000) 3 (IntervalRat.scale (249 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-73466189585 / 1000000000000) (-73466173509 / 1000000000000), orderedInterval (111134465438 / 1000000000000) (111134481514 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 3) <| besselDerivativeNearFromState (394558921713963 / 4000000000000) 3 (IntervalRat.scale (249 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-71853269475 / 1000000000000) (-71853259772 / 1000000000000), orderedInterval (36295362189 / 1000000000000) (36295371892 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 3) <| besselDerivativeNearFromState (538736475720651 / 4000000000000) 3 (IntervalRat.scale (249 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-25507931083 / 1000000000000) (-25507931082 / 1000000000000), orderedInterval (-63749890899 / 1000000000000) (-63749890898 / 1000000000000)))) (orderedInterval (-5696879878 / 1000000000000) (-5696879745 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 3) <| besselDerivativeNearFromState (227798699662737 / 4000000000000) 3 (IntervalRat.scale (249 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (97924573159 / 1000000000000) (97924573160 / 1000000000000), orderedInterval (39003928308 / 1000000000000) (39003928309 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 3) <| besselDerivativeNearFromState (925989067123377 / 4000000000000) 3 (IntervalRat.scale (249 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-10198833519 / 1000000000000) (-10198833471 / 1000000000000), orderedInterval (51461308667 / 1000000000000) (51461308715 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 3) <| besselDerivativeNearFromState (618517782742143 / 4000000000000) 3 (IntervalRat.scale (249 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-63876093791 / 1000000000000) (-63876093779 / 1000000000000), orderedInterval (-5867203656 / 1000000000000) (-5867203644 / 1000000000000)))) (orderedInterval (24970627907 / 1000000000000) (24970628047 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate249_chunkChecks3 :
    compactCertificate249.chunkChecks (3 : Fin 5) 0 9 = true :=
  compactCertificate249.chunkChecks_nine_of_three (3 : Fin 5) compactCertificate249_chunkChecks3_0
    compactCertificate249_chunkChecks3_1 compactCertificate249_chunkChecks3_2

theorem compactCertificate249_chunkChecks4_0 :
    compactCertificate249.chunkChecks (4 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 4) <| besselDerivativeNearFromState (249 / 2) 4 (IntervalRat.scale (249 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-26478023941 / 1000000000000) (-26478022831 / 1000000000000), orderedInterval (66531902726 / 1000000000000) (66531903836 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 4) <| besselDerivativeNearFromState (366824546027349 / 4000000000000) 4 (IntervalRat.scale (249 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-81868157540 / 1000000000000) (-81868157538 / 1000000000000), orderedInterval (-15028232422 / 1000000000000) (-15028232420 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 4) <| besselDerivativeNearFromState (118623521299317 / 800000000000) 4 (IntervalRat.scale (249 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-64669005345 / 1000000000000) (-64669005341 / 1000000000000), orderedInterval (-10330696138 / 1000000000000) (-10330696134 / 1000000000000)))) (orderedInterval (-17945737727 / 1000000000000) (-17945737264 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 4) <| besselDerivativeNearFromState (107038487657343 / 4000000000000) 4 (IntervalRat.scale (249 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (103306485014 / 1000000000000) (103306547729 / 1000000000000), orderedInterval (-116465652565 / 1000000000000) (-116465589851 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 4) <| besselDerivativeNearFromState (287520434056371 / 4000000000000) 4 (IntervalRat.scale (249 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-37265391105 / 1000000000000) (-37265391104 / 1000000000000), orderedInterval (-86159117557 / 1000000000000) (-86159117556 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 4) <| besselDerivativeNearFromState (780673909152807 / 4000000000000) 4 (IntervalRat.scale (249 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (52686302271 / 1000000000000) (52686302272 / 1000000000000), orderedInterval (21911443299 / 1000000000000) (21911443300 / 1000000000000)))) (orderedInterval (-22876180550 / 1000000000000) (-22876180493 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 4) <| besselDerivativeNearFromState (575040868112991 / 4000000000000) 4 (IntervalRat.scale (249 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (2094752154 / 1000000000000) (2094752157 / 1000000000000), orderedInterval (66505745442 / 1000000000000) (66505745445 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 4) <| besselDerivativeNearFromState (985342328769243 / 4000000000000) 4 (IntervalRat.scale (249 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (44479769804 / 1000000000000) (44479799243 / 1000000000000), orderedInterval (-24705448160 / 1000000000000) (-24705418721 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 4) <| besselDerivativeNearFromState (725798699662737 / 4000000000000) 4 (IntervalRat.scale (249 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (1303622205 / 1000000000000) (1303622208 / 1000000000000), orderedInterval (59214932333 / 1000000000000) (59214932336 / 1000000000000)))) (orderedInterval (-20717237971 / 1000000000000) (-20717223869 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate249_chunkChecks4_1 :
    compactCertificate249.chunkChecks (4 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 4) <| besselDerivativeNearFromState (1113561852794751 / 4000000000000) 4 (IntervalRat.scale (249 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (19775405501 / 1000000000000) (19775406272 / 1000000000000), orderedInterval (-43575419308 / 1000000000000) (-43575418538 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 4) <| besselDerivativeNearFromState (642915235470279 / 4000000000000) 4 (IntervalRat.scale (249 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-60508434686 / 1000000000000) (-60508434684 / 1000000000000), orderedInterval (-17119134000 / 1000000000000) (-17119133998 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 4) <| besselDerivativeNearFromState (1140864367426611 / 4000000000000) 4 (IntervalRat.scale (249 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-5473742456 / 1000000000000) (-5473742455 / 1000000000000), orderedInterval (-46916971155 / 1000000000000) (-46916971154 / 1000000000000)))) (orderedInterval (-121667524307 / 1000000000000) (-121667519786 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 4) <| besselDerivativeNearFromState (1065943481083359 / 4000000000000) 4 (IntervalRat.scale (249 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-11400759664 / 1000000000000) (-11400759663 / 1000000000000), orderedInterval (-47507234675 / 1000000000000) (-47507234674 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 4) <| besselDerivativeNearFromState (760707565362447 / 4000000000000) 4 (IntervalRat.scale (249 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (36178518684 / 1000000000000) (36178536700 / 1000000000000), orderedInterval (-45246321562 / 1000000000000) (-45246303546 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 4) <| besselDerivativeNearFromState (862561302169113 / 4000000000000) 4 (IntervalRat.scale (249 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (18362864832 / 1000000000000) (18362865247 / 1000000000000), orderedInterval (-51180049130 / 1000000000000) (-51180048715 / 1000000000000)))) (orderedInterval (22020187016 / 1000000000000) (22020196526 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 4) <| besselDerivativeNearFromState (719113687212297 / 4000000000000) 4 (IntervalRat.scale (249 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-59324290955 / 1000000000000) (-59324290937 / 1000000000000), orderedInterval (-4498761566 / 1000000000000) (-4498761548 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 4) <| besselDerivativeNearFromState (635358751182237 / 4000000000000) 4 (IntervalRat.scale (249 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (35585682939 / 1000000000000) (35585692698 / 1000000000000), orderedInterval (-52472359907 / 1000000000000) (-52472350148 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 4) <| besselDerivativeNearFromState (184151730389463 / 800000000000) 4 (IntervalRat.scale (249 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-52469598673 / 1000000000000) (-52469598457 / 1000000000000), orderedInterval (3658855511 / 1000000000000) (3658855727 / 1000000000000)))) (orderedInterval (-23964368504 / 1000000000000) (-23964366876 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate249_chunkChecks4_2 :
    compactCertificate249.chunkChecks (4 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 4) <| besselDerivativeNearFromState (509373377631861 / 4000000000000) 4 (IntervalRat.scale (249 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (44323308996 / 1000000000000) (44323333709 / 1000000000000), orderedInterval (-55262060816 / 1000000000000) (-55262036103 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 4) <| besselDerivativeNearFromState (431801453374221 / 4000000000000) 4 (IntervalRat.scale (249 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (72146944795 / 1000000000000) (72146947891 / 1000000000000), orderedInterval (-26642100420 / 1000000000000) (-26642097324 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 4) <| besselDerivativeNearFromState (270201300337263 / 4000000000000) 4 (IntervalRat.scale (249 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-68353311809 / 1000000000000) (-68353231170 / 1000000000000), orderedInterval (69442145510 / 1000000000000) (69442226149 / 1000000000000)))) (orderedInterval (-10082230601 / 1000000000000) (-10082225847 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 4) <| besselDerivativeNearFromState (145315157970321 / 4000000000000) 4 (IntervalRat.scale (249 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-73466189585 / 1000000000000) (-73466173509 / 1000000000000), orderedInterval (111134465438 / 1000000000000) (111134481514 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 4) <| besselDerivativeNearFromState (394558921713963 / 4000000000000) 4 (IntervalRat.scale (249 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-71853269475 / 1000000000000) (-71853259772 / 1000000000000), orderedInterval (36295362189 / 1000000000000) (36295371892 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 4) <| besselDerivativeNearFromState (538736475720651 / 4000000000000) 4 (IntervalRat.scale (249 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-25507931083 / 1000000000000) (-25507931082 / 1000000000000), orderedInterval (-63749890899 / 1000000000000) (-63749890898 / 1000000000000)))) (orderedInterval (3420840242 / 1000000000000) (3420840348 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 4) <| besselDerivativeNearFromState (227798699662737 / 4000000000000) 4 (IntervalRat.scale (249 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (97924573159 / 1000000000000) (97924573160 / 1000000000000), orderedInterval (39003928308 / 1000000000000) (39003928309 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 4) <| besselDerivativeNearFromState (925989067123377 / 4000000000000) 4 (IntervalRat.scale (249 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-10198833519 / 1000000000000) (-10198833471 / 1000000000000), orderedInterval (51461308667 / 1000000000000) (51461308715 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 4) <| besselDerivativeNearFromState (618517782742143 / 4000000000000) 4 (IntervalRat.scale (249 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-63876093791 / 1000000000000) (-63876093779 / 1000000000000), orderedInterval (-5867203656 / 1000000000000) (-5867203644 / 1000000000000)))) (orderedInterval (38065738199 / 1000000000000) (38065738429 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate249_chunkChecks4 :
    compactCertificate249.chunkChecks (4 : Fin 5) 0 9 = true :=
  compactCertificate249.chunkChecks_nine_of_three (4 : Fin 5) compactCertificate249_chunkChecks4_0
    compactCertificate249_chunkChecks4_1 compactCertificate249_chunkChecks4_2

theorem compactCertificate249_chunks :
    ∀ r : Fin 5, ∀ b, compactCertificate249.chunkCheck r b = true :=
  compactCertificate249.chunkChecks_all (by
    intro r
    fin_cases r
    · exact compactCertificate249_chunkChecks0
    · exact compactCertificate249_chunkChecks1
    · exact compactCertificate249_chunkChecks2
    · exact compactCertificate249_chunkChecks3
    · exact compactCertificate249_chunkChecks4)

theorem compactCertificate249_coefficient0 :
    compactCertificate249.coefficientCheck (0 : Fin 5) = true := by
  norm_num [CompactCertificate.coefficientCheck, intervalFinSumHull,
    compactCertificate249, rationalIntervalSubset, orderedInterval, Fin.sum_univ_succ]

theorem compactCertificate249_coefficient1 :
    compactCertificate249.coefficientCheck (1 : Fin 5) = true := by
  norm_num [CompactCertificate.coefficientCheck, intervalFinSumHull,
    compactCertificate249, rationalIntervalSubset, orderedInterval, Fin.sum_univ_succ]

theorem compactCertificate249_coefficient2 :
    compactCertificate249.coefficientCheck (2 : Fin 5) = true := by
  norm_num [CompactCertificate.coefficientCheck, intervalFinSumHull,
    compactCertificate249, rationalIntervalSubset, orderedInterval, Fin.sum_univ_succ]

theorem compactCertificate249_coefficient3 :
    compactCertificate249.coefficientCheck (3 : Fin 5) = true := by
  norm_num [CompactCertificate.coefficientCheck, intervalFinSumHull,
    compactCertificate249, rationalIntervalSubset, orderedInterval, Fin.sum_univ_succ]

theorem compactCertificate249_coefficient4 :
    compactCertificate249.coefficientCheck (4 : Fin 5) = true := by
  norm_num [CompactCertificate.coefficientCheck, intervalFinSumHull,
    compactCertificate249, rationalIntervalSubset, orderedInterval, Fin.sum_univ_succ]

theorem compactCertificate249_coefficients : ∀ r : Fin 5,
    compactCertificate249.coefficientCheck r = true := by
  intro r
  fin_cases r
  · exact compactCertificate249_coefficient0
  · exact compactCertificate249_coefficient1
  · exact compactCertificate249_coefficient2
  · exact compactCertificate249_coefficient3
  · exact compactCertificate249_coefficient4

theorem compactCertificate249_lower : (1 : ℚ) ≤ compactCertificate249.output.lo := by
  norm_num [CompactCertificate.output, CompactCertificate.interval,
    CompactCertificate.coefficientTargetNat, compactCertificate249, dualConstant,
    intervalTaylorSum, intervalPow, intervalSub, intervalMaxAbs, widenInterval,
    rationalErrorInterval, orderedInterval, IntervalRat.add, IntervalRat.mul, IntervalRat.scale,
    IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4]

theorem compactCertificate249_proves {t : ℝ} (ht : t ∈ compactCertificate249.interval) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t :=
  compactCertificate249.proves compactCertificate249_states compactCertificate249_chunks
    compactCertificate249_coefficients compactCertificate249_lower ht

end Erdos232
