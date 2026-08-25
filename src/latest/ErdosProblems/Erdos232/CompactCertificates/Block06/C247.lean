/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, OpenAI Codex
-/
import ErdosProblems.Erdos232.CompactBase

open LeanCert.Core
namespace Erdos232

def compactCertificate247 : CompactCertificate where
  left := 122
  right := 123
  center := 245 / 2
  grid := fun i =>
    match i.val with
    | 0 => 39
    | 1 => 29
    | 2 => 46
    | 3 => 8
    | 4 => 23
    | 5 => 61
    | 6 => 45
    | 7 => 77
    | 8 => 57
    | 9 => 87
    | 10 => 50
    | 11 => 89
    | 12 => 84
    | 13 => 60
    | 14 => 68
    | 15 => 56
    | 16 => 50
    | 17 => 72
    | 18 => 40
    | 19 => 34
    | 20 => 21
    | 21 => 11
    | 22 => 31
    | 23 => 42
    | 24 => 18
    | 25 => 73
    | _ => 48
  point := fun i =>
    match i.val with
    | 0 => 245 / 2
    | 1 => 72186356447149 / 800000000000
    | 2 => 23343584512717 / 160000000000
    | 3 => 21063798775943 / 800000000000
    | 4 => 56580326380571 / 800000000000
    | 5 => 153626592564207 / 800000000000
    | 6 => 113160652761191 / 800000000000
    | 7 => 193902707267843 / 800000000000
    | 8 => 142827856560137 / 800000000000
    | 9 => 219134661794951 / 800000000000
    | 10 => 126517455976079 / 800000000000
    | 11 => 224507445798811 / 800000000000
    | 12 => 209763978205159 / 800000000000
    | 13 => 149697472701847 / 800000000000
    | 14 => 169740979141713 / 800000000000
    | 15 => 141512332021697 / 800000000000
    | 16 => 125030436979637 / 800000000000
    | 17 => 36238693932063 / 160000000000
    | 18 => 100238134554061 / 800000000000
    | 19 => 84972976768421 / 800000000000
    | 20 => 53172143439863 / 800000000000
    | 21 => 28596155584521 / 800000000000
    | 22 => 77644125156563 / 800000000000
    | 23 => 106016414900851 / 800000000000
    | 24 => 44827856560137 / 800000000000
    | 25 => 182222748148777 / 800000000000
    | _ => 121716350820743 / 800000000000
  state := fun i =>
    match i.val with
    | 0 => (orderedInterval (-49781984869 / 1000000000000) (-49781984868 / 1000000000000), orderedInterval (-51937506711 / 1000000000000) (-51937506710 / 1000000000000))
    | 1 => (orderedInterval (7484814662 / 1000000000000) (7484814691 / 1000000000000), orderedInterval (-83703747465 / 1000000000000) (-83703747437 / 1000000000000))
    | 2 => (orderedInterval (54597408213 / 1000000000000) (54597451196 / 1000000000000), orderedInterval (-37370280315 / 1000000000000) (-37370237332 / 1000000000000))
    | 3 => (orderedInterval (142788550658 / 1000000000000) (142788554477 / 1000000000000), orderedInterval (-64250546186 / 1000000000000) (-64250542367 / 1000000000000))
    | 4 => (orderedInterval (64502379568 / 1000000000000) (64502439210 / 1000000000000), orderedInterval (-70031466523 / 1000000000000) (-70031406881 / 1000000000000))
    | 5 => (orderedInterval (-53254615056 / 1000000000000) (-53254615055 / 1000000000000), orderedInterval (-21749511813 / 1000000000000) (-21749511812 / 1000000000000))
    | 6 => (orderedInterval (-51001005100 / 1000000000000) (-51001005099 / 1000000000000), orderedInterval (-43403403772 / 1000000000000) (-43403403771 / 1000000000000))
    | 7 => (orderedInterval (-48804392531 / 1000000000000) (-48804392530 / 1000000000000), orderedInterval (-15541577186 / 1000000000000) (-15541577185 / 1000000000000))
    | 8 => (orderedInterval (-14700475156 / 1000000000000) (-14700475155 / 1000000000000), orderedInterval (-57835510205 / 1000000000000) (-57835510204 / 1000000000000))
    | 9 => (orderedInterval (-47376808853 / 1000000000000) (-47376808846 / 1000000000000), orderedInterval (-8832991724 / 1000000000000) (-8832991717 / 1000000000000))
    | 10 => (orderedInterval (60958211680 / 1000000000000) (60958213587 / 1000000000000), orderedInterval (-17787545727 / 1000000000000) (-17787543819 / 1000000000000))
    | 11 => (orderedInterval (-46186535731 / 1000000000000) (-46186533136 / 1000000000000), orderedInterval (11714307444 / 1000000000000) (11714310039 / 1000000000000))
    | 12 => (orderedInterval (-38716637335 / 1000000000000) (-38716537485 / 1000000000000), orderedInterval (30552813529 / 1000000000000) (30552913379 / 1000000000000))
    | 13 => (orderedInterval (-32402369856 / 1000000000000) (-32402362051 / 1000000000000), orderedInterval (48586663148 / 1000000000000) (48586670954 / 1000000000000))
    | 14 => (orderedInterval (-33897750346 / 1000000000000) (-33897735382 / 1000000000000), orderedInterval (43107472450 / 1000000000000) (43107487414 / 1000000000000))
    | 15 => (orderedInterval (59073586877 / 1000000000000) (59073587487 / 1000000000000), orderedInterval (-10619147316 / 1000000000000) (-10619146706 / 1000000000000))
    | 16 => (orderedInterval (-445995410 / 1000000000000) (-445995405 / 1000000000000), orderedInterval (63823026798 / 1000000000000) (63823026803 / 1000000000000))
    | 17 => (orderedInterval (46808742128 / 1000000000000) (46808742129 / 1000000000000), orderedInterval (24790891501 / 1000000000000) (24790891502 / 1000000000000))
    | 18 => (orderedInterval (28958500554 / 1000000000000) (28958500555 / 1000000000000), orderedInterval (65017316760 / 1000000000000) (65017316761 / 1000000000000))
    | 19 => (orderedInterval (14339095992 / 1000000000000) (14339095993 / 1000000000000), orderedInterval (76011889209 / 1000000000000) (76011889210 / 1000000000000))
    | 20 => (orderedInterval (-93623951837 / 1000000000000) (-93623951836 / 1000000000000), orderedInterval (-27801445098 / 1000000000000) (-27801445097 / 1000000000000))
    | 21 => (orderedInterval (-122976393528 / 1000000000000) (-122976389892 / 1000000000000), orderedInterval (53541960099 / 1000000000000) (53541963735 / 1000000000000))
    | 22 => (orderedInterval (-35219878065 / 1000000000000) (-35219878064 / 1000000000000), orderedInterval (-72749865064 / 1000000000000) (-72749865063 / 1000000000000))
    | 23 => (orderedInterval (67748021559 / 1000000000000) (67748021561 / 1000000000000), orderedInterval (14376821214 / 1000000000000) (14376821216 / 1000000000000))
    | 24 => (orderedInterval (28360198763 / 1000000000000) (28360198764 / 1000000000000), orderedInterval (102495358306 / 1000000000000) (102495358307 / 1000000000000))
    | 25 => (orderedInterval (36915346592 / 1000000000000) (36915383883 / 1000000000000), orderedInterval (-37924992911 / 1000000000000) (-37924955620 / 1000000000000))
    | _ => (orderedInterval (54709979590 / 1000000000000) (54710011808 / 1000000000000), orderedInterval (-34691992991 / 1000000000000) (-34691960773 / 1000000000000))
  chunkTarget := fun r b =>
    match r.val with
    | 0 =>
      match b.val with
      | 0 => orderedInterval (-16458253982 / 1000000000000) (-16458251449 / 1000000000000)
      | 1 => orderedInterval (4591791378 / 1000000000000) (4591793613 / 1000000000000)
      | 2 => orderedInterval (1150041248 / 1000000000000) (1150041255 / 1000000000000)
      | 3 => orderedInterval (6369100555 / 1000000000000) (6369101116 / 1000000000000)
      | 4 => orderedInterval (-2193565920 / 1000000000000) (-2193563288 / 1000000000000)
      | 5 => orderedInterval (1906173809 / 1000000000000) (1906173829 / 1000000000000)
      | 6 => orderedInterval (-8489790713 / 1000000000000) (-8489790681 / 1000000000000)
      | 7 => orderedInterval (-2122329884 / 1000000000000) (-2122329801 / 1000000000000)
      | _ => orderedInterval (-13099062791 / 1000000000000) (-13099053676 / 1000000000000)
    | 1 =>
      match b.val with
      | 0 => orderedInterval (-23772500620 / 1000000000000) (-23772497605 / 1000000000000)
      | 1 => orderedInterval (1097355092 / 1000000000000) (1097356376 / 1000000000000)
      | 2 => orderedInterval (-1088678154 / 1000000000000) (-1088678141 / 1000000000000)
      | 3 => orderedInterval (5623055221 / 1000000000000) (5623056353 / 1000000000000)
      | 4 => orderedInterval (5459744337 / 1000000000000) (5459749478 / 1000000000000)
      | 5 => orderedInterval (-3663267162 / 1000000000000) (-3663267134 / 1000000000000)
      | 6 => orderedInterval (-14854645282 / 1000000000000) (-14854645252 / 1000000000000)
      | 7 => orderedInterval (-172797917 / 1000000000000) (-172797883 / 1000000000000)
      | _ => orderedInterval (14107310235 / 1000000000000) (14107323435 / 1000000000000)
    | 2 =>
      match b.val with
      | 0 => orderedInterval (15343475007 / 1000000000000) (15343478622 / 1000000000000)
      | 1 => orderedInterval (-10025876744 / 1000000000000) (-10025875982 / 1000000000000)
      | 2 => orderedInterval (-5129580705 / 1000000000000) (-5129580683 / 1000000000000)
      | 3 => orderedInterval (-15206879425 / 1000000000000) (-15206877023 / 1000000000000)
      | 4 => orderedInterval (3388002083 / 1000000000000) (3388012373 / 1000000000000)
      | 5 => orderedInterval (-5531056189 / 1000000000000) (-5531056147 / 1000000000000)
      | 6 => orderedInterval (6472852741 / 1000000000000) (6472852769 / 1000000000000)
      | 7 => orderedInterval (5382806767 / 1000000000000) (5382806787 / 1000000000000)
      | _ => orderedInterval (26073124741 / 1000000000000) (26073144739 / 1000000000000)
    | 3 =>
      match b.val with
      | 0 => orderedInterval (24475836549 / 1000000000000) (24475840853 / 1000000000000)
      | 1 => orderedInterval (-5389219019 / 1000000000000) (-5389218558 / 1000000000000)
      | 2 => orderedInterval (655773493 / 1000000000000) (655773533 / 1000000000000)
      | 3 => orderedInterval (-34608971014 / 1000000000000) (-34608965770 / 1000000000000)
      | 4 => orderedInterval (-9860573466 / 1000000000000) (-9860552615 / 1000000000000)
      | 5 => orderedInterval (3987059072 / 1000000000000) (3987059134 / 1000000000000)
      | 6 => orderedInterval (14019704747 / 1000000000000) (14019704775 / 1000000000000)
      | 7 => orderedInterval (554711033 / 1000000000000) (554711049 / 1000000000000)
      | _ => orderedInterval (-32588503609 / 1000000000000) (-32588472243 / 1000000000000)
    | _ =>
      match b.val with
      | 0 => orderedInterval (-13663486343 / 1000000000000) (-13663481183 / 1000000000000)
      | 1 => orderedInterval (23208249509 / 1000000000000) (23208249813 / 1000000000000)
      | 2 => orderedInterval (21456704273 / 1000000000000) (21456704346 / 1000000000000)
      | 3 => orderedInterval (42725186211 / 1000000000000) (42725197923 / 1000000000000)
      | 4 => orderedInterval (-305763474 / 1000000000000) (-305720485 / 1000000000000)
      | 5 => orderedInterval (16973626378 / 1000000000000) (16973626472 / 1000000000000)
      | 6 => orderedInterval (-6019269061 / 1000000000000) (-6019269034 / 1000000000000)
      | 7 => orderedInterval (-6788445387 / 1000000000000) (-6788445371 / 1000000000000)
      | _ => orderedInterval (-59805644194 / 1000000000000) (-59805592844 / 1000000000000)
  coefficientTarget := fun i =>
    match i.val with
    | 0 => orderedInterval (-28345896300 / 1000000000000) (-28345879082 / 1000000000000)
    | 1 => orderedInterval (-17264424250 / 1000000000000) (-17264400373 / 1000000000000)
    | 2 => orderedInterval (20766868276 / 1000000000000) (20766905455 / 1000000000000)
    | 3 => orderedInterval (-38754182214 / 1000000000000) (-38754119842 / 1000000000000)
    | _ => orderedInterval (17781157912 / 1000000000000) (17781269637 / 1000000000000)

theorem compactCertificate247_stateChecks0 :
    compactCertificate247.stateChecks 0 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 39 12 (245 / 2)) (orderedInterval (-49781984869 / 1000000000000) (-49781984868 / 1000000000000), orderedInterval (-51937506711 / 1000000000000) (-51937506710 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 29 12 (72186356447149 / 800000000000)) (orderedInterval (7484814662 / 1000000000000) (7484814691 / 1000000000000), orderedInterval (-83703747465 / 1000000000000) (-83703747437 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 46 12 (23343584512717 / 160000000000)) (orderedInterval (54597408213 / 1000000000000) (54597451196 / 1000000000000), orderedInterval (-37370280315 / 1000000000000) (-37370237332 / 1000000000000))) = true
  norm_num [besselStateAtRationalPoint, besselIntervalStepZero,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, besselZeroTransition,
    besselInitial, besselGridStateAt, besselGridStateBlock00, besselGridStateBlock01,
    besselGridStateBlock02, besselGridStateBlock03, besselGridStateBlock04,
    besselGridStateBlock05, besselGridStateBlock06, besselGridStateBlock07,
    besselGridStateBlock08, besselGridStateBlock09, besselGridStateBlock10,
    besselGridStateBlock11, besselGridStateBlock12, besselGridStateBlock13,
    besselGridStateBlock14, besselGridState008, besselGridState011, besselGridState018, besselGridState021, besselGridState023, besselGridState029, besselGridState031, besselGridState034, besselGridState039, besselGridState040, besselGridState042, besselGridState045, besselGridState046, besselGridState048, besselGridState050, besselGridState056, besselGridState057, besselGridState060, besselGridState061, besselGridState068, besselGridState072, besselGridState073, besselGridState077, besselGridState084, besselGridState087, besselGridState089, besselStateSubset, linearInterval, widenInterval,
    rationalErrorInterval, rationalIntervalSubset, orderedInterval, Finset.sum_range_succ,
    IntervalRat.add, IntervalRat.mul, IntervalRat.scale, IntervalRat.singleton]

theorem compactCertificate247_stateChecks1 :
    compactCertificate247.stateChecks 3 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 8 12 (21063798775943 / 800000000000)) (orderedInterval (142788550658 / 1000000000000) (142788554477 / 1000000000000), orderedInterval (-64250546186 / 1000000000000) (-64250542367 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 23 12 (56580326380571 / 800000000000)) (orderedInterval (64502379568 / 1000000000000) (64502439210 / 1000000000000), orderedInterval (-70031466523 / 1000000000000) (-70031406881 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 61 12 (153626592564207 / 800000000000)) (orderedInterval (-53254615056 / 1000000000000) (-53254615055 / 1000000000000), orderedInterval (-21749511813 / 1000000000000) (-21749511812 / 1000000000000))) = true
  norm_num [besselStateAtRationalPoint, besselIntervalStepZero,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, besselZeroTransition,
    besselInitial, besselGridStateAt, besselGridStateBlock00, besselGridStateBlock01,
    besselGridStateBlock02, besselGridStateBlock03, besselGridStateBlock04,
    besselGridStateBlock05, besselGridStateBlock06, besselGridStateBlock07,
    besselGridStateBlock08, besselGridStateBlock09, besselGridStateBlock10,
    besselGridStateBlock11, besselGridStateBlock12, besselGridStateBlock13,
    besselGridStateBlock14, besselGridState008, besselGridState011, besselGridState018, besselGridState021, besselGridState023, besselGridState029, besselGridState031, besselGridState034, besselGridState039, besselGridState040, besselGridState042, besselGridState045, besselGridState046, besselGridState048, besselGridState050, besselGridState056, besselGridState057, besselGridState060, besselGridState061, besselGridState068, besselGridState072, besselGridState073, besselGridState077, besselGridState084, besselGridState087, besselGridState089, besselStateSubset, linearInterval, widenInterval,
    rationalErrorInterval, rationalIntervalSubset, orderedInterval, Finset.sum_range_succ,
    IntervalRat.add, IntervalRat.mul, IntervalRat.scale, IntervalRat.singleton]

theorem compactCertificate247_stateChecks2 :
    compactCertificate247.stateChecks 6 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 45 12 (113160652761191 / 800000000000)) (orderedInterval (-51001005100 / 1000000000000) (-51001005099 / 1000000000000), orderedInterval (-43403403772 / 1000000000000) (-43403403771 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 77 12 (193902707267843 / 800000000000)) (orderedInterval (-48804392531 / 1000000000000) (-48804392530 / 1000000000000), orderedInterval (-15541577186 / 1000000000000) (-15541577185 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 57 12 (142827856560137 / 800000000000)) (orderedInterval (-14700475156 / 1000000000000) (-14700475155 / 1000000000000), orderedInterval (-57835510205 / 1000000000000) (-57835510204 / 1000000000000))) = true
  norm_num [besselStateAtRationalPoint, besselIntervalStepZero,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, besselZeroTransition,
    besselInitial, besselGridStateAt, besselGridStateBlock00, besselGridStateBlock01,
    besselGridStateBlock02, besselGridStateBlock03, besselGridStateBlock04,
    besselGridStateBlock05, besselGridStateBlock06, besselGridStateBlock07,
    besselGridStateBlock08, besselGridStateBlock09, besselGridStateBlock10,
    besselGridStateBlock11, besselGridStateBlock12, besselGridStateBlock13,
    besselGridStateBlock14, besselGridState008, besselGridState011, besselGridState018, besselGridState021, besselGridState023, besselGridState029, besselGridState031, besselGridState034, besselGridState039, besselGridState040, besselGridState042, besselGridState045, besselGridState046, besselGridState048, besselGridState050, besselGridState056, besselGridState057, besselGridState060, besselGridState061, besselGridState068, besselGridState072, besselGridState073, besselGridState077, besselGridState084, besselGridState087, besselGridState089, besselStateSubset, linearInterval, widenInterval,
    rationalErrorInterval, rationalIntervalSubset, orderedInterval, Finset.sum_range_succ,
    IntervalRat.add, IntervalRat.mul, IntervalRat.scale, IntervalRat.singleton]

theorem compactCertificate247_stateChecks3 :
    compactCertificate247.stateChecks 9 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 87 12 (219134661794951 / 800000000000)) (orderedInterval (-47376808853 / 1000000000000) (-47376808846 / 1000000000000), orderedInterval (-8832991724 / 1000000000000) (-8832991717 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 50 12 (126517455976079 / 800000000000)) (orderedInterval (60958211680 / 1000000000000) (60958213587 / 1000000000000), orderedInterval (-17787545727 / 1000000000000) (-17787543819 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 89 12 (224507445798811 / 800000000000)) (orderedInterval (-46186535731 / 1000000000000) (-46186533136 / 1000000000000), orderedInterval (11714307444 / 1000000000000) (11714310039 / 1000000000000))) = true
  norm_num [besselStateAtRationalPoint, besselIntervalStepZero,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, besselZeroTransition,
    besselInitial, besselGridStateAt, besselGridStateBlock00, besselGridStateBlock01,
    besselGridStateBlock02, besselGridStateBlock03, besselGridStateBlock04,
    besselGridStateBlock05, besselGridStateBlock06, besselGridStateBlock07,
    besselGridStateBlock08, besselGridStateBlock09, besselGridStateBlock10,
    besselGridStateBlock11, besselGridStateBlock12, besselGridStateBlock13,
    besselGridStateBlock14, besselGridState008, besselGridState011, besselGridState018, besselGridState021, besselGridState023, besselGridState029, besselGridState031, besselGridState034, besselGridState039, besselGridState040, besselGridState042, besselGridState045, besselGridState046, besselGridState048, besselGridState050, besselGridState056, besselGridState057, besselGridState060, besselGridState061, besselGridState068, besselGridState072, besselGridState073, besselGridState077, besselGridState084, besselGridState087, besselGridState089, besselStateSubset, linearInterval, widenInterval,
    rationalErrorInterval, rationalIntervalSubset, orderedInterval, Finset.sum_range_succ,
    IntervalRat.add, IntervalRat.mul, IntervalRat.scale, IntervalRat.singleton]

theorem compactCertificate247_stateChecks4 :
    compactCertificate247.stateChecks 12 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 84 12 (209763978205159 / 800000000000)) (orderedInterval (-38716637335 / 1000000000000) (-38716537485 / 1000000000000), orderedInterval (30552813529 / 1000000000000) (30552913379 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 60 12 (149697472701847 / 800000000000)) (orderedInterval (-32402369856 / 1000000000000) (-32402362051 / 1000000000000), orderedInterval (48586663148 / 1000000000000) (48586670954 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 68 12 (169740979141713 / 800000000000)) (orderedInterval (-33897750346 / 1000000000000) (-33897735382 / 1000000000000), orderedInterval (43107472450 / 1000000000000) (43107487414 / 1000000000000))) = true
  norm_num [besselStateAtRationalPoint, besselIntervalStepZero,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, besselZeroTransition,
    besselInitial, besselGridStateAt, besselGridStateBlock00, besselGridStateBlock01,
    besselGridStateBlock02, besselGridStateBlock03, besselGridStateBlock04,
    besselGridStateBlock05, besselGridStateBlock06, besselGridStateBlock07,
    besselGridStateBlock08, besselGridStateBlock09, besselGridStateBlock10,
    besselGridStateBlock11, besselGridStateBlock12, besselGridStateBlock13,
    besselGridStateBlock14, besselGridState008, besselGridState011, besselGridState018, besselGridState021, besselGridState023, besselGridState029, besselGridState031, besselGridState034, besselGridState039, besselGridState040, besselGridState042, besselGridState045, besselGridState046, besselGridState048, besselGridState050, besselGridState056, besselGridState057, besselGridState060, besselGridState061, besselGridState068, besselGridState072, besselGridState073, besselGridState077, besselGridState084, besselGridState087, besselGridState089, besselStateSubset, linearInterval, widenInterval,
    rationalErrorInterval, rationalIntervalSubset, orderedInterval, Finset.sum_range_succ,
    IntervalRat.add, IntervalRat.mul, IntervalRat.scale, IntervalRat.singleton]

theorem compactCertificate247_stateChecks5 :
    compactCertificate247.stateChecks 15 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 56 12 (141512332021697 / 800000000000)) (orderedInterval (59073586877 / 1000000000000) (59073587487 / 1000000000000), orderedInterval (-10619147316 / 1000000000000) (-10619146706 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 50 12 (125030436979637 / 800000000000)) (orderedInterval (-445995410 / 1000000000000) (-445995405 / 1000000000000), orderedInterval (63823026798 / 1000000000000) (63823026803 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 72 12 (36238693932063 / 160000000000)) (orderedInterval (46808742128 / 1000000000000) (46808742129 / 1000000000000), orderedInterval (24790891501 / 1000000000000) (24790891502 / 1000000000000))) = true
  norm_num [besselStateAtRationalPoint, besselIntervalStepZero,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, besselZeroTransition,
    besselInitial, besselGridStateAt, besselGridStateBlock00, besselGridStateBlock01,
    besselGridStateBlock02, besselGridStateBlock03, besselGridStateBlock04,
    besselGridStateBlock05, besselGridStateBlock06, besselGridStateBlock07,
    besselGridStateBlock08, besselGridStateBlock09, besselGridStateBlock10,
    besselGridStateBlock11, besselGridStateBlock12, besselGridStateBlock13,
    besselGridStateBlock14, besselGridState008, besselGridState011, besselGridState018, besselGridState021, besselGridState023, besselGridState029, besselGridState031, besselGridState034, besselGridState039, besselGridState040, besselGridState042, besselGridState045, besselGridState046, besselGridState048, besselGridState050, besselGridState056, besselGridState057, besselGridState060, besselGridState061, besselGridState068, besselGridState072, besselGridState073, besselGridState077, besselGridState084, besselGridState087, besselGridState089, besselStateSubset, linearInterval, widenInterval,
    rationalErrorInterval, rationalIntervalSubset, orderedInterval, Finset.sum_range_succ,
    IntervalRat.add, IntervalRat.mul, IntervalRat.scale, IntervalRat.singleton]

theorem compactCertificate247_stateChecks6 :
    compactCertificate247.stateChecks 18 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 40 12 (100238134554061 / 800000000000)) (orderedInterval (28958500554 / 1000000000000) (28958500555 / 1000000000000), orderedInterval (65017316760 / 1000000000000) (65017316761 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 34 12 (84972976768421 / 800000000000)) (orderedInterval (14339095992 / 1000000000000) (14339095993 / 1000000000000), orderedInterval (76011889209 / 1000000000000) (76011889210 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 21 12 (53172143439863 / 800000000000)) (orderedInterval (-93623951837 / 1000000000000) (-93623951836 / 1000000000000), orderedInterval (-27801445098 / 1000000000000) (-27801445097 / 1000000000000))) = true
  norm_num [besselStateAtRationalPoint, besselIntervalStepZero,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, besselZeroTransition,
    besselInitial, besselGridStateAt, besselGridStateBlock00, besselGridStateBlock01,
    besselGridStateBlock02, besselGridStateBlock03, besselGridStateBlock04,
    besselGridStateBlock05, besselGridStateBlock06, besselGridStateBlock07,
    besselGridStateBlock08, besselGridStateBlock09, besselGridStateBlock10,
    besselGridStateBlock11, besselGridStateBlock12, besselGridStateBlock13,
    besselGridStateBlock14, besselGridState008, besselGridState011, besselGridState018, besselGridState021, besselGridState023, besselGridState029, besselGridState031, besselGridState034, besselGridState039, besselGridState040, besselGridState042, besselGridState045, besselGridState046, besselGridState048, besselGridState050, besselGridState056, besselGridState057, besselGridState060, besselGridState061, besselGridState068, besselGridState072, besselGridState073, besselGridState077, besselGridState084, besselGridState087, besselGridState089, besselStateSubset, linearInterval, widenInterval,
    rationalErrorInterval, rationalIntervalSubset, orderedInterval, Finset.sum_range_succ,
    IntervalRat.add, IntervalRat.mul, IntervalRat.scale, IntervalRat.singleton]

theorem compactCertificate247_stateChecks7 :
    compactCertificate247.stateChecks 21 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 11 12 (28596155584521 / 800000000000)) (orderedInterval (-122976393528 / 1000000000000) (-122976389892 / 1000000000000), orderedInterval (53541960099 / 1000000000000) (53541963735 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 31 12 (77644125156563 / 800000000000)) (orderedInterval (-35219878065 / 1000000000000) (-35219878064 / 1000000000000), orderedInterval (-72749865064 / 1000000000000) (-72749865063 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 42 12 (106016414900851 / 800000000000)) (orderedInterval (67748021559 / 1000000000000) (67748021561 / 1000000000000), orderedInterval (14376821214 / 1000000000000) (14376821216 / 1000000000000))) = true
  norm_num [besselStateAtRationalPoint, besselIntervalStepZero,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, besselZeroTransition,
    besselInitial, besselGridStateAt, besselGridStateBlock00, besselGridStateBlock01,
    besselGridStateBlock02, besselGridStateBlock03, besselGridStateBlock04,
    besselGridStateBlock05, besselGridStateBlock06, besselGridStateBlock07,
    besselGridStateBlock08, besselGridStateBlock09, besselGridStateBlock10,
    besselGridStateBlock11, besselGridStateBlock12, besselGridStateBlock13,
    besselGridStateBlock14, besselGridState008, besselGridState011, besselGridState018, besselGridState021, besselGridState023, besselGridState029, besselGridState031, besselGridState034, besselGridState039, besselGridState040, besselGridState042, besselGridState045, besselGridState046, besselGridState048, besselGridState050, besselGridState056, besselGridState057, besselGridState060, besselGridState061, besselGridState068, besselGridState072, besselGridState073, besselGridState077, besselGridState084, besselGridState087, besselGridState089, besselStateSubset, linearInterval, widenInterval,
    rationalErrorInterval, rationalIntervalSubset, orderedInterval, Finset.sum_range_succ,
    IntervalRat.add, IntervalRat.mul, IntervalRat.scale, IntervalRat.singleton]

theorem compactCertificate247_stateChecks8 :
    compactCertificate247.stateChecks 24 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 18 12 (44827856560137 / 800000000000)) (orderedInterval (28360198763 / 1000000000000) (28360198764 / 1000000000000), orderedInterval (102495358306 / 1000000000000) (102495358307 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 73 12 (182222748148777 / 800000000000)) (orderedInterval (36915346592 / 1000000000000) (36915383883 / 1000000000000), orderedInterval (-37924992911 / 1000000000000) (-37924955620 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 48 12 (121716350820743 / 800000000000)) (orderedInterval (54709979590 / 1000000000000) (54710011808 / 1000000000000), orderedInterval (-34691992991 / 1000000000000) (-34691960773 / 1000000000000))) = true
  norm_num [besselStateAtRationalPoint, besselIntervalStepZero,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, besselZeroTransition,
    besselInitial, besselGridStateAt, besselGridStateBlock00, besselGridStateBlock01,
    besselGridStateBlock02, besselGridStateBlock03, besselGridStateBlock04,
    besselGridStateBlock05, besselGridStateBlock06, besselGridStateBlock07,
    besselGridStateBlock08, besselGridStateBlock09, besselGridStateBlock10,
    besselGridStateBlock11, besselGridStateBlock12, besselGridStateBlock13,
    besselGridStateBlock14, besselGridState008, besselGridState011, besselGridState018, besselGridState021, besselGridState023, besselGridState029, besselGridState031, besselGridState034, besselGridState039, besselGridState040, besselGridState042, besselGridState045, besselGridState046, besselGridState048, besselGridState050, besselGridState056, besselGridState057, besselGridState060, besselGridState061, besselGridState068, besselGridState072, besselGridState073, besselGridState077, besselGridState084, besselGridState087, besselGridState089, besselStateSubset, linearInterval, widenInterval,
    rationalErrorInterval, rationalIntervalSubset, orderedInterval, Finset.sum_range_succ,
    IntervalRat.add, IntervalRat.mul, IntervalRat.scale, IntervalRat.singleton]

theorem compactCertificate247_states : ∀ j,
    BesselStateValid (compactCertificate247.point j) (compactCertificate247.state j) :=
  compactCertificate247.statesValid_of_checks3 compactCertificate247_stateChecks0
    compactCertificate247_stateChecks1 compactCertificate247_stateChecks2
    compactCertificate247_stateChecks3 compactCertificate247_stateChecks4
    compactCertificate247_stateChecks5 compactCertificate247_stateChecks6
    compactCertificate247_stateChecks7 compactCertificate247_stateChecks8

theorem compactCertificate247_chunkChecks0_0 :
    compactCertificate247.chunkChecks (0 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 0) <| besselDerivativeNearFromState (245 / 2) 0 (IntervalRat.scale (245 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-49781984869 / 1000000000000) (-49781984868 / 1000000000000), orderedInterval (-51937506711 / 1000000000000) (-51937506710 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 0) <| besselDerivativeNearFromState (72186356447149 / 800000000000) 0 (IntervalRat.scale (245 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (7484814662 / 1000000000000) (7484814691 / 1000000000000), orderedInterval (-83703747465 / 1000000000000) (-83703747437 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 0) <| besselDerivativeNearFromState (23343584512717 / 160000000000) 0 (IntervalRat.scale (245 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (54597408213 / 1000000000000) (54597451196 / 1000000000000), orderedInterval (-37370280315 / 1000000000000) (-37370237332 / 1000000000000)))) (orderedInterval (-16458253982 / 1000000000000) (-16458251449 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 0) <| besselDerivativeNearFromState (21063798775943 / 800000000000) 0 (IntervalRat.scale (245 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (142788550658 / 1000000000000) (142788554477 / 1000000000000), orderedInterval (-64250546186 / 1000000000000) (-64250542367 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 0) <| besselDerivativeNearFromState (56580326380571 / 800000000000) 0 (IntervalRat.scale (245 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (64502379568 / 1000000000000) (64502439210 / 1000000000000), orderedInterval (-70031466523 / 1000000000000) (-70031406881 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 0) <| besselDerivativeNearFromState (153626592564207 / 800000000000) 0 (IntervalRat.scale (245 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-53254615056 / 1000000000000) (-53254615055 / 1000000000000), orderedInterval (-21749511813 / 1000000000000) (-21749511812 / 1000000000000)))) (orderedInterval (4591791378 / 1000000000000) (4591793613 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 0) <| besselDerivativeNearFromState (113160652761191 / 800000000000) 0 (IntervalRat.scale (245 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-51001005100 / 1000000000000) (-51001005099 / 1000000000000), orderedInterval (-43403403772 / 1000000000000) (-43403403771 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 0) <| besselDerivativeNearFromState (193902707267843 / 800000000000) 0 (IntervalRat.scale (245 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-48804392531 / 1000000000000) (-48804392530 / 1000000000000), orderedInterval (-15541577186 / 1000000000000) (-15541577185 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 0) <| besselDerivativeNearFromState (142827856560137 / 800000000000) 0 (IntervalRat.scale (245 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-14700475156 / 1000000000000) (-14700475155 / 1000000000000), orderedInterval (-57835510205 / 1000000000000) (-57835510204 / 1000000000000)))) (orderedInterval (1150041248 / 1000000000000) (1150041255 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate247_chunkChecks0_1 :
    compactCertificate247.chunkChecks (0 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 0) <| besselDerivativeNearFromState (219134661794951 / 800000000000) 0 (IntervalRat.scale (245 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-47376808853 / 1000000000000) (-47376808846 / 1000000000000), orderedInterval (-8832991724 / 1000000000000) (-8832991717 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 0) <| besselDerivativeNearFromState (126517455976079 / 800000000000) 0 (IntervalRat.scale (245 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (60958211680 / 1000000000000) (60958213587 / 1000000000000), orderedInterval (-17787545727 / 1000000000000) (-17787543819 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 0) <| besselDerivativeNearFromState (224507445798811 / 800000000000) 0 (IntervalRat.scale (245 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-46186535731 / 1000000000000) (-46186533136 / 1000000000000), orderedInterval (11714307444 / 1000000000000) (11714310039 / 1000000000000)))) (orderedInterval (6369100555 / 1000000000000) (6369101116 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 0) <| besselDerivativeNearFromState (209763978205159 / 800000000000) 0 (IntervalRat.scale (245 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-38716637335 / 1000000000000) (-38716537485 / 1000000000000), orderedInterval (30552813529 / 1000000000000) (30552913379 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 0) <| besselDerivativeNearFromState (149697472701847 / 800000000000) 0 (IntervalRat.scale (245 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-32402369856 / 1000000000000) (-32402362051 / 1000000000000), orderedInterval (48586663148 / 1000000000000) (48586670954 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 0) <| besselDerivativeNearFromState (169740979141713 / 800000000000) 0 (IntervalRat.scale (245 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-33897750346 / 1000000000000) (-33897735382 / 1000000000000), orderedInterval (43107472450 / 1000000000000) (43107487414 / 1000000000000)))) (orderedInterval (-2193565920 / 1000000000000) (-2193563288 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 0) <| besselDerivativeNearFromState (141512332021697 / 800000000000) 0 (IntervalRat.scale (245 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (59073586877 / 1000000000000) (59073587487 / 1000000000000), orderedInterval (-10619147316 / 1000000000000) (-10619146706 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 0) <| besselDerivativeNearFromState (125030436979637 / 800000000000) 0 (IntervalRat.scale (245 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-445995410 / 1000000000000) (-445995405 / 1000000000000), orderedInterval (63823026798 / 1000000000000) (63823026803 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 0) <| besselDerivativeNearFromState (36238693932063 / 160000000000) 0 (IntervalRat.scale (245 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (46808742128 / 1000000000000) (46808742129 / 1000000000000), orderedInterval (24790891501 / 1000000000000) (24790891502 / 1000000000000)))) (orderedInterval (1906173809 / 1000000000000) (1906173829 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate247_chunkChecks0_2 :
    compactCertificate247.chunkChecks (0 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 0) <| besselDerivativeNearFromState (100238134554061 / 800000000000) 0 (IntervalRat.scale (245 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (28958500554 / 1000000000000) (28958500555 / 1000000000000), orderedInterval (65017316760 / 1000000000000) (65017316761 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 0) <| besselDerivativeNearFromState (84972976768421 / 800000000000) 0 (IntervalRat.scale (245 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (14339095992 / 1000000000000) (14339095993 / 1000000000000), orderedInterval (76011889209 / 1000000000000) (76011889210 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 0) <| besselDerivativeNearFromState (53172143439863 / 800000000000) 0 (IntervalRat.scale (245 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-93623951837 / 1000000000000) (-93623951836 / 1000000000000), orderedInterval (-27801445098 / 1000000000000) (-27801445097 / 1000000000000)))) (orderedInterval (-8489790713 / 1000000000000) (-8489790681 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 0) <| besselDerivativeNearFromState (28596155584521 / 800000000000) 0 (IntervalRat.scale (245 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-122976393528 / 1000000000000) (-122976389892 / 1000000000000), orderedInterval (53541960099 / 1000000000000) (53541963735 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 0) <| besselDerivativeNearFromState (77644125156563 / 800000000000) 0 (IntervalRat.scale (245 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-35219878065 / 1000000000000) (-35219878064 / 1000000000000), orderedInterval (-72749865064 / 1000000000000) (-72749865063 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 0) <| besselDerivativeNearFromState (106016414900851 / 800000000000) 0 (IntervalRat.scale (245 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (67748021559 / 1000000000000) (67748021561 / 1000000000000), orderedInterval (14376821214 / 1000000000000) (14376821216 / 1000000000000)))) (orderedInterval (-2122329884 / 1000000000000) (-2122329801 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 0) <| besselDerivativeNearFromState (44827856560137 / 800000000000) 0 (IntervalRat.scale (245 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (28360198763 / 1000000000000) (28360198764 / 1000000000000), orderedInterval (102495358306 / 1000000000000) (102495358307 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 0) <| besselDerivativeNearFromState (182222748148777 / 800000000000) 0 (IntervalRat.scale (245 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (36915346592 / 1000000000000) (36915383883 / 1000000000000), orderedInterval (-37924992911 / 1000000000000) (-37924955620 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 0) <| besselDerivativeNearFromState (121716350820743 / 800000000000) 0 (IntervalRat.scale (245 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (54709979590 / 1000000000000) (54710011808 / 1000000000000), orderedInterval (-34691992991 / 1000000000000) (-34691960773 / 1000000000000)))) (orderedInterval (-13099062791 / 1000000000000) (-13099053676 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate247_chunkChecks0 :
    compactCertificate247.chunkChecks (0 : Fin 5) 0 9 = true :=
  compactCertificate247.chunkChecks_nine_of_three (0 : Fin 5) compactCertificate247_chunkChecks0_0
    compactCertificate247_chunkChecks0_1 compactCertificate247_chunkChecks0_2

theorem compactCertificate247_chunkChecks1_0 :
    compactCertificate247.chunkChecks (1 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 1) <| besselDerivativeNearFromState (245 / 2) 1 (IntervalRat.scale (245 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-49781984869 / 1000000000000) (-49781984868 / 1000000000000), orderedInterval (-51937506711 / 1000000000000) (-51937506710 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 1) <| besselDerivativeNearFromState (72186356447149 / 800000000000) 1 (IntervalRat.scale (245 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (7484814662 / 1000000000000) (7484814691 / 1000000000000), orderedInterval (-83703747465 / 1000000000000) (-83703747437 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 1) <| besselDerivativeNearFromState (23343584512717 / 160000000000) 1 (IntervalRat.scale (245 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (54597408213 / 1000000000000) (54597451196 / 1000000000000), orderedInterval (-37370280315 / 1000000000000) (-37370237332 / 1000000000000)))) (orderedInterval (-23772500620 / 1000000000000) (-23772497605 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 1) <| besselDerivativeNearFromState (21063798775943 / 800000000000) 1 (IntervalRat.scale (245 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (142788550658 / 1000000000000) (142788554477 / 1000000000000), orderedInterval (-64250546186 / 1000000000000) (-64250542367 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 1) <| besselDerivativeNearFromState (56580326380571 / 800000000000) 1 (IntervalRat.scale (245 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (64502379568 / 1000000000000) (64502439210 / 1000000000000), orderedInterval (-70031466523 / 1000000000000) (-70031406881 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 1) <| besselDerivativeNearFromState (153626592564207 / 800000000000) 1 (IntervalRat.scale (245 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-53254615056 / 1000000000000) (-53254615055 / 1000000000000), orderedInterval (-21749511813 / 1000000000000) (-21749511812 / 1000000000000)))) (orderedInterval (1097355092 / 1000000000000) (1097356376 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 1) <| besselDerivativeNearFromState (113160652761191 / 800000000000) 1 (IntervalRat.scale (245 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-51001005100 / 1000000000000) (-51001005099 / 1000000000000), orderedInterval (-43403403772 / 1000000000000) (-43403403771 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 1) <| besselDerivativeNearFromState (193902707267843 / 800000000000) 1 (IntervalRat.scale (245 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-48804392531 / 1000000000000) (-48804392530 / 1000000000000), orderedInterval (-15541577186 / 1000000000000) (-15541577185 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 1) <| besselDerivativeNearFromState (142827856560137 / 800000000000) 1 (IntervalRat.scale (245 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-14700475156 / 1000000000000) (-14700475155 / 1000000000000), orderedInterval (-57835510205 / 1000000000000) (-57835510204 / 1000000000000)))) (orderedInterval (-1088678154 / 1000000000000) (-1088678141 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate247_chunkChecks1_1 :
    compactCertificate247.chunkChecks (1 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 1) <| besselDerivativeNearFromState (219134661794951 / 800000000000) 1 (IntervalRat.scale (245 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-47376808853 / 1000000000000) (-47376808846 / 1000000000000), orderedInterval (-8832991724 / 1000000000000) (-8832991717 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 1) <| besselDerivativeNearFromState (126517455976079 / 800000000000) 1 (IntervalRat.scale (245 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (60958211680 / 1000000000000) (60958213587 / 1000000000000), orderedInterval (-17787545727 / 1000000000000) (-17787543819 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 1) <| besselDerivativeNearFromState (224507445798811 / 800000000000) 1 (IntervalRat.scale (245 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-46186535731 / 1000000000000) (-46186533136 / 1000000000000), orderedInterval (11714307444 / 1000000000000) (11714310039 / 1000000000000)))) (orderedInterval (5623055221 / 1000000000000) (5623056353 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 1) <| besselDerivativeNearFromState (209763978205159 / 800000000000) 1 (IntervalRat.scale (245 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-38716637335 / 1000000000000) (-38716537485 / 1000000000000), orderedInterval (30552813529 / 1000000000000) (30552913379 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 1) <| besselDerivativeNearFromState (149697472701847 / 800000000000) 1 (IntervalRat.scale (245 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-32402369856 / 1000000000000) (-32402362051 / 1000000000000), orderedInterval (48586663148 / 1000000000000) (48586670954 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 1) <| besselDerivativeNearFromState (169740979141713 / 800000000000) 1 (IntervalRat.scale (245 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-33897750346 / 1000000000000) (-33897735382 / 1000000000000), orderedInterval (43107472450 / 1000000000000) (43107487414 / 1000000000000)))) (orderedInterval (5459744337 / 1000000000000) (5459749478 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 1) <| besselDerivativeNearFromState (141512332021697 / 800000000000) 1 (IntervalRat.scale (245 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (59073586877 / 1000000000000) (59073587487 / 1000000000000), orderedInterval (-10619147316 / 1000000000000) (-10619146706 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 1) <| besselDerivativeNearFromState (125030436979637 / 800000000000) 1 (IntervalRat.scale (245 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-445995410 / 1000000000000) (-445995405 / 1000000000000), orderedInterval (63823026798 / 1000000000000) (63823026803 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 1) <| besselDerivativeNearFromState (36238693932063 / 160000000000) 1 (IntervalRat.scale (245 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (46808742128 / 1000000000000) (46808742129 / 1000000000000), orderedInterval (24790891501 / 1000000000000) (24790891502 / 1000000000000)))) (orderedInterval (-3663267162 / 1000000000000) (-3663267134 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate247_chunkChecks1_2 :
    compactCertificate247.chunkChecks (1 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 1) <| besselDerivativeNearFromState (100238134554061 / 800000000000) 1 (IntervalRat.scale (245 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (28958500554 / 1000000000000) (28958500555 / 1000000000000), orderedInterval (65017316760 / 1000000000000) (65017316761 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 1) <| besselDerivativeNearFromState (84972976768421 / 800000000000) 1 (IntervalRat.scale (245 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (14339095992 / 1000000000000) (14339095993 / 1000000000000), orderedInterval (76011889209 / 1000000000000) (76011889210 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 1) <| besselDerivativeNearFromState (53172143439863 / 800000000000) 1 (IntervalRat.scale (245 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-93623951837 / 1000000000000) (-93623951836 / 1000000000000), orderedInterval (-27801445098 / 1000000000000) (-27801445097 / 1000000000000)))) (orderedInterval (-14854645282 / 1000000000000) (-14854645252 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 1) <| besselDerivativeNearFromState (28596155584521 / 800000000000) 1 (IntervalRat.scale (245 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-122976393528 / 1000000000000) (-122976389892 / 1000000000000), orderedInterval (53541960099 / 1000000000000) (53541963735 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 1) <| besselDerivativeNearFromState (77644125156563 / 800000000000) 1 (IntervalRat.scale (245 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-35219878065 / 1000000000000) (-35219878064 / 1000000000000), orderedInterval (-72749865064 / 1000000000000) (-72749865063 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 1) <| besselDerivativeNearFromState (106016414900851 / 800000000000) 1 (IntervalRat.scale (245 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (67748021559 / 1000000000000) (67748021561 / 1000000000000), orderedInterval (14376821214 / 1000000000000) (14376821216 / 1000000000000)))) (orderedInterval (-172797917 / 1000000000000) (-172797883 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 1) <| besselDerivativeNearFromState (44827856560137 / 800000000000) 1 (IntervalRat.scale (245 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (28360198763 / 1000000000000) (28360198764 / 1000000000000), orderedInterval (102495358306 / 1000000000000) (102495358307 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 1) <| besselDerivativeNearFromState (182222748148777 / 800000000000) 1 (IntervalRat.scale (245 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (36915346592 / 1000000000000) (36915383883 / 1000000000000), orderedInterval (-37924992911 / 1000000000000) (-37924955620 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 1) <| besselDerivativeNearFromState (121716350820743 / 800000000000) 1 (IntervalRat.scale (245 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (54709979590 / 1000000000000) (54710011808 / 1000000000000), orderedInterval (-34691992991 / 1000000000000) (-34691960773 / 1000000000000)))) (orderedInterval (14107310235 / 1000000000000) (14107323435 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate247_chunkChecks1 :
    compactCertificate247.chunkChecks (1 : Fin 5) 0 9 = true :=
  compactCertificate247.chunkChecks_nine_of_three (1 : Fin 5) compactCertificate247_chunkChecks1_0
    compactCertificate247_chunkChecks1_1 compactCertificate247_chunkChecks1_2

theorem compactCertificate247_chunkChecks2_0 :
    compactCertificate247.chunkChecks (2 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 2) <| besselDerivativeNearFromState (245 / 2) 2 (IntervalRat.scale (245 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-49781984869 / 1000000000000) (-49781984868 / 1000000000000), orderedInterval (-51937506711 / 1000000000000) (-51937506710 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 2) <| besselDerivativeNearFromState (72186356447149 / 800000000000) 2 (IntervalRat.scale (245 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (7484814662 / 1000000000000) (7484814691 / 1000000000000), orderedInterval (-83703747465 / 1000000000000) (-83703747437 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 2) <| besselDerivativeNearFromState (23343584512717 / 160000000000) 2 (IntervalRat.scale (245 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (54597408213 / 1000000000000) (54597451196 / 1000000000000), orderedInterval (-37370280315 / 1000000000000) (-37370237332 / 1000000000000)))) (orderedInterval (15343475007 / 1000000000000) (15343478622 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 2) <| besselDerivativeNearFromState (21063798775943 / 800000000000) 2 (IntervalRat.scale (245 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (142788550658 / 1000000000000) (142788554477 / 1000000000000), orderedInterval (-64250546186 / 1000000000000) (-64250542367 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 2) <| besselDerivativeNearFromState (56580326380571 / 800000000000) 2 (IntervalRat.scale (245 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (64502379568 / 1000000000000) (64502439210 / 1000000000000), orderedInterval (-70031466523 / 1000000000000) (-70031406881 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 2) <| besselDerivativeNearFromState (153626592564207 / 800000000000) 2 (IntervalRat.scale (245 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-53254615056 / 1000000000000) (-53254615055 / 1000000000000), orderedInterval (-21749511813 / 1000000000000) (-21749511812 / 1000000000000)))) (orderedInterval (-10025876744 / 1000000000000) (-10025875982 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 2) <| besselDerivativeNearFromState (113160652761191 / 800000000000) 2 (IntervalRat.scale (245 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-51001005100 / 1000000000000) (-51001005099 / 1000000000000), orderedInterval (-43403403772 / 1000000000000) (-43403403771 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 2) <| besselDerivativeNearFromState (193902707267843 / 800000000000) 2 (IntervalRat.scale (245 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-48804392531 / 1000000000000) (-48804392530 / 1000000000000), orderedInterval (-15541577186 / 1000000000000) (-15541577185 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 2) <| besselDerivativeNearFromState (142827856560137 / 800000000000) 2 (IntervalRat.scale (245 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-14700475156 / 1000000000000) (-14700475155 / 1000000000000), orderedInterval (-57835510205 / 1000000000000) (-57835510204 / 1000000000000)))) (orderedInterval (-5129580705 / 1000000000000) (-5129580683 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate247_chunkChecks2_1 :
    compactCertificate247.chunkChecks (2 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 2) <| besselDerivativeNearFromState (219134661794951 / 800000000000) 2 (IntervalRat.scale (245 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-47376808853 / 1000000000000) (-47376808846 / 1000000000000), orderedInterval (-8832991724 / 1000000000000) (-8832991717 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 2) <| besselDerivativeNearFromState (126517455976079 / 800000000000) 2 (IntervalRat.scale (245 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (60958211680 / 1000000000000) (60958213587 / 1000000000000), orderedInterval (-17787545727 / 1000000000000) (-17787543819 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 2) <| besselDerivativeNearFromState (224507445798811 / 800000000000) 2 (IntervalRat.scale (245 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-46186535731 / 1000000000000) (-46186533136 / 1000000000000), orderedInterval (11714307444 / 1000000000000) (11714310039 / 1000000000000)))) (orderedInterval (-15206879425 / 1000000000000) (-15206877023 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 2) <| besselDerivativeNearFromState (209763978205159 / 800000000000) 2 (IntervalRat.scale (245 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-38716637335 / 1000000000000) (-38716537485 / 1000000000000), orderedInterval (30552813529 / 1000000000000) (30552913379 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 2) <| besselDerivativeNearFromState (149697472701847 / 800000000000) 2 (IntervalRat.scale (245 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-32402369856 / 1000000000000) (-32402362051 / 1000000000000), orderedInterval (48586663148 / 1000000000000) (48586670954 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 2) <| besselDerivativeNearFromState (169740979141713 / 800000000000) 2 (IntervalRat.scale (245 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-33897750346 / 1000000000000) (-33897735382 / 1000000000000), orderedInterval (43107472450 / 1000000000000) (43107487414 / 1000000000000)))) (orderedInterval (3388002083 / 1000000000000) (3388012373 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 2) <| besselDerivativeNearFromState (141512332021697 / 800000000000) 2 (IntervalRat.scale (245 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (59073586877 / 1000000000000) (59073587487 / 1000000000000), orderedInterval (-10619147316 / 1000000000000) (-10619146706 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 2) <| besselDerivativeNearFromState (125030436979637 / 800000000000) 2 (IntervalRat.scale (245 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-445995410 / 1000000000000) (-445995405 / 1000000000000), orderedInterval (63823026798 / 1000000000000) (63823026803 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 2) <| besselDerivativeNearFromState (36238693932063 / 160000000000) 2 (IntervalRat.scale (245 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (46808742128 / 1000000000000) (46808742129 / 1000000000000), orderedInterval (24790891501 / 1000000000000) (24790891502 / 1000000000000)))) (orderedInterval (-5531056189 / 1000000000000) (-5531056147 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate247_chunkChecks2_2 :
    compactCertificate247.chunkChecks (2 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 2) <| besselDerivativeNearFromState (100238134554061 / 800000000000) 2 (IntervalRat.scale (245 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (28958500554 / 1000000000000) (28958500555 / 1000000000000), orderedInterval (65017316760 / 1000000000000) (65017316761 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 2) <| besselDerivativeNearFromState (84972976768421 / 800000000000) 2 (IntervalRat.scale (245 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (14339095992 / 1000000000000) (14339095993 / 1000000000000), orderedInterval (76011889209 / 1000000000000) (76011889210 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 2) <| besselDerivativeNearFromState (53172143439863 / 800000000000) 2 (IntervalRat.scale (245 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-93623951837 / 1000000000000) (-93623951836 / 1000000000000), orderedInterval (-27801445098 / 1000000000000) (-27801445097 / 1000000000000)))) (orderedInterval (6472852741 / 1000000000000) (6472852769 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 2) <| besselDerivativeNearFromState (28596155584521 / 800000000000) 2 (IntervalRat.scale (245 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-122976393528 / 1000000000000) (-122976389892 / 1000000000000), orderedInterval (53541960099 / 1000000000000) (53541963735 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 2) <| besselDerivativeNearFromState (77644125156563 / 800000000000) 2 (IntervalRat.scale (245 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-35219878065 / 1000000000000) (-35219878064 / 1000000000000), orderedInterval (-72749865064 / 1000000000000) (-72749865063 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 2) <| besselDerivativeNearFromState (106016414900851 / 800000000000) 2 (IntervalRat.scale (245 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (67748021559 / 1000000000000) (67748021561 / 1000000000000), orderedInterval (14376821214 / 1000000000000) (14376821216 / 1000000000000)))) (orderedInterval (5382806767 / 1000000000000) (5382806787 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 2) <| besselDerivativeNearFromState (44827856560137 / 800000000000) 2 (IntervalRat.scale (245 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (28360198763 / 1000000000000) (28360198764 / 1000000000000), orderedInterval (102495358306 / 1000000000000) (102495358307 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 2) <| besselDerivativeNearFromState (182222748148777 / 800000000000) 2 (IntervalRat.scale (245 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (36915346592 / 1000000000000) (36915383883 / 1000000000000), orderedInterval (-37924992911 / 1000000000000) (-37924955620 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 2) <| besselDerivativeNearFromState (121716350820743 / 800000000000) 2 (IntervalRat.scale (245 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (54709979590 / 1000000000000) (54710011808 / 1000000000000), orderedInterval (-34691992991 / 1000000000000) (-34691960773 / 1000000000000)))) (orderedInterval (26073124741 / 1000000000000) (26073144739 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate247_chunkChecks2 :
    compactCertificate247.chunkChecks (2 : Fin 5) 0 9 = true :=
  compactCertificate247.chunkChecks_nine_of_three (2 : Fin 5) compactCertificate247_chunkChecks2_0
    compactCertificate247_chunkChecks2_1 compactCertificate247_chunkChecks2_2

theorem compactCertificate247_chunkChecks3_0 :
    compactCertificate247.chunkChecks (3 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 3) <| besselDerivativeNearFromState (245 / 2) 3 (IntervalRat.scale (245 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-49781984869 / 1000000000000) (-49781984868 / 1000000000000), orderedInterval (-51937506711 / 1000000000000) (-51937506710 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 3) <| besselDerivativeNearFromState (72186356447149 / 800000000000) 3 (IntervalRat.scale (245 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (7484814662 / 1000000000000) (7484814691 / 1000000000000), orderedInterval (-83703747465 / 1000000000000) (-83703747437 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 3) <| besselDerivativeNearFromState (23343584512717 / 160000000000) 3 (IntervalRat.scale (245 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (54597408213 / 1000000000000) (54597451196 / 1000000000000), orderedInterval (-37370280315 / 1000000000000) (-37370237332 / 1000000000000)))) (orderedInterval (24475836549 / 1000000000000) (24475840853 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 3) <| besselDerivativeNearFromState (21063798775943 / 800000000000) 3 (IntervalRat.scale (245 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (142788550658 / 1000000000000) (142788554477 / 1000000000000), orderedInterval (-64250546186 / 1000000000000) (-64250542367 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 3) <| besselDerivativeNearFromState (56580326380571 / 800000000000) 3 (IntervalRat.scale (245 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (64502379568 / 1000000000000) (64502439210 / 1000000000000), orderedInterval (-70031466523 / 1000000000000) (-70031406881 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 3) <| besselDerivativeNearFromState (153626592564207 / 800000000000) 3 (IntervalRat.scale (245 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-53254615056 / 1000000000000) (-53254615055 / 1000000000000), orderedInterval (-21749511813 / 1000000000000) (-21749511812 / 1000000000000)))) (orderedInterval (-5389219019 / 1000000000000) (-5389218558 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 3) <| besselDerivativeNearFromState (113160652761191 / 800000000000) 3 (IntervalRat.scale (245 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-51001005100 / 1000000000000) (-51001005099 / 1000000000000), orderedInterval (-43403403772 / 1000000000000) (-43403403771 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 3) <| besselDerivativeNearFromState (193902707267843 / 800000000000) 3 (IntervalRat.scale (245 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-48804392531 / 1000000000000) (-48804392530 / 1000000000000), orderedInterval (-15541577186 / 1000000000000) (-15541577185 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 3) <| besselDerivativeNearFromState (142827856560137 / 800000000000) 3 (IntervalRat.scale (245 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-14700475156 / 1000000000000) (-14700475155 / 1000000000000), orderedInterval (-57835510205 / 1000000000000) (-57835510204 / 1000000000000)))) (orderedInterval (655773493 / 1000000000000) (655773533 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate247_chunkChecks3_1 :
    compactCertificate247.chunkChecks (3 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 3) <| besselDerivativeNearFromState (219134661794951 / 800000000000) 3 (IntervalRat.scale (245 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-47376808853 / 1000000000000) (-47376808846 / 1000000000000), orderedInterval (-8832991724 / 1000000000000) (-8832991717 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 3) <| besselDerivativeNearFromState (126517455976079 / 800000000000) 3 (IntervalRat.scale (245 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (60958211680 / 1000000000000) (60958213587 / 1000000000000), orderedInterval (-17787545727 / 1000000000000) (-17787543819 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 3) <| besselDerivativeNearFromState (224507445798811 / 800000000000) 3 (IntervalRat.scale (245 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-46186535731 / 1000000000000) (-46186533136 / 1000000000000), orderedInterval (11714307444 / 1000000000000) (11714310039 / 1000000000000)))) (orderedInterval (-34608971014 / 1000000000000) (-34608965770 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 3) <| besselDerivativeNearFromState (209763978205159 / 800000000000) 3 (IntervalRat.scale (245 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-38716637335 / 1000000000000) (-38716537485 / 1000000000000), orderedInterval (30552813529 / 1000000000000) (30552913379 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 3) <| besselDerivativeNearFromState (149697472701847 / 800000000000) 3 (IntervalRat.scale (245 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-32402369856 / 1000000000000) (-32402362051 / 1000000000000), orderedInterval (48586663148 / 1000000000000) (48586670954 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 3) <| besselDerivativeNearFromState (169740979141713 / 800000000000) 3 (IntervalRat.scale (245 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-33897750346 / 1000000000000) (-33897735382 / 1000000000000), orderedInterval (43107472450 / 1000000000000) (43107487414 / 1000000000000)))) (orderedInterval (-9860573466 / 1000000000000) (-9860552615 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 3) <| besselDerivativeNearFromState (141512332021697 / 800000000000) 3 (IntervalRat.scale (245 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (59073586877 / 1000000000000) (59073587487 / 1000000000000), orderedInterval (-10619147316 / 1000000000000) (-10619146706 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 3) <| besselDerivativeNearFromState (125030436979637 / 800000000000) 3 (IntervalRat.scale (245 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-445995410 / 1000000000000) (-445995405 / 1000000000000), orderedInterval (63823026798 / 1000000000000) (63823026803 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 3) <| besselDerivativeNearFromState (36238693932063 / 160000000000) 3 (IntervalRat.scale (245 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (46808742128 / 1000000000000) (46808742129 / 1000000000000), orderedInterval (24790891501 / 1000000000000) (24790891502 / 1000000000000)))) (orderedInterval (3987059072 / 1000000000000) (3987059134 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate247_chunkChecks3_2 :
    compactCertificate247.chunkChecks (3 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 3) <| besselDerivativeNearFromState (100238134554061 / 800000000000) 3 (IntervalRat.scale (245 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (28958500554 / 1000000000000) (28958500555 / 1000000000000), orderedInterval (65017316760 / 1000000000000) (65017316761 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 3) <| besselDerivativeNearFromState (84972976768421 / 800000000000) 3 (IntervalRat.scale (245 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (14339095992 / 1000000000000) (14339095993 / 1000000000000), orderedInterval (76011889209 / 1000000000000) (76011889210 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 3) <| besselDerivativeNearFromState (53172143439863 / 800000000000) 3 (IntervalRat.scale (245 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-93623951837 / 1000000000000) (-93623951836 / 1000000000000), orderedInterval (-27801445098 / 1000000000000) (-27801445097 / 1000000000000)))) (orderedInterval (14019704747 / 1000000000000) (14019704775 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 3) <| besselDerivativeNearFromState (28596155584521 / 800000000000) 3 (IntervalRat.scale (245 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-122976393528 / 1000000000000) (-122976389892 / 1000000000000), orderedInterval (53541960099 / 1000000000000) (53541963735 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 3) <| besselDerivativeNearFromState (77644125156563 / 800000000000) 3 (IntervalRat.scale (245 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-35219878065 / 1000000000000) (-35219878064 / 1000000000000), orderedInterval (-72749865064 / 1000000000000) (-72749865063 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 3) <| besselDerivativeNearFromState (106016414900851 / 800000000000) 3 (IntervalRat.scale (245 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (67748021559 / 1000000000000) (67748021561 / 1000000000000), orderedInterval (14376821214 / 1000000000000) (14376821216 / 1000000000000)))) (orderedInterval (554711033 / 1000000000000) (554711049 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 3) <| besselDerivativeNearFromState (44827856560137 / 800000000000) 3 (IntervalRat.scale (245 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (28360198763 / 1000000000000) (28360198764 / 1000000000000), orderedInterval (102495358306 / 1000000000000) (102495358307 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 3) <| besselDerivativeNearFromState (182222748148777 / 800000000000) 3 (IntervalRat.scale (245 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (36915346592 / 1000000000000) (36915383883 / 1000000000000), orderedInterval (-37924992911 / 1000000000000) (-37924955620 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 3) <| besselDerivativeNearFromState (121716350820743 / 800000000000) 3 (IntervalRat.scale (245 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (54709979590 / 1000000000000) (54710011808 / 1000000000000), orderedInterval (-34691992991 / 1000000000000) (-34691960773 / 1000000000000)))) (orderedInterval (-32588503609 / 1000000000000) (-32588472243 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate247_chunkChecks3 :
    compactCertificate247.chunkChecks (3 : Fin 5) 0 9 = true :=
  compactCertificate247.chunkChecks_nine_of_three (3 : Fin 5) compactCertificate247_chunkChecks3_0
    compactCertificate247_chunkChecks3_1 compactCertificate247_chunkChecks3_2

theorem compactCertificate247_chunkChecks4_0 :
    compactCertificate247.chunkChecks (4 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 4) <| besselDerivativeNearFromState (245 / 2) 4 (IntervalRat.scale (245 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-49781984869 / 1000000000000) (-49781984868 / 1000000000000), orderedInterval (-51937506711 / 1000000000000) (-51937506710 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 4) <| besselDerivativeNearFromState (72186356447149 / 800000000000) 4 (IntervalRat.scale (245 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (7484814662 / 1000000000000) (7484814691 / 1000000000000), orderedInterval (-83703747465 / 1000000000000) (-83703747437 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 4) <| besselDerivativeNearFromState (23343584512717 / 160000000000) 4 (IntervalRat.scale (245 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (54597408213 / 1000000000000) (54597451196 / 1000000000000), orderedInterval (-37370280315 / 1000000000000) (-37370237332 / 1000000000000)))) (orderedInterval (-13663486343 / 1000000000000) (-13663481183 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 4) <| besselDerivativeNearFromState (21063798775943 / 800000000000) 4 (IntervalRat.scale (245 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (142788550658 / 1000000000000) (142788554477 / 1000000000000), orderedInterval (-64250546186 / 1000000000000) (-64250542367 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 4) <| besselDerivativeNearFromState (56580326380571 / 800000000000) 4 (IntervalRat.scale (245 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (64502379568 / 1000000000000) (64502439210 / 1000000000000), orderedInterval (-70031466523 / 1000000000000) (-70031406881 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 4) <| besselDerivativeNearFromState (153626592564207 / 800000000000) 4 (IntervalRat.scale (245 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-53254615056 / 1000000000000) (-53254615055 / 1000000000000), orderedInterval (-21749511813 / 1000000000000) (-21749511812 / 1000000000000)))) (orderedInterval (23208249509 / 1000000000000) (23208249813 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 4) <| besselDerivativeNearFromState (113160652761191 / 800000000000) 4 (IntervalRat.scale (245 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-51001005100 / 1000000000000) (-51001005099 / 1000000000000), orderedInterval (-43403403772 / 1000000000000) (-43403403771 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 4) <| besselDerivativeNearFromState (193902707267843 / 800000000000) 4 (IntervalRat.scale (245 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-48804392531 / 1000000000000) (-48804392530 / 1000000000000), orderedInterval (-15541577186 / 1000000000000) (-15541577185 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 4) <| besselDerivativeNearFromState (142827856560137 / 800000000000) 4 (IntervalRat.scale (245 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-14700475156 / 1000000000000) (-14700475155 / 1000000000000), orderedInterval (-57835510205 / 1000000000000) (-57835510204 / 1000000000000)))) (orderedInterval (21456704273 / 1000000000000) (21456704346 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate247_chunkChecks4_1 :
    compactCertificate247.chunkChecks (4 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 4) <| besselDerivativeNearFromState (219134661794951 / 800000000000) 4 (IntervalRat.scale (245 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-47376808853 / 1000000000000) (-47376808846 / 1000000000000), orderedInterval (-8832991724 / 1000000000000) (-8832991717 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 4) <| besselDerivativeNearFromState (126517455976079 / 800000000000) 4 (IntervalRat.scale (245 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (60958211680 / 1000000000000) (60958213587 / 1000000000000), orderedInterval (-17787545727 / 1000000000000) (-17787543819 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 4) <| besselDerivativeNearFromState (224507445798811 / 800000000000) 4 (IntervalRat.scale (245 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-46186535731 / 1000000000000) (-46186533136 / 1000000000000), orderedInterval (11714307444 / 1000000000000) (11714310039 / 1000000000000)))) (orderedInterval (42725186211 / 1000000000000) (42725197923 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 4) <| besselDerivativeNearFromState (209763978205159 / 800000000000) 4 (IntervalRat.scale (245 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-38716637335 / 1000000000000) (-38716537485 / 1000000000000), orderedInterval (30552813529 / 1000000000000) (30552913379 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 4) <| besselDerivativeNearFromState (149697472701847 / 800000000000) 4 (IntervalRat.scale (245 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-32402369856 / 1000000000000) (-32402362051 / 1000000000000), orderedInterval (48586663148 / 1000000000000) (48586670954 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 4) <| besselDerivativeNearFromState (169740979141713 / 800000000000) 4 (IntervalRat.scale (245 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-33897750346 / 1000000000000) (-33897735382 / 1000000000000), orderedInterval (43107472450 / 1000000000000) (43107487414 / 1000000000000)))) (orderedInterval (-305763474 / 1000000000000) (-305720485 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 4) <| besselDerivativeNearFromState (141512332021697 / 800000000000) 4 (IntervalRat.scale (245 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (59073586877 / 1000000000000) (59073587487 / 1000000000000), orderedInterval (-10619147316 / 1000000000000) (-10619146706 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 4) <| besselDerivativeNearFromState (125030436979637 / 800000000000) 4 (IntervalRat.scale (245 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-445995410 / 1000000000000) (-445995405 / 1000000000000), orderedInterval (63823026798 / 1000000000000) (63823026803 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 4) <| besselDerivativeNearFromState (36238693932063 / 160000000000) 4 (IntervalRat.scale (245 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (46808742128 / 1000000000000) (46808742129 / 1000000000000), orderedInterval (24790891501 / 1000000000000) (24790891502 / 1000000000000)))) (orderedInterval (16973626378 / 1000000000000) (16973626472 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate247_chunkChecks4_2 :
    compactCertificate247.chunkChecks (4 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 4) <| besselDerivativeNearFromState (100238134554061 / 800000000000) 4 (IntervalRat.scale (245 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (28958500554 / 1000000000000) (28958500555 / 1000000000000), orderedInterval (65017316760 / 1000000000000) (65017316761 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 4) <| besselDerivativeNearFromState (84972976768421 / 800000000000) 4 (IntervalRat.scale (245 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (14339095992 / 1000000000000) (14339095993 / 1000000000000), orderedInterval (76011889209 / 1000000000000) (76011889210 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 4) <| besselDerivativeNearFromState (53172143439863 / 800000000000) 4 (IntervalRat.scale (245 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-93623951837 / 1000000000000) (-93623951836 / 1000000000000), orderedInterval (-27801445098 / 1000000000000) (-27801445097 / 1000000000000)))) (orderedInterval (-6019269061 / 1000000000000) (-6019269034 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 4) <| besselDerivativeNearFromState (28596155584521 / 800000000000) 4 (IntervalRat.scale (245 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-122976393528 / 1000000000000) (-122976389892 / 1000000000000), orderedInterval (53541960099 / 1000000000000) (53541963735 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 4) <| besselDerivativeNearFromState (77644125156563 / 800000000000) 4 (IntervalRat.scale (245 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-35219878065 / 1000000000000) (-35219878064 / 1000000000000), orderedInterval (-72749865064 / 1000000000000) (-72749865063 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 4) <| besselDerivativeNearFromState (106016414900851 / 800000000000) 4 (IntervalRat.scale (245 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (67748021559 / 1000000000000) (67748021561 / 1000000000000), orderedInterval (14376821214 / 1000000000000) (14376821216 / 1000000000000)))) (orderedInterval (-6788445387 / 1000000000000) (-6788445371 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 4) <| besselDerivativeNearFromState (44827856560137 / 800000000000) 4 (IntervalRat.scale (245 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (28360198763 / 1000000000000) (28360198764 / 1000000000000), orderedInterval (102495358306 / 1000000000000) (102495358307 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 4) <| besselDerivativeNearFromState (182222748148777 / 800000000000) 4 (IntervalRat.scale (245 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (36915346592 / 1000000000000) (36915383883 / 1000000000000), orderedInterval (-37924992911 / 1000000000000) (-37924955620 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 4) <| besselDerivativeNearFromState (121716350820743 / 800000000000) 4 (IntervalRat.scale (245 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (54709979590 / 1000000000000) (54710011808 / 1000000000000), orderedInterval (-34691992991 / 1000000000000) (-34691960773 / 1000000000000)))) (orderedInterval (-59805644194 / 1000000000000) (-59805592844 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate247_chunkChecks4 :
    compactCertificate247.chunkChecks (4 : Fin 5) 0 9 = true :=
  compactCertificate247.chunkChecks_nine_of_three (4 : Fin 5) compactCertificate247_chunkChecks4_0
    compactCertificate247_chunkChecks4_1 compactCertificate247_chunkChecks4_2

theorem compactCertificate247_chunks :
    ∀ r : Fin 5, ∀ b, compactCertificate247.chunkCheck r b = true :=
  compactCertificate247.chunkChecks_all (by
    intro r
    fin_cases r
    · exact compactCertificate247_chunkChecks0
    · exact compactCertificate247_chunkChecks1
    · exact compactCertificate247_chunkChecks2
    · exact compactCertificate247_chunkChecks3
    · exact compactCertificate247_chunkChecks4)

theorem compactCertificate247_coefficient0 :
    compactCertificate247.coefficientCheck (0 : Fin 5) = true := by
  norm_num [CompactCertificate.coefficientCheck, intervalFinSumHull,
    compactCertificate247, rationalIntervalSubset, orderedInterval, Fin.sum_univ_succ]

theorem compactCertificate247_coefficient1 :
    compactCertificate247.coefficientCheck (1 : Fin 5) = true := by
  norm_num [CompactCertificate.coefficientCheck, intervalFinSumHull,
    compactCertificate247, rationalIntervalSubset, orderedInterval, Fin.sum_univ_succ]

theorem compactCertificate247_coefficient2 :
    compactCertificate247.coefficientCheck (2 : Fin 5) = true := by
  norm_num [CompactCertificate.coefficientCheck, intervalFinSumHull,
    compactCertificate247, rationalIntervalSubset, orderedInterval, Fin.sum_univ_succ]

theorem compactCertificate247_coefficient3 :
    compactCertificate247.coefficientCheck (3 : Fin 5) = true := by
  norm_num [CompactCertificate.coefficientCheck, intervalFinSumHull,
    compactCertificate247, rationalIntervalSubset, orderedInterval, Fin.sum_univ_succ]

theorem compactCertificate247_coefficient4 :
    compactCertificate247.coefficientCheck (4 : Fin 5) = true := by
  norm_num [CompactCertificate.coefficientCheck, intervalFinSumHull,
    compactCertificate247, rationalIntervalSubset, orderedInterval, Fin.sum_univ_succ]

theorem compactCertificate247_coefficients : ∀ r : Fin 5,
    compactCertificate247.coefficientCheck r = true := by
  intro r
  fin_cases r
  · exact compactCertificate247_coefficient0
  · exact compactCertificate247_coefficient1
  · exact compactCertificate247_coefficient2
  · exact compactCertificate247_coefficient3
  · exact compactCertificate247_coefficient4

theorem compactCertificate247_lower : (1 : ℚ) ≤ compactCertificate247.output.lo := by
  norm_num [CompactCertificate.output, CompactCertificate.interval,
    CompactCertificate.coefficientTargetNat, compactCertificate247, dualConstant,
    intervalTaylorSum, intervalPow, intervalSub, intervalMaxAbs, widenInterval,
    rationalErrorInterval, orderedInterval, IntervalRat.add, IntervalRat.mul, IntervalRat.scale,
    IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4]

theorem compactCertificate247_proves {t : ℝ} (ht : t ∈ compactCertificate247.interval) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t :=
  compactCertificate247.proves compactCertificate247_states compactCertificate247_chunks
    compactCertificate247_coefficients compactCertificate247_lower ht

end Erdos232
