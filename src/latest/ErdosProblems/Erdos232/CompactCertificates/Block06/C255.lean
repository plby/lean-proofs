/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, OpenAI Codex
-/
import ErdosProblems.Erdos232.CompactBase

open LeanCert.Core
namespace Erdos232

def compactCertificate255 : CompactCertificate where
  left := 130
  right := 131
  center := 261 / 2
  grid := fun i =>
    match i.val with
    | 0 => 42
    | 1 => 31
    | 2 => 49
    | 3 => 9
    | 4 => 24
    | 5 => 65
    | 6 => 48
    | 7 => 82
    | 8 => 61
    | 9 => 93
    | 10 => 54
    | 11 => 95
    | 12 => 89
    | 13 => 63
    | 14 => 72
    | 15 => 60
    | 16 => 53
    | 17 => 77
    | 18 => 43
    | 19 => 36
    | 20 => 23
    | 21 => 12
    | 22 => 33
    | 23 => 45
    | 24 => 19
    | 25 => 77
    | _ => 52
  point := fun i =>
    match i.val with
    | 0 => 261 / 2
    | 1 => 384502837402161 / 4000000000000
    | 2 => 124340317506513 / 800000000000
    | 3 => 112196968990227 / 4000000000000
    | 4 => 301376840516919 / 4000000000000
    | 5 => 818296748148123 / 4000000000000
    | 6 => 602753681034099 / 4000000000000
    | 7 => 1032828706059327 / 4000000000000
    | 8 => 760776950248893 / 4000000000000
    | 9 => 1167227484254739 / 4000000000000
    | 10 => 673899102239931 / 4000000000000
    | 11 => 1195845782724279 / 4000000000000
    | 12 => 1117314251256051 / 4000000000000
    | 13 => 797368170922083 / 4000000000000
    | 14 => 904130521550757 / 4000000000000
    | 15 => 753769768523733 / 4000000000000
    | 16 => 665978450034393 / 4000000000000
    | 17 => 193026512576907 / 800000000000
    | 18 => 533921492216529 / 4000000000000
    | 19 => 452611161970569 / 4000000000000
    | 20 => 283223049751107 / 4000000000000
    | 21 => 152318298113469 / 4000000000000
    | 22 => 413573809507407 / 4000000000000
    | 23 => 564699679369839 / 4000000000000
    | 24 => 238776950248893 / 4000000000000
    | 25 => 970615046261853 / 4000000000000
    | _ => 648325868657427 / 4000000000000
  state := fun i =>
    match i.val with
    | 0 => (orderedInterval (-42958064120 / 1000000000000) (-42958042975 / 1000000000000), orderedInterval (55236590871 / 1000000000000) (55236612016 / 1000000000000))
    | 1 => (orderedInterval (37548158294 / 1000000000000) (37548162303 / 1000000000000), orderedInterval (-72396209302 / 1000000000000) (-72396205293 / 1000000000000))
    | 2 => (orderedInterval (-48902092533 / 1000000000000) (-48901983672 / 1000000000000), orderedInterval (41443694368 / 1000000000000) (41443803229 / 1000000000000))
    | 3 => (orderedInterval (-79488791879 / 1000000000000) (-79488791878 / 1000000000000), orderedInterval (-126566434400 / 1000000000000) (-126566434399 / 1000000000000))
    | 4 => (orderedInterval (61279912038 / 1000000000000) (61279912039 / 1000000000000), orderedInterval (68108153128 / 1000000000000) (68108153129 / 1000000000000))
    | 5 => (orderedInterval (-51041605095 / 1000000000000) (-51041605094 / 1000000000000), orderedInterval (-22384680835 / 1000000000000) (-22384680834 / 1000000000000))
    | 6 => (orderedInterval (40695152117 / 1000000000000) (40695152118 / 1000000000000), orderedInterval (50546842319 / 1000000000000) (50546842320 / 1000000000000))
    | 7 => (orderedInterval (48767100890 / 1000000000000) (48767100896 / 1000000000000), orderedInterval (9249239095 / 1000000000000) (9249239101 / 1000000000000))
    | 8 => (orderedInterval (35388300106 / 1000000000000) (35388315359 / 1000000000000), orderedInterval (-45862887793 / 1000000000000) (-45862872539 / 1000000000000))
    | 9 => (orderedInterval (-19204401047 / 1000000000000) (-19204401046 / 1000000000000), orderedInterval (-42544561634 / 1000000000000) (-42544561633 / 1000000000000))
    | 10 => (orderedInterval (-23175572159 / 1000000000000) (-23175571228 / 1000000000000), orderedInterval (57004087887 / 1000000000000) (57004088818 / 1000000000000))
    | 11 => (orderedInterval (-44403439943 / 1000000000000) (-44403439940 / 1000000000000), orderedInterval (-12486377560 / 1000000000000) (-12486377557 / 1000000000000))
    | 12 => (orderedInterval (-23379159798 / 1000000000000) (-23379159797 / 1000000000000), orderedInterval (-41581751651 / 1000000000000) (-41581751650 / 1000000000000))
    | 13 => (orderedInterval (-45473352864 / 1000000000000) (-45473277301 / 1000000000000), orderedInterval (33666658605 / 1000000000000) (33666734167 / 1000000000000))
    | 14 => (orderedInterval (30956894522 / 1000000000000) (30956894523 / 1000000000000), orderedInterval (43037992943 / 1000000000000) (43037992944 / 1000000000000))
    | 15 => (orderedInterval (38830651975 / 1000000000000) (38830651976 / 1000000000000), orderedInterval (43146323091 / 1000000000000) (43146323092 / 1000000000000))
    | 16 => (orderedInterval (-43260745055 / 1000000000000) (-43260745054 / 1000000000000), orderedInterval (-44053500273 / 1000000000000) (-44053500272 / 1000000000000))
    | 17 => (orderedInterval (-8456574880 / 1000000000000) (-8456574879 / 1000000000000), orderedInterval (-50647727152 / 1000000000000) (-50647727151 / 1000000000000))
    | 18 => (orderedInterval (50664863365 / 1000000000000) (50664951096 / 1000000000000), orderedInterval (-47120122860 / 1000000000000) (-47120035128 / 1000000000000))
    | 19 => (orderedInterval (55841303615 / 1000000000000) (55841303616 / 1000000000000), orderedInterval (49832578211 / 1000000000000) (49832578212 / 1000000000000))
    | 20 => (orderedInterval (58676251984 / 1000000000000) (58676281061 / 1000000000000), orderedInterval (-74900721041 / 1000000000000) (-74900691964 / 1000000000000))
    | 21 => (orderedInterval (118669094220 / 1000000000000) (118669094221 / 1000000000000), orderedInterval (49772430557 / 1000000000000) (49772430558 / 1000000000000))
    | 22 => (orderedInterval (-37969036474 / 1000000000000) (-37969036473 / 1000000000000), orderedInterval (-68486942465 / 1000000000000) (-68486942464 / 1000000000000))
    | 23 => (orderedInterval (-37235933030 / 1000000000000) (-37235933029 / 1000000000000), orderedInterval (-55751356287 / 1000000000000) (-55751356286 / 1000000000000))
    | 24 => (orderedInterval (-73158985811 / 1000000000000) (-73158985810 / 1000000000000), orderedInterval (-72273739196 / 1000000000000) (-72273739195 / 1000000000000))
    | 25 => (orderedInterval (-51189780863 / 1000000000000) (-51189780807 / 1000000000000), orderedInterval (-1675934439 / 1000000000000) (-1675934382 / 1000000000000))
    | _ => (orderedInterval (-29866127954 / 1000000000000) (-29866124571 / 1000000000000), orderedInterval (55190235337 / 1000000000000) (55190238720 / 1000000000000))
  chunkTarget := fun r b =>
    match r.val with
    | 0 =>
      match b.val with
      | 0 => orderedInterval (-19546827336 / 1000000000000) (-19546812519 / 1000000000000)
      | 1 => orderedInterval (6728362992 / 1000000000000) (6728363008 / 1000000000000)
      | 2 => orderedInterval (-648907120 / 1000000000000) (-648906743 / 1000000000000)
      | 3 => orderedInterval (-4616939632 / 1000000000000) (-4616939510 / 1000000000000)
      | 4 => orderedInterval (-4034684317 / 1000000000000) (-4034677155 / 1000000000000)
      | 5 => orderedInterval (2707550512 / 1000000000000) (2707550525 / 1000000000000)
      | 6 => orderedInterval (-9351336814 / 1000000000000) (-9351321807 / 1000000000000)
      | 7 => orderedInterval (1523879404 / 1000000000000) (1523879421 / 1000000000000)
      | _ => orderedInterval (9329589969 / 1000000000000) (9329590645 / 1000000000000)
    | 1 =>
      match b.val with
      | 0 => orderedInterval (24293415658 / 1000000000000) (24293431686 / 1000000000000)
      | 1 => orderedInterval (4225446700 / 1000000000000) (4225446718 / 1000000000000)
      | 2 => orderedInterval (-2179896561 / 1000000000000) (-2179896010 / 1000000000000)
      | 3 => orderedInterval (18290099304 / 1000000000000) (18290099502 / 1000000000000)
      | 4 => orderedInterval (6092607609 / 1000000000000) (6092618550 / 1000000000000)
      | 5 => orderedInterval (1538212114 / 1000000000000) (1538212133 / 1000000000000)
      | 6 => orderedInterval (3937592829 / 1000000000000) (3937607722 / 1000000000000)
      | 7 => orderedInterval (5585071503 / 1000000000000) (5585071518 / 1000000000000)
      | _ => orderedInterval (-12806764210 / 1000000000000) (-12806763362 / 1000000000000)
    | 2 =>
      match b.val with
      | 0 => orderedInterval (20721576516 / 1000000000000) (20721594114 / 1000000000000)
      | 1 => orderedInterval (-9734878415 / 1000000000000) (-9734878390 / 1000000000000)
      | 2 => orderedInterval (4088655580 / 1000000000000) (4088656391 / 1000000000000)
      | 3 => orderedInterval (18787425242 / 1000000000000) (18787425591 / 1000000000000)
      | 4 => orderedInterval (8523116285 / 1000000000000) (8523133084 / 1000000000000)
      | 5 => orderedInterval (-4236291037 / 1000000000000) (-4236291009 / 1000000000000)
      | 6 => orderedInterval (10258849043 / 1000000000000) (10258864141 / 1000000000000)
      | 7 => orderedInterval (-3736622805 / 1000000000000) (-3736622790 / 1000000000000)
      | _ => orderedInterval (-22860553619 / 1000000000000) (-22860552542 / 1000000000000)
    | 3 =>
      match b.val with
      | 0 => orderedInterval (-25890201440 / 1000000000000) (-25890182106 / 1000000000000)
      | 1 => orderedInterval (-6547614946 / 1000000000000) (-6547614908 / 1000000000000)
      | 2 => orderedInterval (5609660593 / 1000000000000) (5609661784 / 1000000000000)
      | 3 => orderedInterval (-72408972091 / 1000000000000) (-72408971431 / 1000000000000)
      | 4 => orderedInterval (-17641938038 / 1000000000000) (-17641912372 / 1000000000000)
      | 5 => orderedInterval (1493268554 / 1000000000000) (1493268596 / 1000000000000)
      | 6 => orderedInterval (-5912504285 / 1000000000000) (-5912488981 / 1000000000000)
      | 7 => orderedInterval (-6130295315 / 1000000000000) (-6130295299 / 1000000000000)
      | _ => orderedInterval (19178323003 / 1000000000000) (19178324373 / 1000000000000)
    | _ =>
      match b.val with
      | 0 => orderedInterval (-22300019049 / 1000000000000) (-22299997496 / 1000000000000)
      | 1 => orderedInterval (22262717879 / 1000000000000) (22262717937 / 1000000000000)
      | 2 => orderedInterval (-19280039844 / 1000000000000) (-19280038084 / 1000000000000)
      | 3 => orderedInterval (-92209410019 / 1000000000000) (-92209408690 / 1000000000000)
      | 4 => orderedInterval (-15691364115 / 1000000000000) (-15691324701 / 1000000000000)
      | 5 => orderedInterval (5955381398 / 1000000000000) (5955381465 / 1000000000000)
      | 6 => orderedInterval (-10396414197 / 1000000000000) (-10396398503 / 1000000000000)
      | 7 => orderedInterval (4325664635 / 1000000000000) (4325664651 / 1000000000000)
      | _ => orderedInterval (62830324441 / 1000000000000) (62830326211 / 1000000000000)
  coefficientTarget := fun i =>
    match i.val with
    | 0 => orderedInterval (-17909312342 / 1000000000000) (-17909274135 / 1000000000000)
    | 1 => orderedInterval (48975784946 / 1000000000000) (48975828457 / 1000000000000)
    | 2 => orderedInterval (21811276790 / 1000000000000) (21811328590 / 1000000000000)
    | 3 => orderedInterval (-108250273965 / 1000000000000) (-108250210344 / 1000000000000)
    | _ => orderedInterval (-64503158871 / 1000000000000) (-64503077210 / 1000000000000)

theorem compactCertificate255_stateChecks0 :
    compactCertificate255.stateChecks 0 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 42 12 (261 / 2)) (orderedInterval (-42958064120 / 1000000000000) (-42958042975 / 1000000000000), orderedInterval (55236590871 / 1000000000000) (55236612016 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 31 12 (384502837402161 / 4000000000000)) (orderedInterval (37548158294 / 1000000000000) (37548162303 / 1000000000000), orderedInterval (-72396209302 / 1000000000000) (-72396205293 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 49 12 (124340317506513 / 800000000000)) (orderedInterval (-48902092533 / 1000000000000) (-48901983672 / 1000000000000), orderedInterval (41443694368 / 1000000000000) (41443803229 / 1000000000000))) = true
  norm_num [besselStateAtRationalPoint, besselIntervalStepZero,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, besselZeroTransition,
    besselInitial, besselGridStateAt, besselGridStateBlock00, besselGridStateBlock01,
    besselGridStateBlock02, besselGridStateBlock03, besselGridStateBlock04,
    besselGridStateBlock05, besselGridStateBlock06, besselGridStateBlock07,
    besselGridStateBlock08, besselGridStateBlock09, besselGridStateBlock10,
    besselGridStateBlock11, besselGridStateBlock12, besselGridStateBlock13,
    besselGridStateBlock14, besselGridState009, besselGridState012, besselGridState019, besselGridState023, besselGridState024, besselGridState031, besselGridState033, besselGridState036, besselGridState042, besselGridState043, besselGridState045, besselGridState048, besselGridState049, besselGridState052, besselGridState053, besselGridState054, besselGridState060, besselGridState061, besselGridState063, besselGridState065, besselGridState072, besselGridState077, besselGridState082, besselGridState089, besselGridState093, besselGridState095, besselStateSubset, linearInterval, widenInterval,
    rationalErrorInterval, rationalIntervalSubset, orderedInterval, Finset.sum_range_succ,
    IntervalRat.add, IntervalRat.mul, IntervalRat.scale, IntervalRat.singleton]

theorem compactCertificate255_stateChecks1 :
    compactCertificate255.stateChecks 3 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 9 12 (112196968990227 / 4000000000000)) (orderedInterval (-79488791879 / 1000000000000) (-79488791878 / 1000000000000), orderedInterval (-126566434400 / 1000000000000) (-126566434399 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 24 12 (301376840516919 / 4000000000000)) (orderedInterval (61279912038 / 1000000000000) (61279912039 / 1000000000000), orderedInterval (68108153128 / 1000000000000) (68108153129 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 65 12 (818296748148123 / 4000000000000)) (orderedInterval (-51041605095 / 1000000000000) (-51041605094 / 1000000000000), orderedInterval (-22384680835 / 1000000000000) (-22384680834 / 1000000000000))) = true
  norm_num [besselStateAtRationalPoint, besselIntervalStepZero,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, besselZeroTransition,
    besselInitial, besselGridStateAt, besselGridStateBlock00, besselGridStateBlock01,
    besselGridStateBlock02, besselGridStateBlock03, besselGridStateBlock04,
    besselGridStateBlock05, besselGridStateBlock06, besselGridStateBlock07,
    besselGridStateBlock08, besselGridStateBlock09, besselGridStateBlock10,
    besselGridStateBlock11, besselGridStateBlock12, besselGridStateBlock13,
    besselGridStateBlock14, besselGridState009, besselGridState012, besselGridState019, besselGridState023, besselGridState024, besselGridState031, besselGridState033, besselGridState036, besselGridState042, besselGridState043, besselGridState045, besselGridState048, besselGridState049, besselGridState052, besselGridState053, besselGridState054, besselGridState060, besselGridState061, besselGridState063, besselGridState065, besselGridState072, besselGridState077, besselGridState082, besselGridState089, besselGridState093, besselGridState095, besselStateSubset, linearInterval, widenInterval,
    rationalErrorInterval, rationalIntervalSubset, orderedInterval, Finset.sum_range_succ,
    IntervalRat.add, IntervalRat.mul, IntervalRat.scale, IntervalRat.singleton]

theorem compactCertificate255_stateChecks2 :
    compactCertificate255.stateChecks 6 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 48 12 (602753681034099 / 4000000000000)) (orderedInterval (40695152117 / 1000000000000) (40695152118 / 1000000000000), orderedInterval (50546842319 / 1000000000000) (50546842320 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 82 12 (1032828706059327 / 4000000000000)) (orderedInterval (48767100890 / 1000000000000) (48767100896 / 1000000000000), orderedInterval (9249239095 / 1000000000000) (9249239101 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 61 12 (760776950248893 / 4000000000000)) (orderedInterval (35388300106 / 1000000000000) (35388315359 / 1000000000000), orderedInterval (-45862887793 / 1000000000000) (-45862872539 / 1000000000000))) = true
  norm_num [besselStateAtRationalPoint, besselIntervalStepZero,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, besselZeroTransition,
    besselInitial, besselGridStateAt, besselGridStateBlock00, besselGridStateBlock01,
    besselGridStateBlock02, besselGridStateBlock03, besselGridStateBlock04,
    besselGridStateBlock05, besselGridStateBlock06, besselGridStateBlock07,
    besselGridStateBlock08, besselGridStateBlock09, besselGridStateBlock10,
    besselGridStateBlock11, besselGridStateBlock12, besselGridStateBlock13,
    besselGridStateBlock14, besselGridState009, besselGridState012, besselGridState019, besselGridState023, besselGridState024, besselGridState031, besselGridState033, besselGridState036, besselGridState042, besselGridState043, besselGridState045, besselGridState048, besselGridState049, besselGridState052, besselGridState053, besselGridState054, besselGridState060, besselGridState061, besselGridState063, besselGridState065, besselGridState072, besselGridState077, besselGridState082, besselGridState089, besselGridState093, besselGridState095, besselStateSubset, linearInterval, widenInterval,
    rationalErrorInterval, rationalIntervalSubset, orderedInterval, Finset.sum_range_succ,
    IntervalRat.add, IntervalRat.mul, IntervalRat.scale, IntervalRat.singleton]

theorem compactCertificate255_stateChecks3 :
    compactCertificate255.stateChecks 9 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 93 12 (1167227484254739 / 4000000000000)) (orderedInterval (-19204401047 / 1000000000000) (-19204401046 / 1000000000000), orderedInterval (-42544561634 / 1000000000000) (-42544561633 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 54 12 (673899102239931 / 4000000000000)) (orderedInterval (-23175572159 / 1000000000000) (-23175571228 / 1000000000000), orderedInterval (57004087887 / 1000000000000) (57004088818 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 95 12 (1195845782724279 / 4000000000000)) (orderedInterval (-44403439943 / 1000000000000) (-44403439940 / 1000000000000), orderedInterval (-12486377560 / 1000000000000) (-12486377557 / 1000000000000))) = true
  norm_num [besselStateAtRationalPoint, besselIntervalStepZero,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, besselZeroTransition,
    besselInitial, besselGridStateAt, besselGridStateBlock00, besselGridStateBlock01,
    besselGridStateBlock02, besselGridStateBlock03, besselGridStateBlock04,
    besselGridStateBlock05, besselGridStateBlock06, besselGridStateBlock07,
    besselGridStateBlock08, besselGridStateBlock09, besselGridStateBlock10,
    besselGridStateBlock11, besselGridStateBlock12, besselGridStateBlock13,
    besselGridStateBlock14, besselGridState009, besselGridState012, besselGridState019, besselGridState023, besselGridState024, besselGridState031, besselGridState033, besselGridState036, besselGridState042, besselGridState043, besselGridState045, besselGridState048, besselGridState049, besselGridState052, besselGridState053, besselGridState054, besselGridState060, besselGridState061, besselGridState063, besselGridState065, besselGridState072, besselGridState077, besselGridState082, besselGridState089, besselGridState093, besselGridState095, besselStateSubset, linearInterval, widenInterval,
    rationalErrorInterval, rationalIntervalSubset, orderedInterval, Finset.sum_range_succ,
    IntervalRat.add, IntervalRat.mul, IntervalRat.scale, IntervalRat.singleton]

theorem compactCertificate255_stateChecks4 :
    compactCertificate255.stateChecks 12 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 89 12 (1117314251256051 / 4000000000000)) (orderedInterval (-23379159798 / 1000000000000) (-23379159797 / 1000000000000), orderedInterval (-41581751651 / 1000000000000) (-41581751650 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 63 12 (797368170922083 / 4000000000000)) (orderedInterval (-45473352864 / 1000000000000) (-45473277301 / 1000000000000), orderedInterval (33666658605 / 1000000000000) (33666734167 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 72 12 (904130521550757 / 4000000000000)) (orderedInterval (30956894522 / 1000000000000) (30956894523 / 1000000000000), orderedInterval (43037992943 / 1000000000000) (43037992944 / 1000000000000))) = true
  norm_num [besselStateAtRationalPoint, besselIntervalStepZero,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, besselZeroTransition,
    besselInitial, besselGridStateAt, besselGridStateBlock00, besselGridStateBlock01,
    besselGridStateBlock02, besselGridStateBlock03, besselGridStateBlock04,
    besselGridStateBlock05, besselGridStateBlock06, besselGridStateBlock07,
    besselGridStateBlock08, besselGridStateBlock09, besselGridStateBlock10,
    besselGridStateBlock11, besselGridStateBlock12, besselGridStateBlock13,
    besselGridStateBlock14, besselGridState009, besselGridState012, besselGridState019, besselGridState023, besselGridState024, besselGridState031, besselGridState033, besselGridState036, besselGridState042, besselGridState043, besselGridState045, besselGridState048, besselGridState049, besselGridState052, besselGridState053, besselGridState054, besselGridState060, besselGridState061, besselGridState063, besselGridState065, besselGridState072, besselGridState077, besselGridState082, besselGridState089, besselGridState093, besselGridState095, besselStateSubset, linearInterval, widenInterval,
    rationalErrorInterval, rationalIntervalSubset, orderedInterval, Finset.sum_range_succ,
    IntervalRat.add, IntervalRat.mul, IntervalRat.scale, IntervalRat.singleton]

theorem compactCertificate255_stateChecks5 :
    compactCertificate255.stateChecks 15 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 60 12 (753769768523733 / 4000000000000)) (orderedInterval (38830651975 / 1000000000000) (38830651976 / 1000000000000), orderedInterval (43146323091 / 1000000000000) (43146323092 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 53 12 (665978450034393 / 4000000000000)) (orderedInterval (-43260745055 / 1000000000000) (-43260745054 / 1000000000000), orderedInterval (-44053500273 / 1000000000000) (-44053500272 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 77 12 (193026512576907 / 800000000000)) (orderedInterval (-8456574880 / 1000000000000) (-8456574879 / 1000000000000), orderedInterval (-50647727152 / 1000000000000) (-50647727151 / 1000000000000))) = true
  norm_num [besselStateAtRationalPoint, besselIntervalStepZero,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, besselZeroTransition,
    besselInitial, besselGridStateAt, besselGridStateBlock00, besselGridStateBlock01,
    besselGridStateBlock02, besselGridStateBlock03, besselGridStateBlock04,
    besselGridStateBlock05, besselGridStateBlock06, besselGridStateBlock07,
    besselGridStateBlock08, besselGridStateBlock09, besselGridStateBlock10,
    besselGridStateBlock11, besselGridStateBlock12, besselGridStateBlock13,
    besselGridStateBlock14, besselGridState009, besselGridState012, besselGridState019, besselGridState023, besselGridState024, besselGridState031, besselGridState033, besselGridState036, besselGridState042, besselGridState043, besselGridState045, besselGridState048, besselGridState049, besselGridState052, besselGridState053, besselGridState054, besselGridState060, besselGridState061, besselGridState063, besselGridState065, besselGridState072, besselGridState077, besselGridState082, besselGridState089, besselGridState093, besselGridState095, besselStateSubset, linearInterval, widenInterval,
    rationalErrorInterval, rationalIntervalSubset, orderedInterval, Finset.sum_range_succ,
    IntervalRat.add, IntervalRat.mul, IntervalRat.scale, IntervalRat.singleton]

theorem compactCertificate255_stateChecks6 :
    compactCertificate255.stateChecks 18 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 43 12 (533921492216529 / 4000000000000)) (orderedInterval (50664863365 / 1000000000000) (50664951096 / 1000000000000), orderedInterval (-47120122860 / 1000000000000) (-47120035128 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 36 12 (452611161970569 / 4000000000000)) (orderedInterval (55841303615 / 1000000000000) (55841303616 / 1000000000000), orderedInterval (49832578211 / 1000000000000) (49832578212 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 23 12 (283223049751107 / 4000000000000)) (orderedInterval (58676251984 / 1000000000000) (58676281061 / 1000000000000), orderedInterval (-74900721041 / 1000000000000) (-74900691964 / 1000000000000))) = true
  norm_num [besselStateAtRationalPoint, besselIntervalStepZero,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, besselZeroTransition,
    besselInitial, besselGridStateAt, besselGridStateBlock00, besselGridStateBlock01,
    besselGridStateBlock02, besselGridStateBlock03, besselGridStateBlock04,
    besselGridStateBlock05, besselGridStateBlock06, besselGridStateBlock07,
    besselGridStateBlock08, besselGridStateBlock09, besselGridStateBlock10,
    besselGridStateBlock11, besselGridStateBlock12, besselGridStateBlock13,
    besselGridStateBlock14, besselGridState009, besselGridState012, besselGridState019, besselGridState023, besselGridState024, besselGridState031, besselGridState033, besselGridState036, besselGridState042, besselGridState043, besselGridState045, besselGridState048, besselGridState049, besselGridState052, besselGridState053, besselGridState054, besselGridState060, besselGridState061, besselGridState063, besselGridState065, besselGridState072, besselGridState077, besselGridState082, besselGridState089, besselGridState093, besselGridState095, besselStateSubset, linearInterval, widenInterval,
    rationalErrorInterval, rationalIntervalSubset, orderedInterval, Finset.sum_range_succ,
    IntervalRat.add, IntervalRat.mul, IntervalRat.scale, IntervalRat.singleton]

theorem compactCertificate255_stateChecks7 :
    compactCertificate255.stateChecks 21 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 12 12 (152318298113469 / 4000000000000)) (orderedInterval (118669094220 / 1000000000000) (118669094221 / 1000000000000), orderedInterval (49772430557 / 1000000000000) (49772430558 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 33 12 (413573809507407 / 4000000000000)) (orderedInterval (-37969036474 / 1000000000000) (-37969036473 / 1000000000000), orderedInterval (-68486942465 / 1000000000000) (-68486942464 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 45 12 (564699679369839 / 4000000000000)) (orderedInterval (-37235933030 / 1000000000000) (-37235933029 / 1000000000000), orderedInterval (-55751356287 / 1000000000000) (-55751356286 / 1000000000000))) = true
  norm_num [besselStateAtRationalPoint, besselIntervalStepZero,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, besselZeroTransition,
    besselInitial, besselGridStateAt, besselGridStateBlock00, besselGridStateBlock01,
    besselGridStateBlock02, besselGridStateBlock03, besselGridStateBlock04,
    besselGridStateBlock05, besselGridStateBlock06, besselGridStateBlock07,
    besselGridStateBlock08, besselGridStateBlock09, besselGridStateBlock10,
    besselGridStateBlock11, besselGridStateBlock12, besselGridStateBlock13,
    besselGridStateBlock14, besselGridState009, besselGridState012, besselGridState019, besselGridState023, besselGridState024, besselGridState031, besselGridState033, besselGridState036, besselGridState042, besselGridState043, besselGridState045, besselGridState048, besselGridState049, besselGridState052, besselGridState053, besselGridState054, besselGridState060, besselGridState061, besselGridState063, besselGridState065, besselGridState072, besselGridState077, besselGridState082, besselGridState089, besselGridState093, besselGridState095, besselStateSubset, linearInterval, widenInterval,
    rationalErrorInterval, rationalIntervalSubset, orderedInterval, Finset.sum_range_succ,
    IntervalRat.add, IntervalRat.mul, IntervalRat.scale, IntervalRat.singleton]

theorem compactCertificate255_stateChecks8 :
    compactCertificate255.stateChecks 24 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 19 12 (238776950248893 / 4000000000000)) (orderedInterval (-73158985811 / 1000000000000) (-73158985810 / 1000000000000), orderedInterval (-72273739196 / 1000000000000) (-72273739195 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 77 12 (970615046261853 / 4000000000000)) (orderedInterval (-51189780863 / 1000000000000) (-51189780807 / 1000000000000), orderedInterval (-1675934439 / 1000000000000) (-1675934382 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 52 12 (648325868657427 / 4000000000000)) (orderedInterval (-29866127954 / 1000000000000) (-29866124571 / 1000000000000), orderedInterval (55190235337 / 1000000000000) (55190238720 / 1000000000000))) = true
  norm_num [besselStateAtRationalPoint, besselIntervalStepZero,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, besselZeroTransition,
    besselInitial, besselGridStateAt, besselGridStateBlock00, besselGridStateBlock01,
    besselGridStateBlock02, besselGridStateBlock03, besselGridStateBlock04,
    besselGridStateBlock05, besselGridStateBlock06, besselGridStateBlock07,
    besselGridStateBlock08, besselGridStateBlock09, besselGridStateBlock10,
    besselGridStateBlock11, besselGridStateBlock12, besselGridStateBlock13,
    besselGridStateBlock14, besselGridState009, besselGridState012, besselGridState019, besselGridState023, besselGridState024, besselGridState031, besselGridState033, besselGridState036, besselGridState042, besselGridState043, besselGridState045, besselGridState048, besselGridState049, besselGridState052, besselGridState053, besselGridState054, besselGridState060, besselGridState061, besselGridState063, besselGridState065, besselGridState072, besselGridState077, besselGridState082, besselGridState089, besselGridState093, besselGridState095, besselStateSubset, linearInterval, widenInterval,
    rationalErrorInterval, rationalIntervalSubset, orderedInterval, Finset.sum_range_succ,
    IntervalRat.add, IntervalRat.mul, IntervalRat.scale, IntervalRat.singleton]

theorem compactCertificate255_states : ∀ j,
    BesselStateValid (compactCertificate255.point j) (compactCertificate255.state j) :=
  compactCertificate255.statesValid_of_checks3 compactCertificate255_stateChecks0
    compactCertificate255_stateChecks1 compactCertificate255_stateChecks2
    compactCertificate255_stateChecks3 compactCertificate255_stateChecks4
    compactCertificate255_stateChecks5 compactCertificate255_stateChecks6
    compactCertificate255_stateChecks7 compactCertificate255_stateChecks8

theorem compactCertificate255_chunkChecks0_0 :
    compactCertificate255.chunkChecks (0 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 0) <| besselDerivativeNearFromState (261 / 2) 0 (IntervalRat.scale (261 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-42958064120 / 1000000000000) (-42958042975 / 1000000000000), orderedInterval (55236590871 / 1000000000000) (55236612016 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 0) <| besselDerivativeNearFromState (384502837402161 / 4000000000000) 0 (IntervalRat.scale (261 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (37548158294 / 1000000000000) (37548162303 / 1000000000000), orderedInterval (-72396209302 / 1000000000000) (-72396205293 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 0) <| besselDerivativeNearFromState (124340317506513 / 800000000000) 0 (IntervalRat.scale (261 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-48902092533 / 1000000000000) (-48901983672 / 1000000000000), orderedInterval (41443694368 / 1000000000000) (41443803229 / 1000000000000)))) (orderedInterval (-19546827336 / 1000000000000) (-19546812519 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 0) <| besselDerivativeNearFromState (112196968990227 / 4000000000000) 0 (IntervalRat.scale (261 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-79488791879 / 1000000000000) (-79488791878 / 1000000000000), orderedInterval (-126566434400 / 1000000000000) (-126566434399 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 0) <| besselDerivativeNearFromState (301376840516919 / 4000000000000) 0 (IntervalRat.scale (261 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (61279912038 / 1000000000000) (61279912039 / 1000000000000), orderedInterval (68108153128 / 1000000000000) (68108153129 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 0) <| besselDerivativeNearFromState (818296748148123 / 4000000000000) 0 (IntervalRat.scale (261 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-51041605095 / 1000000000000) (-51041605094 / 1000000000000), orderedInterval (-22384680835 / 1000000000000) (-22384680834 / 1000000000000)))) (orderedInterval (6728362992 / 1000000000000) (6728363008 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 0) <| besselDerivativeNearFromState (602753681034099 / 4000000000000) 0 (IntervalRat.scale (261 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (40695152117 / 1000000000000) (40695152118 / 1000000000000), orderedInterval (50546842319 / 1000000000000) (50546842320 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 0) <| besselDerivativeNearFromState (1032828706059327 / 4000000000000) 0 (IntervalRat.scale (261 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (48767100890 / 1000000000000) (48767100896 / 1000000000000), orderedInterval (9249239095 / 1000000000000) (9249239101 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 0) <| besselDerivativeNearFromState (760776950248893 / 4000000000000) 0 (IntervalRat.scale (261 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (35388300106 / 1000000000000) (35388315359 / 1000000000000), orderedInterval (-45862887793 / 1000000000000) (-45862872539 / 1000000000000)))) (orderedInterval (-648907120 / 1000000000000) (-648906743 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate255_chunkChecks0_1 :
    compactCertificate255.chunkChecks (0 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 0) <| besselDerivativeNearFromState (1167227484254739 / 4000000000000) 0 (IntervalRat.scale (261 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-19204401047 / 1000000000000) (-19204401046 / 1000000000000), orderedInterval (-42544561634 / 1000000000000) (-42544561633 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 0) <| besselDerivativeNearFromState (673899102239931 / 4000000000000) 0 (IntervalRat.scale (261 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-23175572159 / 1000000000000) (-23175571228 / 1000000000000), orderedInterval (57004087887 / 1000000000000) (57004088818 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 0) <| besselDerivativeNearFromState (1195845782724279 / 4000000000000) 0 (IntervalRat.scale (261 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-44403439943 / 1000000000000) (-44403439940 / 1000000000000), orderedInterval (-12486377560 / 1000000000000) (-12486377557 / 1000000000000)))) (orderedInterval (-4616939632 / 1000000000000) (-4616939510 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 0) <| besselDerivativeNearFromState (1117314251256051 / 4000000000000) 0 (IntervalRat.scale (261 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-23379159798 / 1000000000000) (-23379159797 / 1000000000000), orderedInterval (-41581751651 / 1000000000000) (-41581751650 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 0) <| besselDerivativeNearFromState (797368170922083 / 4000000000000) 0 (IntervalRat.scale (261 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-45473352864 / 1000000000000) (-45473277301 / 1000000000000), orderedInterval (33666658605 / 1000000000000) (33666734167 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 0) <| besselDerivativeNearFromState (904130521550757 / 4000000000000) 0 (IntervalRat.scale (261 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (30956894522 / 1000000000000) (30956894523 / 1000000000000), orderedInterval (43037992943 / 1000000000000) (43037992944 / 1000000000000)))) (orderedInterval (-4034684317 / 1000000000000) (-4034677155 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 0) <| besselDerivativeNearFromState (753769768523733 / 4000000000000) 0 (IntervalRat.scale (261 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (38830651975 / 1000000000000) (38830651976 / 1000000000000), orderedInterval (43146323091 / 1000000000000) (43146323092 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 0) <| besselDerivativeNearFromState (665978450034393 / 4000000000000) 0 (IntervalRat.scale (261 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-43260745055 / 1000000000000) (-43260745054 / 1000000000000), orderedInterval (-44053500273 / 1000000000000) (-44053500272 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 0) <| besselDerivativeNearFromState (193026512576907 / 800000000000) 0 (IntervalRat.scale (261 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-8456574880 / 1000000000000) (-8456574879 / 1000000000000), orderedInterval (-50647727152 / 1000000000000) (-50647727151 / 1000000000000)))) (orderedInterval (2707550512 / 1000000000000) (2707550525 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate255_chunkChecks0_2 :
    compactCertificate255.chunkChecks (0 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 0) <| besselDerivativeNearFromState (533921492216529 / 4000000000000) 0 (IntervalRat.scale (261 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (50664863365 / 1000000000000) (50664951096 / 1000000000000), orderedInterval (-47120122860 / 1000000000000) (-47120035128 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 0) <| besselDerivativeNearFromState (452611161970569 / 4000000000000) 0 (IntervalRat.scale (261 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (55841303615 / 1000000000000) (55841303616 / 1000000000000), orderedInterval (49832578211 / 1000000000000) (49832578212 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 0) <| besselDerivativeNearFromState (283223049751107 / 4000000000000) 0 (IntervalRat.scale (261 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (58676251984 / 1000000000000) (58676281061 / 1000000000000), orderedInterval (-74900721041 / 1000000000000) (-74900691964 / 1000000000000)))) (orderedInterval (-9351336814 / 1000000000000) (-9351321807 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 0) <| besselDerivativeNearFromState (152318298113469 / 4000000000000) 0 (IntervalRat.scale (261 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (118669094220 / 1000000000000) (118669094221 / 1000000000000), orderedInterval (49772430557 / 1000000000000) (49772430558 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 0) <| besselDerivativeNearFromState (413573809507407 / 4000000000000) 0 (IntervalRat.scale (261 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-37969036474 / 1000000000000) (-37969036473 / 1000000000000), orderedInterval (-68486942465 / 1000000000000) (-68486942464 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 0) <| besselDerivativeNearFromState (564699679369839 / 4000000000000) 0 (IntervalRat.scale (261 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-37235933030 / 1000000000000) (-37235933029 / 1000000000000), orderedInterval (-55751356287 / 1000000000000) (-55751356286 / 1000000000000)))) (orderedInterval (1523879404 / 1000000000000) (1523879421 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 0) <| besselDerivativeNearFromState (238776950248893 / 4000000000000) 0 (IntervalRat.scale (261 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-73158985811 / 1000000000000) (-73158985810 / 1000000000000), orderedInterval (-72273739196 / 1000000000000) (-72273739195 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 0) <| besselDerivativeNearFromState (970615046261853 / 4000000000000) 0 (IntervalRat.scale (261 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-51189780863 / 1000000000000) (-51189780807 / 1000000000000), orderedInterval (-1675934439 / 1000000000000) (-1675934382 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 0) <| besselDerivativeNearFromState (648325868657427 / 4000000000000) 0 (IntervalRat.scale (261 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-29866127954 / 1000000000000) (-29866124571 / 1000000000000), orderedInterval (55190235337 / 1000000000000) (55190238720 / 1000000000000)))) (orderedInterval (9329589969 / 1000000000000) (9329590645 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate255_chunkChecks0 :
    compactCertificate255.chunkChecks (0 : Fin 5) 0 9 = true :=
  compactCertificate255.chunkChecks_nine_of_three (0 : Fin 5) compactCertificate255_chunkChecks0_0
    compactCertificate255_chunkChecks0_1 compactCertificate255_chunkChecks0_2

theorem compactCertificate255_chunkChecks1_0 :
    compactCertificate255.chunkChecks (1 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 1) <| besselDerivativeNearFromState (261 / 2) 1 (IntervalRat.scale (261 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-42958064120 / 1000000000000) (-42958042975 / 1000000000000), orderedInterval (55236590871 / 1000000000000) (55236612016 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 1) <| besselDerivativeNearFromState (384502837402161 / 4000000000000) 1 (IntervalRat.scale (261 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (37548158294 / 1000000000000) (37548162303 / 1000000000000), orderedInterval (-72396209302 / 1000000000000) (-72396205293 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 1) <| besselDerivativeNearFromState (124340317506513 / 800000000000) 1 (IntervalRat.scale (261 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-48902092533 / 1000000000000) (-48901983672 / 1000000000000), orderedInterval (41443694368 / 1000000000000) (41443803229 / 1000000000000)))) (orderedInterval (24293415658 / 1000000000000) (24293431686 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 1) <| besselDerivativeNearFromState (112196968990227 / 4000000000000) 1 (IntervalRat.scale (261 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-79488791879 / 1000000000000) (-79488791878 / 1000000000000), orderedInterval (-126566434400 / 1000000000000) (-126566434399 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 1) <| besselDerivativeNearFromState (301376840516919 / 4000000000000) 1 (IntervalRat.scale (261 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (61279912038 / 1000000000000) (61279912039 / 1000000000000), orderedInterval (68108153128 / 1000000000000) (68108153129 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 1) <| besselDerivativeNearFromState (818296748148123 / 4000000000000) 1 (IntervalRat.scale (261 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-51041605095 / 1000000000000) (-51041605094 / 1000000000000), orderedInterval (-22384680835 / 1000000000000) (-22384680834 / 1000000000000)))) (orderedInterval (4225446700 / 1000000000000) (4225446718 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 1) <| besselDerivativeNearFromState (602753681034099 / 4000000000000) 1 (IntervalRat.scale (261 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (40695152117 / 1000000000000) (40695152118 / 1000000000000), orderedInterval (50546842319 / 1000000000000) (50546842320 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 1) <| besselDerivativeNearFromState (1032828706059327 / 4000000000000) 1 (IntervalRat.scale (261 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (48767100890 / 1000000000000) (48767100896 / 1000000000000), orderedInterval (9249239095 / 1000000000000) (9249239101 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 1) <| besselDerivativeNearFromState (760776950248893 / 4000000000000) 1 (IntervalRat.scale (261 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (35388300106 / 1000000000000) (35388315359 / 1000000000000), orderedInterval (-45862887793 / 1000000000000) (-45862872539 / 1000000000000)))) (orderedInterval (-2179896561 / 1000000000000) (-2179896010 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate255_chunkChecks1_1 :
    compactCertificate255.chunkChecks (1 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 1) <| besselDerivativeNearFromState (1167227484254739 / 4000000000000) 1 (IntervalRat.scale (261 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-19204401047 / 1000000000000) (-19204401046 / 1000000000000), orderedInterval (-42544561634 / 1000000000000) (-42544561633 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 1) <| besselDerivativeNearFromState (673899102239931 / 4000000000000) 1 (IntervalRat.scale (261 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-23175572159 / 1000000000000) (-23175571228 / 1000000000000), orderedInterval (57004087887 / 1000000000000) (57004088818 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 1) <| besselDerivativeNearFromState (1195845782724279 / 4000000000000) 1 (IntervalRat.scale (261 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-44403439943 / 1000000000000) (-44403439940 / 1000000000000), orderedInterval (-12486377560 / 1000000000000) (-12486377557 / 1000000000000)))) (orderedInterval (18290099304 / 1000000000000) (18290099502 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 1) <| besselDerivativeNearFromState (1117314251256051 / 4000000000000) 1 (IntervalRat.scale (261 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-23379159798 / 1000000000000) (-23379159797 / 1000000000000), orderedInterval (-41581751651 / 1000000000000) (-41581751650 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 1) <| besselDerivativeNearFromState (797368170922083 / 4000000000000) 1 (IntervalRat.scale (261 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-45473352864 / 1000000000000) (-45473277301 / 1000000000000), orderedInterval (33666658605 / 1000000000000) (33666734167 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 1) <| besselDerivativeNearFromState (904130521550757 / 4000000000000) 1 (IntervalRat.scale (261 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (30956894522 / 1000000000000) (30956894523 / 1000000000000), orderedInterval (43037992943 / 1000000000000) (43037992944 / 1000000000000)))) (orderedInterval (6092607609 / 1000000000000) (6092618550 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 1) <| besselDerivativeNearFromState (753769768523733 / 4000000000000) 1 (IntervalRat.scale (261 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (38830651975 / 1000000000000) (38830651976 / 1000000000000), orderedInterval (43146323091 / 1000000000000) (43146323092 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 1) <| besselDerivativeNearFromState (665978450034393 / 4000000000000) 1 (IntervalRat.scale (261 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-43260745055 / 1000000000000) (-43260745054 / 1000000000000), orderedInterval (-44053500273 / 1000000000000) (-44053500272 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 1) <| besselDerivativeNearFromState (193026512576907 / 800000000000) 1 (IntervalRat.scale (261 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-8456574880 / 1000000000000) (-8456574879 / 1000000000000), orderedInterval (-50647727152 / 1000000000000) (-50647727151 / 1000000000000)))) (orderedInterval (1538212114 / 1000000000000) (1538212133 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate255_chunkChecks1_2 :
    compactCertificate255.chunkChecks (1 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 1) <| besselDerivativeNearFromState (533921492216529 / 4000000000000) 1 (IntervalRat.scale (261 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (50664863365 / 1000000000000) (50664951096 / 1000000000000), orderedInterval (-47120122860 / 1000000000000) (-47120035128 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 1) <| besselDerivativeNearFromState (452611161970569 / 4000000000000) 1 (IntervalRat.scale (261 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (55841303615 / 1000000000000) (55841303616 / 1000000000000), orderedInterval (49832578211 / 1000000000000) (49832578212 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 1) <| besselDerivativeNearFromState (283223049751107 / 4000000000000) 1 (IntervalRat.scale (261 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (58676251984 / 1000000000000) (58676281061 / 1000000000000), orderedInterval (-74900721041 / 1000000000000) (-74900691964 / 1000000000000)))) (orderedInterval (3937592829 / 1000000000000) (3937607722 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 1) <| besselDerivativeNearFromState (152318298113469 / 4000000000000) 1 (IntervalRat.scale (261 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (118669094220 / 1000000000000) (118669094221 / 1000000000000), orderedInterval (49772430557 / 1000000000000) (49772430558 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 1) <| besselDerivativeNearFromState (413573809507407 / 4000000000000) 1 (IntervalRat.scale (261 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-37969036474 / 1000000000000) (-37969036473 / 1000000000000), orderedInterval (-68486942465 / 1000000000000) (-68486942464 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 1) <| besselDerivativeNearFromState (564699679369839 / 4000000000000) 1 (IntervalRat.scale (261 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-37235933030 / 1000000000000) (-37235933029 / 1000000000000), orderedInterval (-55751356287 / 1000000000000) (-55751356286 / 1000000000000)))) (orderedInterval (5585071503 / 1000000000000) (5585071518 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 1) <| besselDerivativeNearFromState (238776950248893 / 4000000000000) 1 (IntervalRat.scale (261 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-73158985811 / 1000000000000) (-73158985810 / 1000000000000), orderedInterval (-72273739196 / 1000000000000) (-72273739195 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 1) <| besselDerivativeNearFromState (970615046261853 / 4000000000000) 1 (IntervalRat.scale (261 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-51189780863 / 1000000000000) (-51189780807 / 1000000000000), orderedInterval (-1675934439 / 1000000000000) (-1675934382 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 1) <| besselDerivativeNearFromState (648325868657427 / 4000000000000) 1 (IntervalRat.scale (261 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-29866127954 / 1000000000000) (-29866124571 / 1000000000000), orderedInterval (55190235337 / 1000000000000) (55190238720 / 1000000000000)))) (orderedInterval (-12806764210 / 1000000000000) (-12806763362 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate255_chunkChecks1 :
    compactCertificate255.chunkChecks (1 : Fin 5) 0 9 = true :=
  compactCertificate255.chunkChecks_nine_of_three (1 : Fin 5) compactCertificate255_chunkChecks1_0
    compactCertificate255_chunkChecks1_1 compactCertificate255_chunkChecks1_2

theorem compactCertificate255_chunkChecks2_0 :
    compactCertificate255.chunkChecks (2 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 2) <| besselDerivativeNearFromState (261 / 2) 2 (IntervalRat.scale (261 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-42958064120 / 1000000000000) (-42958042975 / 1000000000000), orderedInterval (55236590871 / 1000000000000) (55236612016 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 2) <| besselDerivativeNearFromState (384502837402161 / 4000000000000) 2 (IntervalRat.scale (261 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (37548158294 / 1000000000000) (37548162303 / 1000000000000), orderedInterval (-72396209302 / 1000000000000) (-72396205293 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 2) <| besselDerivativeNearFromState (124340317506513 / 800000000000) 2 (IntervalRat.scale (261 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-48902092533 / 1000000000000) (-48901983672 / 1000000000000), orderedInterval (41443694368 / 1000000000000) (41443803229 / 1000000000000)))) (orderedInterval (20721576516 / 1000000000000) (20721594114 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 2) <| besselDerivativeNearFromState (112196968990227 / 4000000000000) 2 (IntervalRat.scale (261 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-79488791879 / 1000000000000) (-79488791878 / 1000000000000), orderedInterval (-126566434400 / 1000000000000) (-126566434399 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 2) <| besselDerivativeNearFromState (301376840516919 / 4000000000000) 2 (IntervalRat.scale (261 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (61279912038 / 1000000000000) (61279912039 / 1000000000000), orderedInterval (68108153128 / 1000000000000) (68108153129 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 2) <| besselDerivativeNearFromState (818296748148123 / 4000000000000) 2 (IntervalRat.scale (261 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-51041605095 / 1000000000000) (-51041605094 / 1000000000000), orderedInterval (-22384680835 / 1000000000000) (-22384680834 / 1000000000000)))) (orderedInterval (-9734878415 / 1000000000000) (-9734878390 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 2) <| besselDerivativeNearFromState (602753681034099 / 4000000000000) 2 (IntervalRat.scale (261 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (40695152117 / 1000000000000) (40695152118 / 1000000000000), orderedInterval (50546842319 / 1000000000000) (50546842320 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 2) <| besselDerivativeNearFromState (1032828706059327 / 4000000000000) 2 (IntervalRat.scale (261 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (48767100890 / 1000000000000) (48767100896 / 1000000000000), orderedInterval (9249239095 / 1000000000000) (9249239101 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 2) <| besselDerivativeNearFromState (760776950248893 / 4000000000000) 2 (IntervalRat.scale (261 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (35388300106 / 1000000000000) (35388315359 / 1000000000000), orderedInterval (-45862887793 / 1000000000000) (-45862872539 / 1000000000000)))) (orderedInterval (4088655580 / 1000000000000) (4088656391 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate255_chunkChecks2_1 :
    compactCertificate255.chunkChecks (2 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 2) <| besselDerivativeNearFromState (1167227484254739 / 4000000000000) 2 (IntervalRat.scale (261 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-19204401047 / 1000000000000) (-19204401046 / 1000000000000), orderedInterval (-42544561634 / 1000000000000) (-42544561633 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 2) <| besselDerivativeNearFromState (673899102239931 / 4000000000000) 2 (IntervalRat.scale (261 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-23175572159 / 1000000000000) (-23175571228 / 1000000000000), orderedInterval (57004087887 / 1000000000000) (57004088818 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 2) <| besselDerivativeNearFromState (1195845782724279 / 4000000000000) 2 (IntervalRat.scale (261 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-44403439943 / 1000000000000) (-44403439940 / 1000000000000), orderedInterval (-12486377560 / 1000000000000) (-12486377557 / 1000000000000)))) (orderedInterval (18787425242 / 1000000000000) (18787425591 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 2) <| besselDerivativeNearFromState (1117314251256051 / 4000000000000) 2 (IntervalRat.scale (261 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-23379159798 / 1000000000000) (-23379159797 / 1000000000000), orderedInterval (-41581751651 / 1000000000000) (-41581751650 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 2) <| besselDerivativeNearFromState (797368170922083 / 4000000000000) 2 (IntervalRat.scale (261 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-45473352864 / 1000000000000) (-45473277301 / 1000000000000), orderedInterval (33666658605 / 1000000000000) (33666734167 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 2) <| besselDerivativeNearFromState (904130521550757 / 4000000000000) 2 (IntervalRat.scale (261 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (30956894522 / 1000000000000) (30956894523 / 1000000000000), orderedInterval (43037992943 / 1000000000000) (43037992944 / 1000000000000)))) (orderedInterval (8523116285 / 1000000000000) (8523133084 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 2) <| besselDerivativeNearFromState (753769768523733 / 4000000000000) 2 (IntervalRat.scale (261 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (38830651975 / 1000000000000) (38830651976 / 1000000000000), orderedInterval (43146323091 / 1000000000000) (43146323092 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 2) <| besselDerivativeNearFromState (665978450034393 / 4000000000000) 2 (IntervalRat.scale (261 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-43260745055 / 1000000000000) (-43260745054 / 1000000000000), orderedInterval (-44053500273 / 1000000000000) (-44053500272 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 2) <| besselDerivativeNearFromState (193026512576907 / 800000000000) 2 (IntervalRat.scale (261 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-8456574880 / 1000000000000) (-8456574879 / 1000000000000), orderedInterval (-50647727152 / 1000000000000) (-50647727151 / 1000000000000)))) (orderedInterval (-4236291037 / 1000000000000) (-4236291009 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate255_chunkChecks2_2 :
    compactCertificate255.chunkChecks (2 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 2) <| besselDerivativeNearFromState (533921492216529 / 4000000000000) 2 (IntervalRat.scale (261 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (50664863365 / 1000000000000) (50664951096 / 1000000000000), orderedInterval (-47120122860 / 1000000000000) (-47120035128 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 2) <| besselDerivativeNearFromState (452611161970569 / 4000000000000) 2 (IntervalRat.scale (261 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (55841303615 / 1000000000000) (55841303616 / 1000000000000), orderedInterval (49832578211 / 1000000000000) (49832578212 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 2) <| besselDerivativeNearFromState (283223049751107 / 4000000000000) 2 (IntervalRat.scale (261 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (58676251984 / 1000000000000) (58676281061 / 1000000000000), orderedInterval (-74900721041 / 1000000000000) (-74900691964 / 1000000000000)))) (orderedInterval (10258849043 / 1000000000000) (10258864141 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 2) <| besselDerivativeNearFromState (152318298113469 / 4000000000000) 2 (IntervalRat.scale (261 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (118669094220 / 1000000000000) (118669094221 / 1000000000000), orderedInterval (49772430557 / 1000000000000) (49772430558 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 2) <| besselDerivativeNearFromState (413573809507407 / 4000000000000) 2 (IntervalRat.scale (261 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-37969036474 / 1000000000000) (-37969036473 / 1000000000000), orderedInterval (-68486942465 / 1000000000000) (-68486942464 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 2) <| besselDerivativeNearFromState (564699679369839 / 4000000000000) 2 (IntervalRat.scale (261 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-37235933030 / 1000000000000) (-37235933029 / 1000000000000), orderedInterval (-55751356287 / 1000000000000) (-55751356286 / 1000000000000)))) (orderedInterval (-3736622805 / 1000000000000) (-3736622790 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 2) <| besselDerivativeNearFromState (238776950248893 / 4000000000000) 2 (IntervalRat.scale (261 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-73158985811 / 1000000000000) (-73158985810 / 1000000000000), orderedInterval (-72273739196 / 1000000000000) (-72273739195 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 2) <| besselDerivativeNearFromState (970615046261853 / 4000000000000) 2 (IntervalRat.scale (261 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-51189780863 / 1000000000000) (-51189780807 / 1000000000000), orderedInterval (-1675934439 / 1000000000000) (-1675934382 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 2) <| besselDerivativeNearFromState (648325868657427 / 4000000000000) 2 (IntervalRat.scale (261 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-29866127954 / 1000000000000) (-29866124571 / 1000000000000), orderedInterval (55190235337 / 1000000000000) (55190238720 / 1000000000000)))) (orderedInterval (-22860553619 / 1000000000000) (-22860552542 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate255_chunkChecks2 :
    compactCertificate255.chunkChecks (2 : Fin 5) 0 9 = true :=
  compactCertificate255.chunkChecks_nine_of_three (2 : Fin 5) compactCertificate255_chunkChecks2_0
    compactCertificate255_chunkChecks2_1 compactCertificate255_chunkChecks2_2

theorem compactCertificate255_chunkChecks3_0 :
    compactCertificate255.chunkChecks (3 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 3) <| besselDerivativeNearFromState (261 / 2) 3 (IntervalRat.scale (261 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-42958064120 / 1000000000000) (-42958042975 / 1000000000000), orderedInterval (55236590871 / 1000000000000) (55236612016 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 3) <| besselDerivativeNearFromState (384502837402161 / 4000000000000) 3 (IntervalRat.scale (261 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (37548158294 / 1000000000000) (37548162303 / 1000000000000), orderedInterval (-72396209302 / 1000000000000) (-72396205293 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 3) <| besselDerivativeNearFromState (124340317506513 / 800000000000) 3 (IntervalRat.scale (261 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-48902092533 / 1000000000000) (-48901983672 / 1000000000000), orderedInterval (41443694368 / 1000000000000) (41443803229 / 1000000000000)))) (orderedInterval (-25890201440 / 1000000000000) (-25890182106 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 3) <| besselDerivativeNearFromState (112196968990227 / 4000000000000) 3 (IntervalRat.scale (261 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-79488791879 / 1000000000000) (-79488791878 / 1000000000000), orderedInterval (-126566434400 / 1000000000000) (-126566434399 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 3) <| besselDerivativeNearFromState (301376840516919 / 4000000000000) 3 (IntervalRat.scale (261 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (61279912038 / 1000000000000) (61279912039 / 1000000000000), orderedInterval (68108153128 / 1000000000000) (68108153129 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 3) <| besselDerivativeNearFromState (818296748148123 / 4000000000000) 3 (IntervalRat.scale (261 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-51041605095 / 1000000000000) (-51041605094 / 1000000000000), orderedInterval (-22384680835 / 1000000000000) (-22384680834 / 1000000000000)))) (orderedInterval (-6547614946 / 1000000000000) (-6547614908 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 3) <| besselDerivativeNearFromState (602753681034099 / 4000000000000) 3 (IntervalRat.scale (261 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (40695152117 / 1000000000000) (40695152118 / 1000000000000), orderedInterval (50546842319 / 1000000000000) (50546842320 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 3) <| besselDerivativeNearFromState (1032828706059327 / 4000000000000) 3 (IntervalRat.scale (261 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (48767100890 / 1000000000000) (48767100896 / 1000000000000), orderedInterval (9249239095 / 1000000000000) (9249239101 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 3) <| besselDerivativeNearFromState (760776950248893 / 4000000000000) 3 (IntervalRat.scale (261 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (35388300106 / 1000000000000) (35388315359 / 1000000000000), orderedInterval (-45862887793 / 1000000000000) (-45862872539 / 1000000000000)))) (orderedInterval (5609660593 / 1000000000000) (5609661784 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate255_chunkChecks3_1 :
    compactCertificate255.chunkChecks (3 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 3) <| besselDerivativeNearFromState (1167227484254739 / 4000000000000) 3 (IntervalRat.scale (261 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-19204401047 / 1000000000000) (-19204401046 / 1000000000000), orderedInterval (-42544561634 / 1000000000000) (-42544561633 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 3) <| besselDerivativeNearFromState (673899102239931 / 4000000000000) 3 (IntervalRat.scale (261 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-23175572159 / 1000000000000) (-23175571228 / 1000000000000), orderedInterval (57004087887 / 1000000000000) (57004088818 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 3) <| besselDerivativeNearFromState (1195845782724279 / 4000000000000) 3 (IntervalRat.scale (261 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-44403439943 / 1000000000000) (-44403439940 / 1000000000000), orderedInterval (-12486377560 / 1000000000000) (-12486377557 / 1000000000000)))) (orderedInterval (-72408972091 / 1000000000000) (-72408971431 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 3) <| besselDerivativeNearFromState (1117314251256051 / 4000000000000) 3 (IntervalRat.scale (261 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-23379159798 / 1000000000000) (-23379159797 / 1000000000000), orderedInterval (-41581751651 / 1000000000000) (-41581751650 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 3) <| besselDerivativeNearFromState (797368170922083 / 4000000000000) 3 (IntervalRat.scale (261 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-45473352864 / 1000000000000) (-45473277301 / 1000000000000), orderedInterval (33666658605 / 1000000000000) (33666734167 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 3) <| besselDerivativeNearFromState (904130521550757 / 4000000000000) 3 (IntervalRat.scale (261 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (30956894522 / 1000000000000) (30956894523 / 1000000000000), orderedInterval (43037992943 / 1000000000000) (43037992944 / 1000000000000)))) (orderedInterval (-17641938038 / 1000000000000) (-17641912372 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 3) <| besselDerivativeNearFromState (753769768523733 / 4000000000000) 3 (IntervalRat.scale (261 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (38830651975 / 1000000000000) (38830651976 / 1000000000000), orderedInterval (43146323091 / 1000000000000) (43146323092 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 3) <| besselDerivativeNearFromState (665978450034393 / 4000000000000) 3 (IntervalRat.scale (261 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-43260745055 / 1000000000000) (-43260745054 / 1000000000000), orderedInterval (-44053500273 / 1000000000000) (-44053500272 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 3) <| besselDerivativeNearFromState (193026512576907 / 800000000000) 3 (IntervalRat.scale (261 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-8456574880 / 1000000000000) (-8456574879 / 1000000000000), orderedInterval (-50647727152 / 1000000000000) (-50647727151 / 1000000000000)))) (orderedInterval (1493268554 / 1000000000000) (1493268596 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate255_chunkChecks3_2 :
    compactCertificate255.chunkChecks (3 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 3) <| besselDerivativeNearFromState (533921492216529 / 4000000000000) 3 (IntervalRat.scale (261 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (50664863365 / 1000000000000) (50664951096 / 1000000000000), orderedInterval (-47120122860 / 1000000000000) (-47120035128 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 3) <| besselDerivativeNearFromState (452611161970569 / 4000000000000) 3 (IntervalRat.scale (261 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (55841303615 / 1000000000000) (55841303616 / 1000000000000), orderedInterval (49832578211 / 1000000000000) (49832578212 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 3) <| besselDerivativeNearFromState (283223049751107 / 4000000000000) 3 (IntervalRat.scale (261 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (58676251984 / 1000000000000) (58676281061 / 1000000000000), orderedInterval (-74900721041 / 1000000000000) (-74900691964 / 1000000000000)))) (orderedInterval (-5912504285 / 1000000000000) (-5912488981 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 3) <| besselDerivativeNearFromState (152318298113469 / 4000000000000) 3 (IntervalRat.scale (261 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (118669094220 / 1000000000000) (118669094221 / 1000000000000), orderedInterval (49772430557 / 1000000000000) (49772430558 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 3) <| besselDerivativeNearFromState (413573809507407 / 4000000000000) 3 (IntervalRat.scale (261 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-37969036474 / 1000000000000) (-37969036473 / 1000000000000), orderedInterval (-68486942465 / 1000000000000) (-68486942464 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 3) <| besselDerivativeNearFromState (564699679369839 / 4000000000000) 3 (IntervalRat.scale (261 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-37235933030 / 1000000000000) (-37235933029 / 1000000000000), orderedInterval (-55751356287 / 1000000000000) (-55751356286 / 1000000000000)))) (orderedInterval (-6130295315 / 1000000000000) (-6130295299 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 3) <| besselDerivativeNearFromState (238776950248893 / 4000000000000) 3 (IntervalRat.scale (261 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-73158985811 / 1000000000000) (-73158985810 / 1000000000000), orderedInterval (-72273739196 / 1000000000000) (-72273739195 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 3) <| besselDerivativeNearFromState (970615046261853 / 4000000000000) 3 (IntervalRat.scale (261 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-51189780863 / 1000000000000) (-51189780807 / 1000000000000), orderedInterval (-1675934439 / 1000000000000) (-1675934382 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 3) <| besselDerivativeNearFromState (648325868657427 / 4000000000000) 3 (IntervalRat.scale (261 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-29866127954 / 1000000000000) (-29866124571 / 1000000000000), orderedInterval (55190235337 / 1000000000000) (55190238720 / 1000000000000)))) (orderedInterval (19178323003 / 1000000000000) (19178324373 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate255_chunkChecks3 :
    compactCertificate255.chunkChecks (3 : Fin 5) 0 9 = true :=
  compactCertificate255.chunkChecks_nine_of_three (3 : Fin 5) compactCertificate255_chunkChecks3_0
    compactCertificate255_chunkChecks3_1 compactCertificate255_chunkChecks3_2

theorem compactCertificate255_chunkChecks4_0 :
    compactCertificate255.chunkChecks (4 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 4) <| besselDerivativeNearFromState (261 / 2) 4 (IntervalRat.scale (261 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-42958064120 / 1000000000000) (-42958042975 / 1000000000000), orderedInterval (55236590871 / 1000000000000) (55236612016 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 4) <| besselDerivativeNearFromState (384502837402161 / 4000000000000) 4 (IntervalRat.scale (261 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (37548158294 / 1000000000000) (37548162303 / 1000000000000), orderedInterval (-72396209302 / 1000000000000) (-72396205293 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 4) <| besselDerivativeNearFromState (124340317506513 / 800000000000) 4 (IntervalRat.scale (261 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-48902092533 / 1000000000000) (-48901983672 / 1000000000000), orderedInterval (41443694368 / 1000000000000) (41443803229 / 1000000000000)))) (orderedInterval (-22300019049 / 1000000000000) (-22299997496 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 4) <| besselDerivativeNearFromState (112196968990227 / 4000000000000) 4 (IntervalRat.scale (261 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-79488791879 / 1000000000000) (-79488791878 / 1000000000000), orderedInterval (-126566434400 / 1000000000000) (-126566434399 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 4) <| besselDerivativeNearFromState (301376840516919 / 4000000000000) 4 (IntervalRat.scale (261 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (61279912038 / 1000000000000) (61279912039 / 1000000000000), orderedInterval (68108153128 / 1000000000000) (68108153129 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 4) <| besselDerivativeNearFromState (818296748148123 / 4000000000000) 4 (IntervalRat.scale (261 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-51041605095 / 1000000000000) (-51041605094 / 1000000000000), orderedInterval (-22384680835 / 1000000000000) (-22384680834 / 1000000000000)))) (orderedInterval (22262717879 / 1000000000000) (22262717937 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 4) <| besselDerivativeNearFromState (602753681034099 / 4000000000000) 4 (IntervalRat.scale (261 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (40695152117 / 1000000000000) (40695152118 / 1000000000000), orderedInterval (50546842319 / 1000000000000) (50546842320 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 4) <| besselDerivativeNearFromState (1032828706059327 / 4000000000000) 4 (IntervalRat.scale (261 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (48767100890 / 1000000000000) (48767100896 / 1000000000000), orderedInterval (9249239095 / 1000000000000) (9249239101 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 4) <| besselDerivativeNearFromState (760776950248893 / 4000000000000) 4 (IntervalRat.scale (261 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (35388300106 / 1000000000000) (35388315359 / 1000000000000), orderedInterval (-45862887793 / 1000000000000) (-45862872539 / 1000000000000)))) (orderedInterval (-19280039844 / 1000000000000) (-19280038084 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate255_chunkChecks4_1 :
    compactCertificate255.chunkChecks (4 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 4) <| besselDerivativeNearFromState (1167227484254739 / 4000000000000) 4 (IntervalRat.scale (261 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-19204401047 / 1000000000000) (-19204401046 / 1000000000000), orderedInterval (-42544561634 / 1000000000000) (-42544561633 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 4) <| besselDerivativeNearFromState (673899102239931 / 4000000000000) 4 (IntervalRat.scale (261 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-23175572159 / 1000000000000) (-23175571228 / 1000000000000), orderedInterval (57004087887 / 1000000000000) (57004088818 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 4) <| besselDerivativeNearFromState (1195845782724279 / 4000000000000) 4 (IntervalRat.scale (261 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-44403439943 / 1000000000000) (-44403439940 / 1000000000000), orderedInterval (-12486377560 / 1000000000000) (-12486377557 / 1000000000000)))) (orderedInterval (-92209410019 / 1000000000000) (-92209408690 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 4) <| besselDerivativeNearFromState (1117314251256051 / 4000000000000) 4 (IntervalRat.scale (261 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-23379159798 / 1000000000000) (-23379159797 / 1000000000000), orderedInterval (-41581751651 / 1000000000000) (-41581751650 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 4) <| besselDerivativeNearFromState (797368170922083 / 4000000000000) 4 (IntervalRat.scale (261 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-45473352864 / 1000000000000) (-45473277301 / 1000000000000), orderedInterval (33666658605 / 1000000000000) (33666734167 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 4) <| besselDerivativeNearFromState (904130521550757 / 4000000000000) 4 (IntervalRat.scale (261 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (30956894522 / 1000000000000) (30956894523 / 1000000000000), orderedInterval (43037992943 / 1000000000000) (43037992944 / 1000000000000)))) (orderedInterval (-15691364115 / 1000000000000) (-15691324701 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 4) <| besselDerivativeNearFromState (753769768523733 / 4000000000000) 4 (IntervalRat.scale (261 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (38830651975 / 1000000000000) (38830651976 / 1000000000000), orderedInterval (43146323091 / 1000000000000) (43146323092 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 4) <| besselDerivativeNearFromState (665978450034393 / 4000000000000) 4 (IntervalRat.scale (261 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-43260745055 / 1000000000000) (-43260745054 / 1000000000000), orderedInterval (-44053500273 / 1000000000000) (-44053500272 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 4) <| besselDerivativeNearFromState (193026512576907 / 800000000000) 4 (IntervalRat.scale (261 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-8456574880 / 1000000000000) (-8456574879 / 1000000000000), orderedInterval (-50647727152 / 1000000000000) (-50647727151 / 1000000000000)))) (orderedInterval (5955381398 / 1000000000000) (5955381465 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate255_chunkChecks4_2 :
    compactCertificate255.chunkChecks (4 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 4) <| besselDerivativeNearFromState (533921492216529 / 4000000000000) 4 (IntervalRat.scale (261 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (50664863365 / 1000000000000) (50664951096 / 1000000000000), orderedInterval (-47120122860 / 1000000000000) (-47120035128 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 4) <| besselDerivativeNearFromState (452611161970569 / 4000000000000) 4 (IntervalRat.scale (261 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (55841303615 / 1000000000000) (55841303616 / 1000000000000), orderedInterval (49832578211 / 1000000000000) (49832578212 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 4) <| besselDerivativeNearFromState (283223049751107 / 4000000000000) 4 (IntervalRat.scale (261 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (58676251984 / 1000000000000) (58676281061 / 1000000000000), orderedInterval (-74900721041 / 1000000000000) (-74900691964 / 1000000000000)))) (orderedInterval (-10396414197 / 1000000000000) (-10396398503 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 4) <| besselDerivativeNearFromState (152318298113469 / 4000000000000) 4 (IntervalRat.scale (261 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (118669094220 / 1000000000000) (118669094221 / 1000000000000), orderedInterval (49772430557 / 1000000000000) (49772430558 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 4) <| besselDerivativeNearFromState (413573809507407 / 4000000000000) 4 (IntervalRat.scale (261 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-37969036474 / 1000000000000) (-37969036473 / 1000000000000), orderedInterval (-68486942465 / 1000000000000) (-68486942464 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 4) <| besselDerivativeNearFromState (564699679369839 / 4000000000000) 4 (IntervalRat.scale (261 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-37235933030 / 1000000000000) (-37235933029 / 1000000000000), orderedInterval (-55751356287 / 1000000000000) (-55751356286 / 1000000000000)))) (orderedInterval (4325664635 / 1000000000000) (4325664651 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 4) <| besselDerivativeNearFromState (238776950248893 / 4000000000000) 4 (IntervalRat.scale (261 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-73158985811 / 1000000000000) (-73158985810 / 1000000000000), orderedInterval (-72273739196 / 1000000000000) (-72273739195 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 4) <| besselDerivativeNearFromState (970615046261853 / 4000000000000) 4 (IntervalRat.scale (261 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-51189780863 / 1000000000000) (-51189780807 / 1000000000000), orderedInterval (-1675934439 / 1000000000000) (-1675934382 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 4) <| besselDerivativeNearFromState (648325868657427 / 4000000000000) 4 (IntervalRat.scale (261 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-29866127954 / 1000000000000) (-29866124571 / 1000000000000), orderedInterval (55190235337 / 1000000000000) (55190238720 / 1000000000000)))) (orderedInterval (62830324441 / 1000000000000) (62830326211 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate255_chunkChecks4 :
    compactCertificate255.chunkChecks (4 : Fin 5) 0 9 = true :=
  compactCertificate255.chunkChecks_nine_of_three (4 : Fin 5) compactCertificate255_chunkChecks4_0
    compactCertificate255_chunkChecks4_1 compactCertificate255_chunkChecks4_2

theorem compactCertificate255_chunks :
    ∀ r : Fin 5, ∀ b, compactCertificate255.chunkCheck r b = true :=
  compactCertificate255.chunkChecks_all (by
    intro r
    fin_cases r
    · exact compactCertificate255_chunkChecks0
    · exact compactCertificate255_chunkChecks1
    · exact compactCertificate255_chunkChecks2
    · exact compactCertificate255_chunkChecks3
    · exact compactCertificate255_chunkChecks4)

theorem compactCertificate255_coefficient0 :
    compactCertificate255.coefficientCheck (0 : Fin 5) = true := by
  norm_num [CompactCertificate.coefficientCheck, intervalFinSumHull,
    compactCertificate255, rationalIntervalSubset, orderedInterval, Fin.sum_univ_succ]

theorem compactCertificate255_coefficient1 :
    compactCertificate255.coefficientCheck (1 : Fin 5) = true := by
  norm_num [CompactCertificate.coefficientCheck, intervalFinSumHull,
    compactCertificate255, rationalIntervalSubset, orderedInterval, Fin.sum_univ_succ]

theorem compactCertificate255_coefficient2 :
    compactCertificate255.coefficientCheck (2 : Fin 5) = true := by
  norm_num [CompactCertificate.coefficientCheck, intervalFinSumHull,
    compactCertificate255, rationalIntervalSubset, orderedInterval, Fin.sum_univ_succ]

theorem compactCertificate255_coefficient3 :
    compactCertificate255.coefficientCheck (3 : Fin 5) = true := by
  norm_num [CompactCertificate.coefficientCheck, intervalFinSumHull,
    compactCertificate255, rationalIntervalSubset, orderedInterval, Fin.sum_univ_succ]

theorem compactCertificate255_coefficient4 :
    compactCertificate255.coefficientCheck (4 : Fin 5) = true := by
  norm_num [CompactCertificate.coefficientCheck, intervalFinSumHull,
    compactCertificate255, rationalIntervalSubset, orderedInterval, Fin.sum_univ_succ]

theorem compactCertificate255_coefficients : ∀ r : Fin 5,
    compactCertificate255.coefficientCheck r = true := by
  intro r
  fin_cases r
  · exact compactCertificate255_coefficient0
  · exact compactCertificate255_coefficient1
  · exact compactCertificate255_coefficient2
  · exact compactCertificate255_coefficient3
  · exact compactCertificate255_coefficient4

theorem compactCertificate255_lower : (1 : ℚ) ≤ compactCertificate255.output.lo := by
  norm_num [CompactCertificate.output, CompactCertificate.interval,
    CompactCertificate.coefficientTargetNat, compactCertificate255, dualConstant,
    intervalTaylorSum, intervalPow, intervalSub, intervalMaxAbs, widenInterval,
    rationalErrorInterval, orderedInterval, IntervalRat.add, IntervalRat.mul, IntervalRat.scale,
    IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4]

theorem compactCertificate255_proves {t : ℝ} (ht : t ∈ compactCertificate255.interval) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t :=
  compactCertificate255.proves compactCertificate255_states compactCertificate255_chunks
    compactCertificate255_coefficients compactCertificate255_lower ht

end Erdos232
