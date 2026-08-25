/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, OpenAI Codex
-/
import ErdosProblems.Erdos232.CompactBase

open LeanCert.Core
namespace Erdos232

def compactCertificate254 : CompactCertificate where
  left := 129
  right := 130
  center := 259 / 2
  grid := fun i =>
    match i.val with
    | 0 => 41
    | 1 => 30
    | 2 => 49
    | 3 => 9
    | 4 => 24
    | 5 => 65
    | 6 => 48
    | 7 => 82
    | 8 => 60
    | 9 => 92
    | 10 => 53
    | 11 => 94
    | 12 => 88
    | 13 => 63
    | 14 => 71
    | 15 => 60
    | 16 => 53
    | 17 => 76
    | 18 => 42
    | 19 => 36
    | 20 => 22
    | 21 => 12
    | 22 => 33
    | 23 => 45
    | 24 => 19
    | 25 => 77
    | _ => 51
  point := fun i =>
    match i.val with
    | 0 => 259 / 2
    | 1 => 381556455506359 / 4000000000000
    | 2 => 123387518138647 / 800000000000
    | 3 => 111337222101413 / 4000000000000
    | 4 => 299067439440161 / 4000000000000
    | 5 => 812026274982237 / 4000000000000
    | 6 => 598134878880581 / 4000000000000
    | 7 => 1024914309844313 / 4000000000000
    | 8 => 754947241817867 / 4000000000000
    | 9 => 1158283212344741 / 4000000000000
    | 10 => 668735124444989 / 4000000000000
    | 11 => 1186682213508001 / 4000000000000
    | 12 => 1108752456227269 / 4000000000000
    | 13 => 791258069995477 / 4000000000000
    | 14 => 897202318320483 / 4000000000000
    | 15 => 747993754971827 / 4000000000000
    | 16 => 660875166892367 / 4000000000000
    | 17 => 191547382212333 / 800000000000
    | 18 => 529830139785751 / 4000000000000
    | 19 => 449142877204511 / 4000000000000
    | 20 => 281052758182133 / 4000000000000
    | 21 => 151151108089611 / 4000000000000
    | 22 => 410404661541833 / 4000000000000
    | 23 => 560372478761641 / 4000000000000
    | 24 => 236947241817867 / 4000000000000
    | 25 => 963177383072107 / 4000000000000
    | _ => 643357854338213 / 4000000000000
  state := fun i =>
    match i.val with
    | 0 => (orderedInterval (-69819468250 / 1000000000000) (-69819468240 / 1000000000000), orderedInterval (-6148267462 / 1000000000000) (-6148267452 / 1000000000000))
    | 1 => (orderedInterval (76610273151 / 1000000000000) (76610276205 / 1000000000000), orderedInterval (-28769162984 / 1000000000000) (-28769159931 / 1000000000000))
    | 2 => (orderedInterval (-56691150762 / 1000000000000) (-56691150761 / 1000000000000), orderedInterval (-30043913411 / 1000000000000) (-30043913410 / 1000000000000))
    | 3 => (orderedInterval (-50556292594 / 1000000000000) (-50556292593 / 1000000000000), orderedInterval (-141635764508 / 1000000000000) (-141635764507 / 1000000000000))
    | 4 => (orderedInterval (14004818371 / 1000000000000) (14004818372 / 1000000000000), orderedInterval (91113686191 / 1000000000000) (91113686192 / 1000000000000))
    | 5 => (orderedInterval (22433395389 / 1000000000000) (22433396416 / 1000000000000), orderedInterval (-51365151927 / 1000000000000) (-51365150900 / 1000000000000))
    | 6 => (orderedInterval (-30024085113 / 1000000000000) (-30024082153 / 1000000000000), orderedInterval (58030814386 / 1000000000000) (58030817346 / 1000000000000))
    | 7 => (orderedInterval (-28025865739 / 1000000000000) (-28025859809 / 1000000000000), orderedInterval (41275194208 / 1000000000000) (41275200139 / 1000000000000))
    | 8 => (orderedInterval (49669750927 / 1000000000000) (49669750928 / 1000000000000), orderedInterval (29967686231 / 1000000000000) (29967686232 / 1000000000000))
    | 9 => (orderedInterval (45526822562 / 1000000000000) (45526822565 / 1000000000000), orderedInterval (11137443380 / 1000000000000) (11137443384 / 1000000000000))
    | 10 => (orderedInterval (-61356645747 / 1000000000000) (-61356645736 / 1000000000000), orderedInterval (-6392919757 / 1000000000000) (-6392919746 / 1000000000000))
    | 11 => (orderedInterval (38873778085 / 1000000000000) (38873846559 / 1000000000000), orderedInterval (-25258934077 / 1000000000000) (-25258865603 / 1000000000000))
    | 12 => (orderedInterval (47843651694 / 1000000000000) (47843651746 / 1000000000000), orderedInterval (2686401773 / 1000000000000) (2686401825 / 1000000000000))
    | 13 => (orderedInterval (-35624735973 / 1000000000000) (-35624735972 / 1000000000000), orderedInterval (-44059094545 / 1000000000000) (-44059094544 / 1000000000000))
    | 14 => (orderedInterval (-47700684772 / 1000000000000) (-47700667185 / 1000000000000), orderedInterval (23831524538 / 1000000000000) (23831542125 / 1000000000000))
    | 15 => (orderedInterval (-38138389888 / 1000000000000) (-38138364022 / 1000000000000), orderedInterval (44259385770 / 1000000000000) (44259411636 / 1000000000000))
    | 16 => (orderedInterval (29813057490 / 1000000000000) (29813060972 / 1000000000000), orderedInterval (-54536374054 / 1000000000000) (-54536370571 / 1000000000000))
    | 17 => (orderedInterval (51236668650 / 1000000000000) (51236668667 / 1000000000000), orderedInterval (5693733669 / 1000000000000) (5693733686 / 1000000000000))
    | 18 => (orderedInterval (66708546741 / 1000000000000) (66708546742 / 1000000000000), orderedInterval (18620354663 / 1000000000000) (18620354664 / 1000000000000))
    | 19 => (orderedInterval (-2057695343 / 1000000000000) (-2057695334 / 1000000000000), orderedInterval (75278435823 / 1000000000000) (75278435832 / 1000000000000))
    | 20 => (orderedInterval (89051065297 / 1000000000000) (89051068159 / 1000000000000), orderedInterval (-34252669659 / 1000000000000) (-34252666798 / 1000000000000))
    | 21 => (orderedInterval (99266498633 / 1000000000000) (99266498634 / 1000000000000), orderedInterval (82311827836 / 1000000000000) (82311827837 / 1000000000000))
    | 22 => (orderedInterval (22313974182 / 1000000000000) (22313974593 / 1000000000000), orderedInterval (-75653090076 / 1000000000000) (-75653089666 / 1000000000000))
    | 23 => (orderedInterval (31965584168 / 1000000000000) (31965587871 / 1000000000000), orderedInterval (-59464561086 / 1000000000000) (-59464557383 / 1000000000000))
    | 24 => (orderedInterval (-33576401571 / 1000000000000) (-33576401570 / 1000000000000), orderedInterval (-97797994084 / 1000000000000) (-97797994083 / 1000000000000))
    | 25 => (orderedInterval (16340747182 / 1000000000000) (16340747450 / 1000000000000), orderedInterval (-48786535182 / 1000000000000) (-48786534915 / 1000000000000))
    | _ => (orderedInterval (-62028249681 / 1000000000000) (-62028249677 / 1000000000000), orderedInterval (-10323114263 / 1000000000000) (-10323114259 / 1000000000000))
  chunkTarget := fun r b =>
    match r.val with
    | 0 =>
      match b.val with
      | 0 => orderedInterval (-30286835282 / 1000000000000) (-30286835240 / 1000000000000)
      | 1 => orderedInterval (-534941804 / 1000000000000) (-534941715 / 1000000000000)
      | 2 => orderedInterval (2064849525 / 1000000000000) (2064849716 / 1000000000000)
      | 3 => orderedInterval (-7109452652 / 1000000000000) (-7109442865 / 1000000000000)
      | 4 => orderedInterval (-3991109850 / 1000000000000) (-3991109744 / 1000000000000)
      | 5 => orderedInterval (-834650856 / 1000000000000) (-834650344 / 1000000000000)
      | 6 => orderedInterval (-7650645429 / 1000000000000) (-7650645301 / 1000000000000)
      | 7 => orderedInterval (-4789008115 / 1000000000000) (-4789007806 / 1000000000000)
      | _ => orderedInterval (10105569603 / 1000000000000) (10105569662 / 1000000000000)
    | 1 =>
      match b.val with
      | 0 => orderedInterval (-4734164010 / 1000000000000) (-4734163974 / 1000000000000)
      | 1 => orderedInterval (7975169983 / 1000000000000) (7975170116 / 1000000000000)
      | 2 => orderedInterval (-1463383317 / 1000000000000) (-1463382941 / 1000000000000)
      | 3 => orderedInterval (-13262571883 / 1000000000000) (-13262549474 / 1000000000000)
      | 4 => orderedInterval (-6676906039 / 1000000000000) (-6676905856 / 1000000000000)
      | 5 => orderedInterval (4989312140 / 1000000000000) (4989312845 / 1000000000000)
      | 6 => orderedInterval (-7344653472 / 1000000000000) (-7344653390 / 1000000000000)
      | 7 => orderedInterval (5846408598 / 1000000000000) (5846408928 / 1000000000000)
      | _ => orderedInterval (9520262128 / 1000000000000) (9520262221 / 1000000000000)
    | 2 =>
      match b.val with
      | 0 => orderedInterval (32042086064 / 1000000000000) (32042086096 / 1000000000000)
      | 1 => orderedInterval (3661689963 / 1000000000000) (3661690169 / 1000000000000)
      | 2 => orderedInterval (-5922620922 / 1000000000000) (-5922620179 / 1000000000000)
      | 3 => orderedInterval (19124698651 / 1000000000000) (19124750142 / 1000000000000)
      | 4 => orderedInterval (11145036938 / 1000000000000) (11145037253 / 1000000000000)
      | 5 => orderedInterval (-827725403 / 1000000000000) (-827724421 / 1000000000000)
      | 6 => orderedInterval (10274655127 / 1000000000000) (10274655185 / 1000000000000)
      | 7 => orderedInterval (3295683604 / 1000000000000) (3295683959 / 1000000000000)
      | _ => orderedInterval (-13384899084 / 1000000000000) (-13384898932 / 1000000000000)
    | 3 =>
      match b.val with
      | 0 => orderedInterval (5274827702 / 1000000000000) (5274827732 / 1000000000000)
      | 1 => orderedInterval (-14750103770 / 1000000000000) (-14750103450 / 1000000000000)
      | 2 => orderedInterval (7664825959 / 1000000000000) (7664827423 / 1000000000000)
      | 3 => orderedInterval (66167520909 / 1000000000000) (66167638843 / 1000000000000)
      | 4 => orderedInterval (15865623041 / 1000000000000) (15865623586 / 1000000000000)
      | 5 => orderedInterval (-8934777558 / 1000000000000) (-8934776193 / 1000000000000)
      | 6 => orderedInterval (6061744423 / 1000000000000) (6061744467 / 1000000000000)
      | 7 => orderedInterval (-6610563205 / 1000000000000) (-6610562823 / 1000000000000)
      | _ => orderedInterval (-29081237799 / 1000000000000) (-29081237542 / 1000000000000)
    | _ =>
      match b.val with
      | 0 => orderedInterval (-34236994348 / 1000000000000) (-34236994318 / 1000000000000)
      | 1 => orderedInterval (-9344804448 / 1000000000000) (-9344803946 / 1000000000000)
      | 2 => orderedInterval (18545616396 / 1000000000000) (18545619297 / 1000000000000)
      | 3 => orderedInterval (-63678763744 / 1000000000000) (-63678492712 / 1000000000000)
      | 4 => orderedInterval (-34542833267 / 1000000000000) (-34542832315 / 1000000000000)
      | 5 => orderedInterval (9033254287 / 1000000000000) (9033256205 / 1000000000000)
      | 6 => orderedInterval (-11450396222 / 1000000000000) (-11450396185 / 1000000000000)
      | 7 => orderedInterval (-3465684787 / 1000000000000) (-3465684374 / 1000000000000)
      | _ => orderedInterval (12232255359 / 1000000000000) (12232255809 / 1000000000000)
  coefficientTarget := fun i =>
    match i.val with
    | 0 => orderedInterval (-43026224860 / 1000000000000) (-43026213637 / 1000000000000)
    | 1 => orderedInterval (-5150525872 / 1000000000000) (-5150501525 / 1000000000000)
    | 2 => orderedInterval (59408604938 / 1000000000000) (59408659272 / 1000000000000)
    | 3 => orderedInterval (41657859702 / 1000000000000) (41657982043 / 1000000000000)
    | _ => orderedInterval (-116908350774 / 1000000000000) (-116908072539 / 1000000000000)

theorem compactCertificate254_stateChecks0 :
    compactCertificate254.stateChecks 0 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 41 12 (259 / 2)) (orderedInterval (-69819468250 / 1000000000000) (-69819468240 / 1000000000000), orderedInterval (-6148267462 / 1000000000000) (-6148267452 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 30 12 (381556455506359 / 4000000000000)) (orderedInterval (76610273151 / 1000000000000) (76610276205 / 1000000000000), orderedInterval (-28769162984 / 1000000000000) (-28769159931 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 49 12 (123387518138647 / 800000000000)) (orderedInterval (-56691150762 / 1000000000000) (-56691150761 / 1000000000000), orderedInterval (-30043913411 / 1000000000000) (-30043913410 / 1000000000000))) = true
  norm_num [besselStateAtRationalPoint, besselIntervalStepZero,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, besselZeroTransition,
    besselInitial, besselGridStateAt, besselGridStateBlock00, besselGridStateBlock01,
    besselGridStateBlock02, besselGridStateBlock03, besselGridStateBlock04,
    besselGridStateBlock05, besselGridStateBlock06, besselGridStateBlock07,
    besselGridStateBlock08, besselGridStateBlock09, besselGridStateBlock10,
    besselGridStateBlock11, besselGridStateBlock12, besselGridStateBlock13,
    besselGridStateBlock14, besselGridState009, besselGridState012, besselGridState019, besselGridState022, besselGridState024, besselGridState030, besselGridState033, besselGridState036, besselGridState041, besselGridState042, besselGridState045, besselGridState048, besselGridState049, besselGridState051, besselGridState053, besselGridState060, besselGridState063, besselGridState065, besselGridState071, besselGridState076, besselGridState077, besselGridState082, besselGridState088, besselGridState092, besselGridState094, besselStateSubset, linearInterval, widenInterval,
    rationalErrorInterval, rationalIntervalSubset, orderedInterval, Finset.sum_range_succ,
    IntervalRat.add, IntervalRat.mul, IntervalRat.scale, IntervalRat.singleton]

theorem compactCertificate254_stateChecks1 :
    compactCertificate254.stateChecks 3 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 9 12 (111337222101413 / 4000000000000)) (orderedInterval (-50556292594 / 1000000000000) (-50556292593 / 1000000000000), orderedInterval (-141635764508 / 1000000000000) (-141635764507 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 24 12 (299067439440161 / 4000000000000)) (orderedInterval (14004818371 / 1000000000000) (14004818372 / 1000000000000), orderedInterval (91113686191 / 1000000000000) (91113686192 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 65 12 (812026274982237 / 4000000000000)) (orderedInterval (22433395389 / 1000000000000) (22433396416 / 1000000000000), orderedInterval (-51365151927 / 1000000000000) (-51365150900 / 1000000000000))) = true
  norm_num [besselStateAtRationalPoint, besselIntervalStepZero,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, besselZeroTransition,
    besselInitial, besselGridStateAt, besselGridStateBlock00, besselGridStateBlock01,
    besselGridStateBlock02, besselGridStateBlock03, besselGridStateBlock04,
    besselGridStateBlock05, besselGridStateBlock06, besselGridStateBlock07,
    besselGridStateBlock08, besselGridStateBlock09, besselGridStateBlock10,
    besselGridStateBlock11, besselGridStateBlock12, besselGridStateBlock13,
    besselGridStateBlock14, besselGridState009, besselGridState012, besselGridState019, besselGridState022, besselGridState024, besselGridState030, besselGridState033, besselGridState036, besselGridState041, besselGridState042, besselGridState045, besselGridState048, besselGridState049, besselGridState051, besselGridState053, besselGridState060, besselGridState063, besselGridState065, besselGridState071, besselGridState076, besselGridState077, besselGridState082, besselGridState088, besselGridState092, besselGridState094, besselStateSubset, linearInterval, widenInterval,
    rationalErrorInterval, rationalIntervalSubset, orderedInterval, Finset.sum_range_succ,
    IntervalRat.add, IntervalRat.mul, IntervalRat.scale, IntervalRat.singleton]

theorem compactCertificate254_stateChecks2 :
    compactCertificate254.stateChecks 6 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 48 12 (598134878880581 / 4000000000000)) (orderedInterval (-30024085113 / 1000000000000) (-30024082153 / 1000000000000), orderedInterval (58030814386 / 1000000000000) (58030817346 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 82 12 (1024914309844313 / 4000000000000)) (orderedInterval (-28025865739 / 1000000000000) (-28025859809 / 1000000000000), orderedInterval (41275194208 / 1000000000000) (41275200139 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 60 12 (754947241817867 / 4000000000000)) (orderedInterval (49669750927 / 1000000000000) (49669750928 / 1000000000000), orderedInterval (29967686231 / 1000000000000) (29967686232 / 1000000000000))) = true
  norm_num [besselStateAtRationalPoint, besselIntervalStepZero,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, besselZeroTransition,
    besselInitial, besselGridStateAt, besselGridStateBlock00, besselGridStateBlock01,
    besselGridStateBlock02, besselGridStateBlock03, besselGridStateBlock04,
    besselGridStateBlock05, besselGridStateBlock06, besselGridStateBlock07,
    besselGridStateBlock08, besselGridStateBlock09, besselGridStateBlock10,
    besselGridStateBlock11, besselGridStateBlock12, besselGridStateBlock13,
    besselGridStateBlock14, besselGridState009, besselGridState012, besselGridState019, besselGridState022, besselGridState024, besselGridState030, besselGridState033, besselGridState036, besselGridState041, besselGridState042, besselGridState045, besselGridState048, besselGridState049, besselGridState051, besselGridState053, besselGridState060, besselGridState063, besselGridState065, besselGridState071, besselGridState076, besselGridState077, besselGridState082, besselGridState088, besselGridState092, besselGridState094, besselStateSubset, linearInterval, widenInterval,
    rationalErrorInterval, rationalIntervalSubset, orderedInterval, Finset.sum_range_succ,
    IntervalRat.add, IntervalRat.mul, IntervalRat.scale, IntervalRat.singleton]

theorem compactCertificate254_stateChecks3 :
    compactCertificate254.stateChecks 9 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 92 12 (1158283212344741 / 4000000000000)) (orderedInterval (45526822562 / 1000000000000) (45526822565 / 1000000000000), orderedInterval (11137443380 / 1000000000000) (11137443384 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 53 12 (668735124444989 / 4000000000000)) (orderedInterval (-61356645747 / 1000000000000) (-61356645736 / 1000000000000), orderedInterval (-6392919757 / 1000000000000) (-6392919746 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 94 12 (1186682213508001 / 4000000000000)) (orderedInterval (38873778085 / 1000000000000) (38873846559 / 1000000000000), orderedInterval (-25258934077 / 1000000000000) (-25258865603 / 1000000000000))) = true
  norm_num [besselStateAtRationalPoint, besselIntervalStepZero,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, besselZeroTransition,
    besselInitial, besselGridStateAt, besselGridStateBlock00, besselGridStateBlock01,
    besselGridStateBlock02, besselGridStateBlock03, besselGridStateBlock04,
    besselGridStateBlock05, besselGridStateBlock06, besselGridStateBlock07,
    besselGridStateBlock08, besselGridStateBlock09, besselGridStateBlock10,
    besselGridStateBlock11, besselGridStateBlock12, besselGridStateBlock13,
    besselGridStateBlock14, besselGridState009, besselGridState012, besselGridState019, besselGridState022, besselGridState024, besselGridState030, besselGridState033, besselGridState036, besselGridState041, besselGridState042, besselGridState045, besselGridState048, besselGridState049, besselGridState051, besselGridState053, besselGridState060, besselGridState063, besselGridState065, besselGridState071, besselGridState076, besselGridState077, besselGridState082, besselGridState088, besselGridState092, besselGridState094, besselStateSubset, linearInterval, widenInterval,
    rationalErrorInterval, rationalIntervalSubset, orderedInterval, Finset.sum_range_succ,
    IntervalRat.add, IntervalRat.mul, IntervalRat.scale, IntervalRat.singleton]

theorem compactCertificate254_stateChecks4 :
    compactCertificate254.stateChecks 12 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 88 12 (1108752456227269 / 4000000000000)) (orderedInterval (47843651694 / 1000000000000) (47843651746 / 1000000000000), orderedInterval (2686401773 / 1000000000000) (2686401825 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 63 12 (791258069995477 / 4000000000000)) (orderedInterval (-35624735973 / 1000000000000) (-35624735972 / 1000000000000), orderedInterval (-44059094545 / 1000000000000) (-44059094544 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 71 12 (897202318320483 / 4000000000000)) (orderedInterval (-47700684772 / 1000000000000) (-47700667185 / 1000000000000), orderedInterval (23831524538 / 1000000000000) (23831542125 / 1000000000000))) = true
  norm_num [besselStateAtRationalPoint, besselIntervalStepZero,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, besselZeroTransition,
    besselInitial, besselGridStateAt, besselGridStateBlock00, besselGridStateBlock01,
    besselGridStateBlock02, besselGridStateBlock03, besselGridStateBlock04,
    besselGridStateBlock05, besselGridStateBlock06, besselGridStateBlock07,
    besselGridStateBlock08, besselGridStateBlock09, besselGridStateBlock10,
    besselGridStateBlock11, besselGridStateBlock12, besselGridStateBlock13,
    besselGridStateBlock14, besselGridState009, besselGridState012, besselGridState019, besselGridState022, besselGridState024, besselGridState030, besselGridState033, besselGridState036, besselGridState041, besselGridState042, besselGridState045, besselGridState048, besselGridState049, besselGridState051, besselGridState053, besselGridState060, besselGridState063, besselGridState065, besselGridState071, besselGridState076, besselGridState077, besselGridState082, besselGridState088, besselGridState092, besselGridState094, besselStateSubset, linearInterval, widenInterval,
    rationalErrorInterval, rationalIntervalSubset, orderedInterval, Finset.sum_range_succ,
    IntervalRat.add, IntervalRat.mul, IntervalRat.scale, IntervalRat.singleton]

theorem compactCertificate254_stateChecks5 :
    compactCertificate254.stateChecks 15 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 60 12 (747993754971827 / 4000000000000)) (orderedInterval (-38138389888 / 1000000000000) (-38138364022 / 1000000000000), orderedInterval (44259385770 / 1000000000000) (44259411636 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 53 12 (660875166892367 / 4000000000000)) (orderedInterval (29813057490 / 1000000000000) (29813060972 / 1000000000000), orderedInterval (-54536374054 / 1000000000000) (-54536370571 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 76 12 (191547382212333 / 800000000000)) (orderedInterval (51236668650 / 1000000000000) (51236668667 / 1000000000000), orderedInterval (5693733669 / 1000000000000) (5693733686 / 1000000000000))) = true
  norm_num [besselStateAtRationalPoint, besselIntervalStepZero,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, besselZeroTransition,
    besselInitial, besselGridStateAt, besselGridStateBlock00, besselGridStateBlock01,
    besselGridStateBlock02, besselGridStateBlock03, besselGridStateBlock04,
    besselGridStateBlock05, besselGridStateBlock06, besselGridStateBlock07,
    besselGridStateBlock08, besselGridStateBlock09, besselGridStateBlock10,
    besselGridStateBlock11, besselGridStateBlock12, besselGridStateBlock13,
    besselGridStateBlock14, besselGridState009, besselGridState012, besselGridState019, besselGridState022, besselGridState024, besselGridState030, besselGridState033, besselGridState036, besselGridState041, besselGridState042, besselGridState045, besselGridState048, besselGridState049, besselGridState051, besselGridState053, besselGridState060, besselGridState063, besselGridState065, besselGridState071, besselGridState076, besselGridState077, besselGridState082, besselGridState088, besselGridState092, besselGridState094, besselStateSubset, linearInterval, widenInterval,
    rationalErrorInterval, rationalIntervalSubset, orderedInterval, Finset.sum_range_succ,
    IntervalRat.add, IntervalRat.mul, IntervalRat.scale, IntervalRat.singleton]

theorem compactCertificate254_stateChecks6 :
    compactCertificate254.stateChecks 18 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 42 12 (529830139785751 / 4000000000000)) (orderedInterval (66708546741 / 1000000000000) (66708546742 / 1000000000000), orderedInterval (18620354663 / 1000000000000) (18620354664 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 36 12 (449142877204511 / 4000000000000)) (orderedInterval (-2057695343 / 1000000000000) (-2057695334 / 1000000000000), orderedInterval (75278435823 / 1000000000000) (75278435832 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 22 12 (281052758182133 / 4000000000000)) (orderedInterval (89051065297 / 1000000000000) (89051068159 / 1000000000000), orderedInterval (-34252669659 / 1000000000000) (-34252666798 / 1000000000000))) = true
  norm_num [besselStateAtRationalPoint, besselIntervalStepZero,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, besselZeroTransition,
    besselInitial, besselGridStateAt, besselGridStateBlock00, besselGridStateBlock01,
    besselGridStateBlock02, besselGridStateBlock03, besselGridStateBlock04,
    besselGridStateBlock05, besselGridStateBlock06, besselGridStateBlock07,
    besselGridStateBlock08, besselGridStateBlock09, besselGridStateBlock10,
    besselGridStateBlock11, besselGridStateBlock12, besselGridStateBlock13,
    besselGridStateBlock14, besselGridState009, besselGridState012, besselGridState019, besselGridState022, besselGridState024, besselGridState030, besselGridState033, besselGridState036, besselGridState041, besselGridState042, besselGridState045, besselGridState048, besselGridState049, besselGridState051, besselGridState053, besselGridState060, besselGridState063, besselGridState065, besselGridState071, besselGridState076, besselGridState077, besselGridState082, besselGridState088, besselGridState092, besselGridState094, besselStateSubset, linearInterval, widenInterval,
    rationalErrorInterval, rationalIntervalSubset, orderedInterval, Finset.sum_range_succ,
    IntervalRat.add, IntervalRat.mul, IntervalRat.scale, IntervalRat.singleton]

theorem compactCertificate254_stateChecks7 :
    compactCertificate254.stateChecks 21 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 12 12 (151151108089611 / 4000000000000)) (orderedInterval (99266498633 / 1000000000000) (99266498634 / 1000000000000), orderedInterval (82311827836 / 1000000000000) (82311827837 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 33 12 (410404661541833 / 4000000000000)) (orderedInterval (22313974182 / 1000000000000) (22313974593 / 1000000000000), orderedInterval (-75653090076 / 1000000000000) (-75653089666 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 45 12 (560372478761641 / 4000000000000)) (orderedInterval (31965584168 / 1000000000000) (31965587871 / 1000000000000), orderedInterval (-59464561086 / 1000000000000) (-59464557383 / 1000000000000))) = true
  norm_num [besselStateAtRationalPoint, besselIntervalStepZero,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, besselZeroTransition,
    besselInitial, besselGridStateAt, besselGridStateBlock00, besselGridStateBlock01,
    besselGridStateBlock02, besselGridStateBlock03, besselGridStateBlock04,
    besselGridStateBlock05, besselGridStateBlock06, besselGridStateBlock07,
    besselGridStateBlock08, besselGridStateBlock09, besselGridStateBlock10,
    besselGridStateBlock11, besselGridStateBlock12, besselGridStateBlock13,
    besselGridStateBlock14, besselGridState009, besselGridState012, besselGridState019, besselGridState022, besselGridState024, besselGridState030, besselGridState033, besselGridState036, besselGridState041, besselGridState042, besselGridState045, besselGridState048, besselGridState049, besselGridState051, besselGridState053, besselGridState060, besselGridState063, besselGridState065, besselGridState071, besselGridState076, besselGridState077, besselGridState082, besselGridState088, besselGridState092, besselGridState094, besselStateSubset, linearInterval, widenInterval,
    rationalErrorInterval, rationalIntervalSubset, orderedInterval, Finset.sum_range_succ,
    IntervalRat.add, IntervalRat.mul, IntervalRat.scale, IntervalRat.singleton]

theorem compactCertificate254_stateChecks8 :
    compactCertificate254.stateChecks 24 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 19 12 (236947241817867 / 4000000000000)) (orderedInterval (-33576401571 / 1000000000000) (-33576401570 / 1000000000000), orderedInterval (-97797994084 / 1000000000000) (-97797994083 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 77 12 (963177383072107 / 4000000000000)) (orderedInterval (16340747182 / 1000000000000) (16340747450 / 1000000000000), orderedInterval (-48786535182 / 1000000000000) (-48786534915 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 51 12 (643357854338213 / 4000000000000)) (orderedInterval (-62028249681 / 1000000000000) (-62028249677 / 1000000000000), orderedInterval (-10323114263 / 1000000000000) (-10323114259 / 1000000000000))) = true
  norm_num [besselStateAtRationalPoint, besselIntervalStepZero,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, besselZeroTransition,
    besselInitial, besselGridStateAt, besselGridStateBlock00, besselGridStateBlock01,
    besselGridStateBlock02, besselGridStateBlock03, besselGridStateBlock04,
    besselGridStateBlock05, besselGridStateBlock06, besselGridStateBlock07,
    besselGridStateBlock08, besselGridStateBlock09, besselGridStateBlock10,
    besselGridStateBlock11, besselGridStateBlock12, besselGridStateBlock13,
    besselGridStateBlock14, besselGridState009, besselGridState012, besselGridState019, besselGridState022, besselGridState024, besselGridState030, besselGridState033, besselGridState036, besselGridState041, besselGridState042, besselGridState045, besselGridState048, besselGridState049, besselGridState051, besselGridState053, besselGridState060, besselGridState063, besselGridState065, besselGridState071, besselGridState076, besselGridState077, besselGridState082, besselGridState088, besselGridState092, besselGridState094, besselStateSubset, linearInterval, widenInterval,
    rationalErrorInterval, rationalIntervalSubset, orderedInterval, Finset.sum_range_succ,
    IntervalRat.add, IntervalRat.mul, IntervalRat.scale, IntervalRat.singleton]

theorem compactCertificate254_states : ∀ j,
    BesselStateValid (compactCertificate254.point j) (compactCertificate254.state j) :=
  compactCertificate254.statesValid_of_checks3 compactCertificate254_stateChecks0
    compactCertificate254_stateChecks1 compactCertificate254_stateChecks2
    compactCertificate254_stateChecks3 compactCertificate254_stateChecks4
    compactCertificate254_stateChecks5 compactCertificate254_stateChecks6
    compactCertificate254_stateChecks7 compactCertificate254_stateChecks8

theorem compactCertificate254_chunkChecks0_0 :
    compactCertificate254.chunkChecks (0 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 0) <| besselDerivativeNearFromState (259 / 2) 0 (IntervalRat.scale (259 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-69819468250 / 1000000000000) (-69819468240 / 1000000000000), orderedInterval (-6148267462 / 1000000000000) (-6148267452 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 0) <| besselDerivativeNearFromState (381556455506359 / 4000000000000) 0 (IntervalRat.scale (259 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (76610273151 / 1000000000000) (76610276205 / 1000000000000), orderedInterval (-28769162984 / 1000000000000) (-28769159931 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 0) <| besselDerivativeNearFromState (123387518138647 / 800000000000) 0 (IntervalRat.scale (259 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-56691150762 / 1000000000000) (-56691150761 / 1000000000000), orderedInterval (-30043913411 / 1000000000000) (-30043913410 / 1000000000000)))) (orderedInterval (-30286835282 / 1000000000000) (-30286835240 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 0) <| besselDerivativeNearFromState (111337222101413 / 4000000000000) 0 (IntervalRat.scale (259 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-50556292594 / 1000000000000) (-50556292593 / 1000000000000), orderedInterval (-141635764508 / 1000000000000) (-141635764507 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 0) <| besselDerivativeNearFromState (299067439440161 / 4000000000000) 0 (IntervalRat.scale (259 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (14004818371 / 1000000000000) (14004818372 / 1000000000000), orderedInterval (91113686191 / 1000000000000) (91113686192 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 0) <| besselDerivativeNearFromState (812026274982237 / 4000000000000) 0 (IntervalRat.scale (259 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (22433395389 / 1000000000000) (22433396416 / 1000000000000), orderedInterval (-51365151927 / 1000000000000) (-51365150900 / 1000000000000)))) (orderedInterval (-534941804 / 1000000000000) (-534941715 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 0) <| besselDerivativeNearFromState (598134878880581 / 4000000000000) 0 (IntervalRat.scale (259 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-30024085113 / 1000000000000) (-30024082153 / 1000000000000), orderedInterval (58030814386 / 1000000000000) (58030817346 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 0) <| besselDerivativeNearFromState (1024914309844313 / 4000000000000) 0 (IntervalRat.scale (259 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-28025865739 / 1000000000000) (-28025859809 / 1000000000000), orderedInterval (41275194208 / 1000000000000) (41275200139 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 0) <| besselDerivativeNearFromState (754947241817867 / 4000000000000) 0 (IntervalRat.scale (259 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (49669750927 / 1000000000000) (49669750928 / 1000000000000), orderedInterval (29967686231 / 1000000000000) (29967686232 / 1000000000000)))) (orderedInterval (2064849525 / 1000000000000) (2064849716 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate254_chunkChecks0_1 :
    compactCertificate254.chunkChecks (0 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 0) <| besselDerivativeNearFromState (1158283212344741 / 4000000000000) 0 (IntervalRat.scale (259 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (45526822562 / 1000000000000) (45526822565 / 1000000000000), orderedInterval (11137443380 / 1000000000000) (11137443384 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 0) <| besselDerivativeNearFromState (668735124444989 / 4000000000000) 0 (IntervalRat.scale (259 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-61356645747 / 1000000000000) (-61356645736 / 1000000000000), orderedInterval (-6392919757 / 1000000000000) (-6392919746 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 0) <| besselDerivativeNearFromState (1186682213508001 / 4000000000000) 0 (IntervalRat.scale (259 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (38873778085 / 1000000000000) (38873846559 / 1000000000000), orderedInterval (-25258934077 / 1000000000000) (-25258865603 / 1000000000000)))) (orderedInterval (-7109452652 / 1000000000000) (-7109442865 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 0) <| besselDerivativeNearFromState (1108752456227269 / 4000000000000) 0 (IntervalRat.scale (259 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (47843651694 / 1000000000000) (47843651746 / 1000000000000), orderedInterval (2686401773 / 1000000000000) (2686401825 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 0) <| besselDerivativeNearFromState (791258069995477 / 4000000000000) 0 (IntervalRat.scale (259 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-35624735973 / 1000000000000) (-35624735972 / 1000000000000), orderedInterval (-44059094545 / 1000000000000) (-44059094544 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 0) <| besselDerivativeNearFromState (897202318320483 / 4000000000000) 0 (IntervalRat.scale (259 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-47700684772 / 1000000000000) (-47700667185 / 1000000000000), orderedInterval (23831524538 / 1000000000000) (23831542125 / 1000000000000)))) (orderedInterval (-3991109850 / 1000000000000) (-3991109744 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 0) <| besselDerivativeNearFromState (747993754971827 / 4000000000000) 0 (IntervalRat.scale (259 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-38138389888 / 1000000000000) (-38138364022 / 1000000000000), orderedInterval (44259385770 / 1000000000000) (44259411636 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 0) <| besselDerivativeNearFromState (660875166892367 / 4000000000000) 0 (IntervalRat.scale (259 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (29813057490 / 1000000000000) (29813060972 / 1000000000000), orderedInterval (-54536374054 / 1000000000000) (-54536370571 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 0) <| besselDerivativeNearFromState (191547382212333 / 800000000000) 0 (IntervalRat.scale (259 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (51236668650 / 1000000000000) (51236668667 / 1000000000000), orderedInterval (5693733669 / 1000000000000) (5693733686 / 1000000000000)))) (orderedInterval (-834650856 / 1000000000000) (-834650344 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate254_chunkChecks0_2 :
    compactCertificate254.chunkChecks (0 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 0) <| besselDerivativeNearFromState (529830139785751 / 4000000000000) 0 (IntervalRat.scale (259 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (66708546741 / 1000000000000) (66708546742 / 1000000000000), orderedInterval (18620354663 / 1000000000000) (18620354664 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 0) <| besselDerivativeNearFromState (449142877204511 / 4000000000000) 0 (IntervalRat.scale (259 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-2057695343 / 1000000000000) (-2057695334 / 1000000000000), orderedInterval (75278435823 / 1000000000000) (75278435832 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 0) <| besselDerivativeNearFromState (281052758182133 / 4000000000000) 0 (IntervalRat.scale (259 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (89051065297 / 1000000000000) (89051068159 / 1000000000000), orderedInterval (-34252669659 / 1000000000000) (-34252666798 / 1000000000000)))) (orderedInterval (-7650645429 / 1000000000000) (-7650645301 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 0) <| besselDerivativeNearFromState (151151108089611 / 4000000000000) 0 (IntervalRat.scale (259 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (99266498633 / 1000000000000) (99266498634 / 1000000000000), orderedInterval (82311827836 / 1000000000000) (82311827837 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 0) <| besselDerivativeNearFromState (410404661541833 / 4000000000000) 0 (IntervalRat.scale (259 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (22313974182 / 1000000000000) (22313974593 / 1000000000000), orderedInterval (-75653090076 / 1000000000000) (-75653089666 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 0) <| besselDerivativeNearFromState (560372478761641 / 4000000000000) 0 (IntervalRat.scale (259 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (31965584168 / 1000000000000) (31965587871 / 1000000000000), orderedInterval (-59464561086 / 1000000000000) (-59464557383 / 1000000000000)))) (orderedInterval (-4789008115 / 1000000000000) (-4789007806 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 0) <| besselDerivativeNearFromState (236947241817867 / 4000000000000) 0 (IntervalRat.scale (259 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-33576401571 / 1000000000000) (-33576401570 / 1000000000000), orderedInterval (-97797994084 / 1000000000000) (-97797994083 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 0) <| besselDerivativeNearFromState (963177383072107 / 4000000000000) 0 (IntervalRat.scale (259 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (16340747182 / 1000000000000) (16340747450 / 1000000000000), orderedInterval (-48786535182 / 1000000000000) (-48786534915 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 0) <| besselDerivativeNearFromState (643357854338213 / 4000000000000) 0 (IntervalRat.scale (259 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-62028249681 / 1000000000000) (-62028249677 / 1000000000000), orderedInterval (-10323114263 / 1000000000000) (-10323114259 / 1000000000000)))) (orderedInterval (10105569603 / 1000000000000) (10105569662 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate254_chunkChecks0 :
    compactCertificate254.chunkChecks (0 : Fin 5) 0 9 = true :=
  compactCertificate254.chunkChecks_nine_of_three (0 : Fin 5) compactCertificate254_chunkChecks0_0
    compactCertificate254_chunkChecks0_1 compactCertificate254_chunkChecks0_2

theorem compactCertificate254_chunkChecks1_0 :
    compactCertificate254.chunkChecks (1 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 1) <| besselDerivativeNearFromState (259 / 2) 1 (IntervalRat.scale (259 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-69819468250 / 1000000000000) (-69819468240 / 1000000000000), orderedInterval (-6148267462 / 1000000000000) (-6148267452 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 1) <| besselDerivativeNearFromState (381556455506359 / 4000000000000) 1 (IntervalRat.scale (259 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (76610273151 / 1000000000000) (76610276205 / 1000000000000), orderedInterval (-28769162984 / 1000000000000) (-28769159931 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 1) <| besselDerivativeNearFromState (123387518138647 / 800000000000) 1 (IntervalRat.scale (259 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-56691150762 / 1000000000000) (-56691150761 / 1000000000000), orderedInterval (-30043913411 / 1000000000000) (-30043913410 / 1000000000000)))) (orderedInterval (-4734164010 / 1000000000000) (-4734163974 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 1) <| besselDerivativeNearFromState (111337222101413 / 4000000000000) 1 (IntervalRat.scale (259 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-50556292594 / 1000000000000) (-50556292593 / 1000000000000), orderedInterval (-141635764508 / 1000000000000) (-141635764507 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 1) <| besselDerivativeNearFromState (299067439440161 / 4000000000000) 1 (IntervalRat.scale (259 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (14004818371 / 1000000000000) (14004818372 / 1000000000000), orderedInterval (91113686191 / 1000000000000) (91113686192 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 1) <| besselDerivativeNearFromState (812026274982237 / 4000000000000) 1 (IntervalRat.scale (259 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (22433395389 / 1000000000000) (22433396416 / 1000000000000), orderedInterval (-51365151927 / 1000000000000) (-51365150900 / 1000000000000)))) (orderedInterval (7975169983 / 1000000000000) (7975170116 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 1) <| besselDerivativeNearFromState (598134878880581 / 4000000000000) 1 (IntervalRat.scale (259 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-30024085113 / 1000000000000) (-30024082153 / 1000000000000), orderedInterval (58030814386 / 1000000000000) (58030817346 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 1) <| besselDerivativeNearFromState (1024914309844313 / 4000000000000) 1 (IntervalRat.scale (259 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-28025865739 / 1000000000000) (-28025859809 / 1000000000000), orderedInterval (41275194208 / 1000000000000) (41275200139 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 1) <| besselDerivativeNearFromState (754947241817867 / 4000000000000) 1 (IntervalRat.scale (259 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (49669750927 / 1000000000000) (49669750928 / 1000000000000), orderedInterval (29967686231 / 1000000000000) (29967686232 / 1000000000000)))) (orderedInterval (-1463383317 / 1000000000000) (-1463382941 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate254_chunkChecks1_1 :
    compactCertificate254.chunkChecks (1 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 1) <| besselDerivativeNearFromState (1158283212344741 / 4000000000000) 1 (IntervalRat.scale (259 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (45526822562 / 1000000000000) (45526822565 / 1000000000000), orderedInterval (11137443380 / 1000000000000) (11137443384 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 1) <| besselDerivativeNearFromState (668735124444989 / 4000000000000) 1 (IntervalRat.scale (259 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-61356645747 / 1000000000000) (-61356645736 / 1000000000000), orderedInterval (-6392919757 / 1000000000000) (-6392919746 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 1) <| besselDerivativeNearFromState (1186682213508001 / 4000000000000) 1 (IntervalRat.scale (259 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (38873778085 / 1000000000000) (38873846559 / 1000000000000), orderedInterval (-25258934077 / 1000000000000) (-25258865603 / 1000000000000)))) (orderedInterval (-13262571883 / 1000000000000) (-13262549474 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 1) <| besselDerivativeNearFromState (1108752456227269 / 4000000000000) 1 (IntervalRat.scale (259 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (47843651694 / 1000000000000) (47843651746 / 1000000000000), orderedInterval (2686401773 / 1000000000000) (2686401825 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 1) <| besselDerivativeNearFromState (791258069995477 / 4000000000000) 1 (IntervalRat.scale (259 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-35624735973 / 1000000000000) (-35624735972 / 1000000000000), orderedInterval (-44059094545 / 1000000000000) (-44059094544 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 1) <| besselDerivativeNearFromState (897202318320483 / 4000000000000) 1 (IntervalRat.scale (259 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-47700684772 / 1000000000000) (-47700667185 / 1000000000000), orderedInterval (23831524538 / 1000000000000) (23831542125 / 1000000000000)))) (orderedInterval (-6676906039 / 1000000000000) (-6676905856 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 1) <| besselDerivativeNearFromState (747993754971827 / 4000000000000) 1 (IntervalRat.scale (259 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-38138389888 / 1000000000000) (-38138364022 / 1000000000000), orderedInterval (44259385770 / 1000000000000) (44259411636 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 1) <| besselDerivativeNearFromState (660875166892367 / 4000000000000) 1 (IntervalRat.scale (259 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (29813057490 / 1000000000000) (29813060972 / 1000000000000), orderedInterval (-54536374054 / 1000000000000) (-54536370571 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 1) <| besselDerivativeNearFromState (191547382212333 / 800000000000) 1 (IntervalRat.scale (259 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (51236668650 / 1000000000000) (51236668667 / 1000000000000), orderedInterval (5693733669 / 1000000000000) (5693733686 / 1000000000000)))) (orderedInterval (4989312140 / 1000000000000) (4989312845 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate254_chunkChecks1_2 :
    compactCertificate254.chunkChecks (1 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 1) <| besselDerivativeNearFromState (529830139785751 / 4000000000000) 1 (IntervalRat.scale (259 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (66708546741 / 1000000000000) (66708546742 / 1000000000000), orderedInterval (18620354663 / 1000000000000) (18620354664 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 1) <| besselDerivativeNearFromState (449142877204511 / 4000000000000) 1 (IntervalRat.scale (259 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-2057695343 / 1000000000000) (-2057695334 / 1000000000000), orderedInterval (75278435823 / 1000000000000) (75278435832 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 1) <| besselDerivativeNearFromState (281052758182133 / 4000000000000) 1 (IntervalRat.scale (259 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (89051065297 / 1000000000000) (89051068159 / 1000000000000), orderedInterval (-34252669659 / 1000000000000) (-34252666798 / 1000000000000)))) (orderedInterval (-7344653472 / 1000000000000) (-7344653390 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 1) <| besselDerivativeNearFromState (151151108089611 / 4000000000000) 1 (IntervalRat.scale (259 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (99266498633 / 1000000000000) (99266498634 / 1000000000000), orderedInterval (82311827836 / 1000000000000) (82311827837 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 1) <| besselDerivativeNearFromState (410404661541833 / 4000000000000) 1 (IntervalRat.scale (259 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (22313974182 / 1000000000000) (22313974593 / 1000000000000), orderedInterval (-75653090076 / 1000000000000) (-75653089666 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 1) <| besselDerivativeNearFromState (560372478761641 / 4000000000000) 1 (IntervalRat.scale (259 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (31965584168 / 1000000000000) (31965587871 / 1000000000000), orderedInterval (-59464561086 / 1000000000000) (-59464557383 / 1000000000000)))) (orderedInterval (5846408598 / 1000000000000) (5846408928 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 1) <| besselDerivativeNearFromState (236947241817867 / 4000000000000) 1 (IntervalRat.scale (259 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-33576401571 / 1000000000000) (-33576401570 / 1000000000000), orderedInterval (-97797994084 / 1000000000000) (-97797994083 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 1) <| besselDerivativeNearFromState (963177383072107 / 4000000000000) 1 (IntervalRat.scale (259 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (16340747182 / 1000000000000) (16340747450 / 1000000000000), orderedInterval (-48786535182 / 1000000000000) (-48786534915 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 1) <| besselDerivativeNearFromState (643357854338213 / 4000000000000) 1 (IntervalRat.scale (259 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-62028249681 / 1000000000000) (-62028249677 / 1000000000000), orderedInterval (-10323114263 / 1000000000000) (-10323114259 / 1000000000000)))) (orderedInterval (9520262128 / 1000000000000) (9520262221 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate254_chunkChecks1 :
    compactCertificate254.chunkChecks (1 : Fin 5) 0 9 = true :=
  compactCertificate254.chunkChecks_nine_of_three (1 : Fin 5) compactCertificate254_chunkChecks1_0
    compactCertificate254_chunkChecks1_1 compactCertificate254_chunkChecks1_2

theorem compactCertificate254_chunkChecks2_0 :
    compactCertificate254.chunkChecks (2 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 2) <| besselDerivativeNearFromState (259 / 2) 2 (IntervalRat.scale (259 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-69819468250 / 1000000000000) (-69819468240 / 1000000000000), orderedInterval (-6148267462 / 1000000000000) (-6148267452 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 2) <| besselDerivativeNearFromState (381556455506359 / 4000000000000) 2 (IntervalRat.scale (259 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (76610273151 / 1000000000000) (76610276205 / 1000000000000), orderedInterval (-28769162984 / 1000000000000) (-28769159931 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 2) <| besselDerivativeNearFromState (123387518138647 / 800000000000) 2 (IntervalRat.scale (259 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-56691150762 / 1000000000000) (-56691150761 / 1000000000000), orderedInterval (-30043913411 / 1000000000000) (-30043913410 / 1000000000000)))) (orderedInterval (32042086064 / 1000000000000) (32042086096 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 2) <| besselDerivativeNearFromState (111337222101413 / 4000000000000) 2 (IntervalRat.scale (259 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-50556292594 / 1000000000000) (-50556292593 / 1000000000000), orderedInterval (-141635764508 / 1000000000000) (-141635764507 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 2) <| besselDerivativeNearFromState (299067439440161 / 4000000000000) 2 (IntervalRat.scale (259 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (14004818371 / 1000000000000) (14004818372 / 1000000000000), orderedInterval (91113686191 / 1000000000000) (91113686192 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 2) <| besselDerivativeNearFromState (812026274982237 / 4000000000000) 2 (IntervalRat.scale (259 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (22433395389 / 1000000000000) (22433396416 / 1000000000000), orderedInterval (-51365151927 / 1000000000000) (-51365150900 / 1000000000000)))) (orderedInterval (3661689963 / 1000000000000) (3661690169 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 2) <| besselDerivativeNearFromState (598134878880581 / 4000000000000) 2 (IntervalRat.scale (259 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-30024085113 / 1000000000000) (-30024082153 / 1000000000000), orderedInterval (58030814386 / 1000000000000) (58030817346 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 2) <| besselDerivativeNearFromState (1024914309844313 / 4000000000000) 2 (IntervalRat.scale (259 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-28025865739 / 1000000000000) (-28025859809 / 1000000000000), orderedInterval (41275194208 / 1000000000000) (41275200139 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 2) <| besselDerivativeNearFromState (754947241817867 / 4000000000000) 2 (IntervalRat.scale (259 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (49669750927 / 1000000000000) (49669750928 / 1000000000000), orderedInterval (29967686231 / 1000000000000) (29967686232 / 1000000000000)))) (orderedInterval (-5922620922 / 1000000000000) (-5922620179 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate254_chunkChecks2_1 :
    compactCertificate254.chunkChecks (2 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 2) <| besselDerivativeNearFromState (1158283212344741 / 4000000000000) 2 (IntervalRat.scale (259 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (45526822562 / 1000000000000) (45526822565 / 1000000000000), orderedInterval (11137443380 / 1000000000000) (11137443384 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 2) <| besselDerivativeNearFromState (668735124444989 / 4000000000000) 2 (IntervalRat.scale (259 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-61356645747 / 1000000000000) (-61356645736 / 1000000000000), orderedInterval (-6392919757 / 1000000000000) (-6392919746 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 2) <| besselDerivativeNearFromState (1186682213508001 / 4000000000000) 2 (IntervalRat.scale (259 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (38873778085 / 1000000000000) (38873846559 / 1000000000000), orderedInterval (-25258934077 / 1000000000000) (-25258865603 / 1000000000000)))) (orderedInterval (19124698651 / 1000000000000) (19124750142 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 2) <| besselDerivativeNearFromState (1108752456227269 / 4000000000000) 2 (IntervalRat.scale (259 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (47843651694 / 1000000000000) (47843651746 / 1000000000000), orderedInterval (2686401773 / 1000000000000) (2686401825 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 2) <| besselDerivativeNearFromState (791258069995477 / 4000000000000) 2 (IntervalRat.scale (259 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-35624735973 / 1000000000000) (-35624735972 / 1000000000000), orderedInterval (-44059094545 / 1000000000000) (-44059094544 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 2) <| besselDerivativeNearFromState (897202318320483 / 4000000000000) 2 (IntervalRat.scale (259 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-47700684772 / 1000000000000) (-47700667185 / 1000000000000), orderedInterval (23831524538 / 1000000000000) (23831542125 / 1000000000000)))) (orderedInterval (11145036938 / 1000000000000) (11145037253 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 2) <| besselDerivativeNearFromState (747993754971827 / 4000000000000) 2 (IntervalRat.scale (259 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-38138389888 / 1000000000000) (-38138364022 / 1000000000000), orderedInterval (44259385770 / 1000000000000) (44259411636 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 2) <| besselDerivativeNearFromState (660875166892367 / 4000000000000) 2 (IntervalRat.scale (259 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (29813057490 / 1000000000000) (29813060972 / 1000000000000), orderedInterval (-54536374054 / 1000000000000) (-54536370571 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 2) <| besselDerivativeNearFromState (191547382212333 / 800000000000) 2 (IntervalRat.scale (259 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (51236668650 / 1000000000000) (51236668667 / 1000000000000), orderedInterval (5693733669 / 1000000000000) (5693733686 / 1000000000000)))) (orderedInterval (-827725403 / 1000000000000) (-827724421 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate254_chunkChecks2_2 :
    compactCertificate254.chunkChecks (2 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 2) <| besselDerivativeNearFromState (529830139785751 / 4000000000000) 2 (IntervalRat.scale (259 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (66708546741 / 1000000000000) (66708546742 / 1000000000000), orderedInterval (18620354663 / 1000000000000) (18620354664 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 2) <| besselDerivativeNearFromState (449142877204511 / 4000000000000) 2 (IntervalRat.scale (259 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-2057695343 / 1000000000000) (-2057695334 / 1000000000000), orderedInterval (75278435823 / 1000000000000) (75278435832 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 2) <| besselDerivativeNearFromState (281052758182133 / 4000000000000) 2 (IntervalRat.scale (259 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (89051065297 / 1000000000000) (89051068159 / 1000000000000), orderedInterval (-34252669659 / 1000000000000) (-34252666798 / 1000000000000)))) (orderedInterval (10274655127 / 1000000000000) (10274655185 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 2) <| besselDerivativeNearFromState (151151108089611 / 4000000000000) 2 (IntervalRat.scale (259 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (99266498633 / 1000000000000) (99266498634 / 1000000000000), orderedInterval (82311827836 / 1000000000000) (82311827837 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 2) <| besselDerivativeNearFromState (410404661541833 / 4000000000000) 2 (IntervalRat.scale (259 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (22313974182 / 1000000000000) (22313974593 / 1000000000000), orderedInterval (-75653090076 / 1000000000000) (-75653089666 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 2) <| besselDerivativeNearFromState (560372478761641 / 4000000000000) 2 (IntervalRat.scale (259 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (31965584168 / 1000000000000) (31965587871 / 1000000000000), orderedInterval (-59464561086 / 1000000000000) (-59464557383 / 1000000000000)))) (orderedInterval (3295683604 / 1000000000000) (3295683959 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 2) <| besselDerivativeNearFromState (236947241817867 / 4000000000000) 2 (IntervalRat.scale (259 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-33576401571 / 1000000000000) (-33576401570 / 1000000000000), orderedInterval (-97797994084 / 1000000000000) (-97797994083 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 2) <| besselDerivativeNearFromState (963177383072107 / 4000000000000) 2 (IntervalRat.scale (259 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (16340747182 / 1000000000000) (16340747450 / 1000000000000), orderedInterval (-48786535182 / 1000000000000) (-48786534915 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 2) <| besselDerivativeNearFromState (643357854338213 / 4000000000000) 2 (IntervalRat.scale (259 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-62028249681 / 1000000000000) (-62028249677 / 1000000000000), orderedInterval (-10323114263 / 1000000000000) (-10323114259 / 1000000000000)))) (orderedInterval (-13384899084 / 1000000000000) (-13384898932 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate254_chunkChecks2 :
    compactCertificate254.chunkChecks (2 : Fin 5) 0 9 = true :=
  compactCertificate254.chunkChecks_nine_of_three (2 : Fin 5) compactCertificate254_chunkChecks2_0
    compactCertificate254_chunkChecks2_1 compactCertificate254_chunkChecks2_2

theorem compactCertificate254_chunkChecks3_0 :
    compactCertificate254.chunkChecks (3 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 3) <| besselDerivativeNearFromState (259 / 2) 3 (IntervalRat.scale (259 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-69819468250 / 1000000000000) (-69819468240 / 1000000000000), orderedInterval (-6148267462 / 1000000000000) (-6148267452 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 3) <| besselDerivativeNearFromState (381556455506359 / 4000000000000) 3 (IntervalRat.scale (259 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (76610273151 / 1000000000000) (76610276205 / 1000000000000), orderedInterval (-28769162984 / 1000000000000) (-28769159931 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 3) <| besselDerivativeNearFromState (123387518138647 / 800000000000) 3 (IntervalRat.scale (259 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-56691150762 / 1000000000000) (-56691150761 / 1000000000000), orderedInterval (-30043913411 / 1000000000000) (-30043913410 / 1000000000000)))) (orderedInterval (5274827702 / 1000000000000) (5274827732 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 3) <| besselDerivativeNearFromState (111337222101413 / 4000000000000) 3 (IntervalRat.scale (259 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-50556292594 / 1000000000000) (-50556292593 / 1000000000000), orderedInterval (-141635764508 / 1000000000000) (-141635764507 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 3) <| besselDerivativeNearFromState (299067439440161 / 4000000000000) 3 (IntervalRat.scale (259 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (14004818371 / 1000000000000) (14004818372 / 1000000000000), orderedInterval (91113686191 / 1000000000000) (91113686192 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 3) <| besselDerivativeNearFromState (812026274982237 / 4000000000000) 3 (IntervalRat.scale (259 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (22433395389 / 1000000000000) (22433396416 / 1000000000000), orderedInterval (-51365151927 / 1000000000000) (-51365150900 / 1000000000000)))) (orderedInterval (-14750103770 / 1000000000000) (-14750103450 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 3) <| besselDerivativeNearFromState (598134878880581 / 4000000000000) 3 (IntervalRat.scale (259 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-30024085113 / 1000000000000) (-30024082153 / 1000000000000), orderedInterval (58030814386 / 1000000000000) (58030817346 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 3) <| besselDerivativeNearFromState (1024914309844313 / 4000000000000) 3 (IntervalRat.scale (259 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-28025865739 / 1000000000000) (-28025859809 / 1000000000000), orderedInterval (41275194208 / 1000000000000) (41275200139 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 3) <| besselDerivativeNearFromState (754947241817867 / 4000000000000) 3 (IntervalRat.scale (259 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (49669750927 / 1000000000000) (49669750928 / 1000000000000), orderedInterval (29967686231 / 1000000000000) (29967686232 / 1000000000000)))) (orderedInterval (7664825959 / 1000000000000) (7664827423 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate254_chunkChecks3_1 :
    compactCertificate254.chunkChecks (3 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 3) <| besselDerivativeNearFromState (1158283212344741 / 4000000000000) 3 (IntervalRat.scale (259 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (45526822562 / 1000000000000) (45526822565 / 1000000000000), orderedInterval (11137443380 / 1000000000000) (11137443384 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 3) <| besselDerivativeNearFromState (668735124444989 / 4000000000000) 3 (IntervalRat.scale (259 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-61356645747 / 1000000000000) (-61356645736 / 1000000000000), orderedInterval (-6392919757 / 1000000000000) (-6392919746 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 3) <| besselDerivativeNearFromState (1186682213508001 / 4000000000000) 3 (IntervalRat.scale (259 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (38873778085 / 1000000000000) (38873846559 / 1000000000000), orderedInterval (-25258934077 / 1000000000000) (-25258865603 / 1000000000000)))) (orderedInterval (66167520909 / 1000000000000) (66167638843 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 3) <| besselDerivativeNearFromState (1108752456227269 / 4000000000000) 3 (IntervalRat.scale (259 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (47843651694 / 1000000000000) (47843651746 / 1000000000000), orderedInterval (2686401773 / 1000000000000) (2686401825 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 3) <| besselDerivativeNearFromState (791258069995477 / 4000000000000) 3 (IntervalRat.scale (259 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-35624735973 / 1000000000000) (-35624735972 / 1000000000000), orderedInterval (-44059094545 / 1000000000000) (-44059094544 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 3) <| besselDerivativeNearFromState (897202318320483 / 4000000000000) 3 (IntervalRat.scale (259 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-47700684772 / 1000000000000) (-47700667185 / 1000000000000), orderedInterval (23831524538 / 1000000000000) (23831542125 / 1000000000000)))) (orderedInterval (15865623041 / 1000000000000) (15865623586 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 3) <| besselDerivativeNearFromState (747993754971827 / 4000000000000) 3 (IntervalRat.scale (259 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-38138389888 / 1000000000000) (-38138364022 / 1000000000000), orderedInterval (44259385770 / 1000000000000) (44259411636 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 3) <| besselDerivativeNearFromState (660875166892367 / 4000000000000) 3 (IntervalRat.scale (259 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (29813057490 / 1000000000000) (29813060972 / 1000000000000), orderedInterval (-54536374054 / 1000000000000) (-54536370571 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 3) <| besselDerivativeNearFromState (191547382212333 / 800000000000) 3 (IntervalRat.scale (259 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (51236668650 / 1000000000000) (51236668667 / 1000000000000), orderedInterval (5693733669 / 1000000000000) (5693733686 / 1000000000000)))) (orderedInterval (-8934777558 / 1000000000000) (-8934776193 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate254_chunkChecks3_2 :
    compactCertificate254.chunkChecks (3 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 3) <| besselDerivativeNearFromState (529830139785751 / 4000000000000) 3 (IntervalRat.scale (259 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (66708546741 / 1000000000000) (66708546742 / 1000000000000), orderedInterval (18620354663 / 1000000000000) (18620354664 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 3) <| besselDerivativeNearFromState (449142877204511 / 4000000000000) 3 (IntervalRat.scale (259 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-2057695343 / 1000000000000) (-2057695334 / 1000000000000), orderedInterval (75278435823 / 1000000000000) (75278435832 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 3) <| besselDerivativeNearFromState (281052758182133 / 4000000000000) 3 (IntervalRat.scale (259 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (89051065297 / 1000000000000) (89051068159 / 1000000000000), orderedInterval (-34252669659 / 1000000000000) (-34252666798 / 1000000000000)))) (orderedInterval (6061744423 / 1000000000000) (6061744467 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 3) <| besselDerivativeNearFromState (151151108089611 / 4000000000000) 3 (IntervalRat.scale (259 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (99266498633 / 1000000000000) (99266498634 / 1000000000000), orderedInterval (82311827836 / 1000000000000) (82311827837 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 3) <| besselDerivativeNearFromState (410404661541833 / 4000000000000) 3 (IntervalRat.scale (259 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (22313974182 / 1000000000000) (22313974593 / 1000000000000), orderedInterval (-75653090076 / 1000000000000) (-75653089666 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 3) <| besselDerivativeNearFromState (560372478761641 / 4000000000000) 3 (IntervalRat.scale (259 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (31965584168 / 1000000000000) (31965587871 / 1000000000000), orderedInterval (-59464561086 / 1000000000000) (-59464557383 / 1000000000000)))) (orderedInterval (-6610563205 / 1000000000000) (-6610562823 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 3) <| besselDerivativeNearFromState (236947241817867 / 4000000000000) 3 (IntervalRat.scale (259 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-33576401571 / 1000000000000) (-33576401570 / 1000000000000), orderedInterval (-97797994084 / 1000000000000) (-97797994083 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 3) <| besselDerivativeNearFromState (963177383072107 / 4000000000000) 3 (IntervalRat.scale (259 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (16340747182 / 1000000000000) (16340747450 / 1000000000000), orderedInterval (-48786535182 / 1000000000000) (-48786534915 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 3) <| besselDerivativeNearFromState (643357854338213 / 4000000000000) 3 (IntervalRat.scale (259 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-62028249681 / 1000000000000) (-62028249677 / 1000000000000), orderedInterval (-10323114263 / 1000000000000) (-10323114259 / 1000000000000)))) (orderedInterval (-29081237799 / 1000000000000) (-29081237542 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate254_chunkChecks3 :
    compactCertificate254.chunkChecks (3 : Fin 5) 0 9 = true :=
  compactCertificate254.chunkChecks_nine_of_three (3 : Fin 5) compactCertificate254_chunkChecks3_0
    compactCertificate254_chunkChecks3_1 compactCertificate254_chunkChecks3_2

theorem compactCertificate254_chunkChecks4_0 :
    compactCertificate254.chunkChecks (4 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 4) <| besselDerivativeNearFromState (259 / 2) 4 (IntervalRat.scale (259 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-69819468250 / 1000000000000) (-69819468240 / 1000000000000), orderedInterval (-6148267462 / 1000000000000) (-6148267452 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 4) <| besselDerivativeNearFromState (381556455506359 / 4000000000000) 4 (IntervalRat.scale (259 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (76610273151 / 1000000000000) (76610276205 / 1000000000000), orderedInterval (-28769162984 / 1000000000000) (-28769159931 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 4) <| besselDerivativeNearFromState (123387518138647 / 800000000000) 4 (IntervalRat.scale (259 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-56691150762 / 1000000000000) (-56691150761 / 1000000000000), orderedInterval (-30043913411 / 1000000000000) (-30043913410 / 1000000000000)))) (orderedInterval (-34236994348 / 1000000000000) (-34236994318 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 4) <| besselDerivativeNearFromState (111337222101413 / 4000000000000) 4 (IntervalRat.scale (259 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-50556292594 / 1000000000000) (-50556292593 / 1000000000000), orderedInterval (-141635764508 / 1000000000000) (-141635764507 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 4) <| besselDerivativeNearFromState (299067439440161 / 4000000000000) 4 (IntervalRat.scale (259 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (14004818371 / 1000000000000) (14004818372 / 1000000000000), orderedInterval (91113686191 / 1000000000000) (91113686192 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 4) <| besselDerivativeNearFromState (812026274982237 / 4000000000000) 4 (IntervalRat.scale (259 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (22433395389 / 1000000000000) (22433396416 / 1000000000000), orderedInterval (-51365151927 / 1000000000000) (-51365150900 / 1000000000000)))) (orderedInterval (-9344804448 / 1000000000000) (-9344803946 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 4) <| besselDerivativeNearFromState (598134878880581 / 4000000000000) 4 (IntervalRat.scale (259 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-30024085113 / 1000000000000) (-30024082153 / 1000000000000), orderedInterval (58030814386 / 1000000000000) (58030817346 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 4) <| besselDerivativeNearFromState (1024914309844313 / 4000000000000) 4 (IntervalRat.scale (259 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-28025865739 / 1000000000000) (-28025859809 / 1000000000000), orderedInterval (41275194208 / 1000000000000) (41275200139 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 4) <| besselDerivativeNearFromState (754947241817867 / 4000000000000) 4 (IntervalRat.scale (259 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (49669750927 / 1000000000000) (49669750928 / 1000000000000), orderedInterval (29967686231 / 1000000000000) (29967686232 / 1000000000000)))) (orderedInterval (18545616396 / 1000000000000) (18545619297 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate254_chunkChecks4_1 :
    compactCertificate254.chunkChecks (4 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 4) <| besselDerivativeNearFromState (1158283212344741 / 4000000000000) 4 (IntervalRat.scale (259 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (45526822562 / 1000000000000) (45526822565 / 1000000000000), orderedInterval (11137443380 / 1000000000000) (11137443384 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 4) <| besselDerivativeNearFromState (668735124444989 / 4000000000000) 4 (IntervalRat.scale (259 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-61356645747 / 1000000000000) (-61356645736 / 1000000000000), orderedInterval (-6392919757 / 1000000000000) (-6392919746 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 4) <| besselDerivativeNearFromState (1186682213508001 / 4000000000000) 4 (IntervalRat.scale (259 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (38873778085 / 1000000000000) (38873846559 / 1000000000000), orderedInterval (-25258934077 / 1000000000000) (-25258865603 / 1000000000000)))) (orderedInterval (-63678763744 / 1000000000000) (-63678492712 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 4) <| besselDerivativeNearFromState (1108752456227269 / 4000000000000) 4 (IntervalRat.scale (259 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (47843651694 / 1000000000000) (47843651746 / 1000000000000), orderedInterval (2686401773 / 1000000000000) (2686401825 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 4) <| besselDerivativeNearFromState (791258069995477 / 4000000000000) 4 (IntervalRat.scale (259 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-35624735973 / 1000000000000) (-35624735972 / 1000000000000), orderedInterval (-44059094545 / 1000000000000) (-44059094544 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 4) <| besselDerivativeNearFromState (897202318320483 / 4000000000000) 4 (IntervalRat.scale (259 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-47700684772 / 1000000000000) (-47700667185 / 1000000000000), orderedInterval (23831524538 / 1000000000000) (23831542125 / 1000000000000)))) (orderedInterval (-34542833267 / 1000000000000) (-34542832315 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 4) <| besselDerivativeNearFromState (747993754971827 / 4000000000000) 4 (IntervalRat.scale (259 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-38138389888 / 1000000000000) (-38138364022 / 1000000000000), orderedInterval (44259385770 / 1000000000000) (44259411636 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 4) <| besselDerivativeNearFromState (660875166892367 / 4000000000000) 4 (IntervalRat.scale (259 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (29813057490 / 1000000000000) (29813060972 / 1000000000000), orderedInterval (-54536374054 / 1000000000000) (-54536370571 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 4) <| besselDerivativeNearFromState (191547382212333 / 800000000000) 4 (IntervalRat.scale (259 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (51236668650 / 1000000000000) (51236668667 / 1000000000000), orderedInterval (5693733669 / 1000000000000) (5693733686 / 1000000000000)))) (orderedInterval (9033254287 / 1000000000000) (9033256205 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate254_chunkChecks4_2 :
    compactCertificate254.chunkChecks (4 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 4) <| besselDerivativeNearFromState (529830139785751 / 4000000000000) 4 (IntervalRat.scale (259 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (66708546741 / 1000000000000) (66708546742 / 1000000000000), orderedInterval (18620354663 / 1000000000000) (18620354664 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 4) <| besselDerivativeNearFromState (449142877204511 / 4000000000000) 4 (IntervalRat.scale (259 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-2057695343 / 1000000000000) (-2057695334 / 1000000000000), orderedInterval (75278435823 / 1000000000000) (75278435832 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 4) <| besselDerivativeNearFromState (281052758182133 / 4000000000000) 4 (IntervalRat.scale (259 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (89051065297 / 1000000000000) (89051068159 / 1000000000000), orderedInterval (-34252669659 / 1000000000000) (-34252666798 / 1000000000000)))) (orderedInterval (-11450396222 / 1000000000000) (-11450396185 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 4) <| besselDerivativeNearFromState (151151108089611 / 4000000000000) 4 (IntervalRat.scale (259 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (99266498633 / 1000000000000) (99266498634 / 1000000000000), orderedInterval (82311827836 / 1000000000000) (82311827837 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 4) <| besselDerivativeNearFromState (410404661541833 / 4000000000000) 4 (IntervalRat.scale (259 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (22313974182 / 1000000000000) (22313974593 / 1000000000000), orderedInterval (-75653090076 / 1000000000000) (-75653089666 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 4) <| besselDerivativeNearFromState (560372478761641 / 4000000000000) 4 (IntervalRat.scale (259 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (31965584168 / 1000000000000) (31965587871 / 1000000000000), orderedInterval (-59464561086 / 1000000000000) (-59464557383 / 1000000000000)))) (orderedInterval (-3465684787 / 1000000000000) (-3465684374 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 4) <| besselDerivativeNearFromState (236947241817867 / 4000000000000) 4 (IntervalRat.scale (259 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-33576401571 / 1000000000000) (-33576401570 / 1000000000000), orderedInterval (-97797994084 / 1000000000000) (-97797994083 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 4) <| besselDerivativeNearFromState (963177383072107 / 4000000000000) 4 (IntervalRat.scale (259 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (16340747182 / 1000000000000) (16340747450 / 1000000000000), orderedInterval (-48786535182 / 1000000000000) (-48786534915 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 4) <| besselDerivativeNearFromState (643357854338213 / 4000000000000) 4 (IntervalRat.scale (259 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-62028249681 / 1000000000000) (-62028249677 / 1000000000000), orderedInterval (-10323114263 / 1000000000000) (-10323114259 / 1000000000000)))) (orderedInterval (12232255359 / 1000000000000) (12232255809 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate254_chunkChecks4 :
    compactCertificate254.chunkChecks (4 : Fin 5) 0 9 = true :=
  compactCertificate254.chunkChecks_nine_of_three (4 : Fin 5) compactCertificate254_chunkChecks4_0
    compactCertificate254_chunkChecks4_1 compactCertificate254_chunkChecks4_2

theorem compactCertificate254_chunks :
    ∀ r : Fin 5, ∀ b, compactCertificate254.chunkCheck r b = true :=
  compactCertificate254.chunkChecks_all (by
    intro r
    fin_cases r
    · exact compactCertificate254_chunkChecks0
    · exact compactCertificate254_chunkChecks1
    · exact compactCertificate254_chunkChecks2
    · exact compactCertificate254_chunkChecks3
    · exact compactCertificate254_chunkChecks4)

theorem compactCertificate254_coefficient0 :
    compactCertificate254.coefficientCheck (0 : Fin 5) = true := by
  norm_num [CompactCertificate.coefficientCheck, intervalFinSumHull,
    compactCertificate254, rationalIntervalSubset, orderedInterval, Fin.sum_univ_succ]

theorem compactCertificate254_coefficient1 :
    compactCertificate254.coefficientCheck (1 : Fin 5) = true := by
  norm_num [CompactCertificate.coefficientCheck, intervalFinSumHull,
    compactCertificate254, rationalIntervalSubset, orderedInterval, Fin.sum_univ_succ]

theorem compactCertificate254_coefficient2 :
    compactCertificate254.coefficientCheck (2 : Fin 5) = true := by
  norm_num [CompactCertificate.coefficientCheck, intervalFinSumHull,
    compactCertificate254, rationalIntervalSubset, orderedInterval, Fin.sum_univ_succ]

theorem compactCertificate254_coefficient3 :
    compactCertificate254.coefficientCheck (3 : Fin 5) = true := by
  norm_num [CompactCertificate.coefficientCheck, intervalFinSumHull,
    compactCertificate254, rationalIntervalSubset, orderedInterval, Fin.sum_univ_succ]

theorem compactCertificate254_coefficient4 :
    compactCertificate254.coefficientCheck (4 : Fin 5) = true := by
  norm_num [CompactCertificate.coefficientCheck, intervalFinSumHull,
    compactCertificate254, rationalIntervalSubset, orderedInterval, Fin.sum_univ_succ]

theorem compactCertificate254_coefficients : ∀ r : Fin 5,
    compactCertificate254.coefficientCheck r = true := by
  intro r
  fin_cases r
  · exact compactCertificate254_coefficient0
  · exact compactCertificate254_coefficient1
  · exact compactCertificate254_coefficient2
  · exact compactCertificate254_coefficient3
  · exact compactCertificate254_coefficient4

theorem compactCertificate254_lower : (1 : ℚ) ≤ compactCertificate254.output.lo := by
  norm_num [CompactCertificate.output, CompactCertificate.interval,
    CompactCertificate.coefficientTargetNat, compactCertificate254, dualConstant,
    intervalTaylorSum, intervalPow, intervalSub, intervalMaxAbs, widenInterval,
    rationalErrorInterval, orderedInterval, IntervalRat.add, IntervalRat.mul, IntervalRat.scale,
    IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4]

theorem compactCertificate254_proves {t : ℝ} (ht : t ∈ compactCertificate254.interval) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t :=
  compactCertificate254.proves compactCertificate254_states compactCertificate254_chunks
    compactCertificate254_coefficients compactCertificate254_lower ht

end Erdos232
