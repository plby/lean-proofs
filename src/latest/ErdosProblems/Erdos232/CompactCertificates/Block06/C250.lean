/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, OpenAI Codex
-/
import ErdosProblems.Erdos232.CompactBase

open LeanCert.Core
namespace Erdos232

def compactCertificate250 : CompactCertificate where
  left := 125
  right := 126
  center := 251 / 2
  grid := fun i =>
    match i.val with
    | 0 => 40
    | 1 => 29
    | 2 => 48
    | 3 => 9
    | 4 => 23
    | 5 => 63
    | 6 => 46
    | 7 => 79
    | 8 => 58
    | 9 => 89
    | 10 => 52
    | 11 => 92
    | 12 => 86
    | 13 => 61
    | 14 => 69
    | 15 => 58
    | 16 => 51
    | 17 => 74
    | 18 => 41
    | 19 => 35
    | 20 => 22
    | 21 => 12
    | 22 => 32
    | 23 => 43
    | 24 => 18
    | 25 => 74
    | _ => 50
  point := fun i =>
    match i.val with
    | 0 => 251 / 2
    | 1 => 369770927923151 / 4000000000000
    | 2 => 119576320667183 / 800000000000
    | 3 => 107898234546157 / 4000000000000
    | 4 => 289829835133129 / 4000000000000
    | 5 => 786944382318693 / 4000000000000
    | 6 => 579659670266509 / 4000000000000
    | 7 => 993256724984257 / 4000000000000
    | 8 => 731628408093763 / 4000000000000
    | 9 => 1122506124704749 / 4000000000000
    | 10 => 648079213265221 / 4000000000000
    | 11 => 1150027936642889 / 4000000000000
    | 12 => 1074505276112141 / 4000000000000
    | 13 => 766817666289053 / 4000000000000
    | 14 => 869489505399387 / 4000000000000
    | 15 => 724889700764203 / 4000000000000
    | 16 => 640462034324263 / 4000000000000
    | 17 => 185630860754037 / 800000000000
    | 18 => 513464730062639 / 4000000000000
    | 19 => 435269738140279 / 4000000000000
    | 20 => 272371591906237 / 4000000000000
    | 21 => 146482347994179 / 4000000000000
    | 22 => 397728069679537 / 4000000000000
    | 23 => 543063676328849 / 4000000000000
    | 24 => 229628408093763 / 4000000000000
    | 25 => 933426730313123 / 4000000000000
    | _ => 623485797061357 / 4000000000000
  state := fun i =>
    match i.val with
    | 0 => (orderedInterval (41423043043 / 1000000000000) (41423043044 / 1000000000000), orderedInterval (57772972228 / 1000000000000) (57772972229 / 1000000000000))
    | 1 => (orderedInterval (-70755805603 / 1000000000000) (-70755783908 / 1000000000000), orderedInterval (43744080611 / 1000000000000) (43744102306 / 1000000000000))
    | 2 => (orderedInterval (-33636680044 / 1000000000000) (-33636674226 / 1000000000000), orderedInterval (56038847231 / 1000000000000) (56038853050 / 1000000000000))
    | 3 => (orderedInterval (76194530497 / 1000000000000) (76194538901 / 1000000000000), orderedInterval (-134817994594 / 1000000000000) (-134817986190 / 1000000000000))
    | 4 => (orderedInterval (-78079369423 / 1000000000000) (-78079369422 / 1000000000000), orderedInterval (-51323055547 / 1000000000000) (-51323055546 / 1000000000000))
    | 5 => (orderedInterval (22124728815 / 1000000000000) (22124729732 / 1000000000000), orderedInterval (-52462440671 / 1000000000000) (-52462439755 / 1000000000000))
    | 6 => (orderedInterval (61437983035 / 1000000000000) (61437983036 / 1000000000000), orderedInterval (24655961880 / 1000000000000) (24655961881 / 1000000000000))
    | 7 => (orderedInterval (-40076405307 / 1000000000000) (-40076405306 / 1000000000000), orderedInterval (-30865186772 / 1000000000000) (-30865186771 / 1000000000000))
    | 8 => (orderedInterval (58750186236 / 1000000000000) (58750186252 / 1000000000000), orderedInterval (5221432131 / 1000000000000) (5221432146 / 1000000000000))
    | 9 => (orderedInterval (-46276230890 / 1000000000000) (-46276228510 / 1000000000000), orderedInterval (11355126795 / 1000000000000) (11355129175 / 1000000000000))
    | 10 => (orderedInterval (-33211091467 / 1000000000000) (-33211084973 / 1000000000000), orderedInterval (53265473334 / 1000000000000) (53265479828 / 1000000000000))
    | 11 => (orderedInterval (-31540413374 / 1000000000000) (-31540393579 / 1000000000000), orderedInterval (34975882395 / 1000000000000) (34975902190 / 1000000000000))
    | 12 => (orderedInterval (-33739014590 / 1000000000000) (-33738985661 / 1000000000000), orderedInterval (35156777883 / 1000000000000) (35156806812 / 1000000000000))
    | 13 => (orderedInterval (-43370151555 / 1000000000000) (-43370151554 / 1000000000000), orderedInterval (-37832487469 / 1000000000000) (-37832487468 / 1000000000000))
    | 14 => (orderedInterval (-53208973089 / 1000000000000) (-53208973084 / 1000000000000), orderedInterval (-9752015828 / 1000000000000) (-9752015823 / 1000000000000))
    | 15 => (orderedInterval (-12079323578 / 1000000000000) (-12079323498 / 1000000000000), orderedInterval (58059369457 / 1000000000000) (58059369537 / 1000000000000))
    | 16 => (orderedInterval (-39594876509 / 1000000000000) (-39594876508 / 1000000000000), orderedInterval (-48950311271 / 1000000000000) (-48950311270 / 1000000000000))
    | 17 => (orderedInterval (17743035550 / 1000000000000) (17743035551 / 1000000000000), orderedInterval (49244463458 / 1000000000000) (49244463459 / 1000000000000))
    | 18 => (orderedInterval (-23837166705 / 1000000000000) (-23837166704 / 1000000000000), orderedInterval (-66173453623 / 1000000000000) (-66173453622 / 1000000000000))
    | 19 => (orderedInterval (26518689116 / 1000000000000) (26518690018 / 1000000000000), orderedInterval (-71865510423 / 1000000000000) (-71865509521 / 1000000000000))
    | 20 => (orderedInterval (-22849960588 / 1000000000000) (-22849960316 / 1000000000000), orderedInterval (94121946285 / 1000000000000) (94121946557 / 1000000000000))
    | 21 => (orderedInterval (-38526087786 / 1000000000000) (-38526087105 / 1000000000000), orderedInterval (126626224556 / 1000000000000) (126626225237 / 1000000000000))
    | 22 => (orderedInterval (-24775395169 / 1000000000000) (-24775394577 / 1000000000000), orderedInterval (76208800208 / 1000000000000) (76208800800 / 1000000000000))
    | 23 => (orderedInterval (-68071241655 / 1000000000000) (-68071241647 / 1000000000000), orderedInterval (-7190650622 / 1000000000000) (-7190650614 / 1000000000000))
    | 24 => (orderedInterval (105040748428 / 1000000000000) (105040748497 / 1000000000000), orderedInterval (-8370654826 / 1000000000000) (-8370654757 / 1000000000000))
    | 25 => (orderedInterval (52005943135 / 1000000000000) (52005943443 / 1000000000000), orderedInterval (-4956341039 / 1000000000000) (-4956340730 / 1000000000000))
    | _ => (orderedInterval (-26268338711 / 1000000000000) (-26268337163 / 1000000000000), orderedInterval (58344452681 / 1000000000000) (58344454229 / 1000000000000))
  chunkTarget := fun r b =>
    match r.val with
    | 0 =>
      match b.val with
      | 0 => orderedInterval (13785498588 / 1000000000000) (13785499142 / 1000000000000)
      | 1 => orderedInterval (-5250309931 / 1000000000000) (-5250309759 / 1000000000000)
      | 2 => orderedInterval (2655992769 / 1000000000000) (2655992777 / 1000000000000)
      | 3 => orderedInterval (1278402861 / 1000000000000) (1278406629 / 1000000000000)
      | 4 => orderedInterval (-3222844976 / 1000000000000) (-3222844438 / 1000000000000)
      | 5 => orderedInterval (2580686955 / 1000000000000) (2580686969 / 1000000000000)
      | 6 => orderedInterval (1566539431 / 1000000000000) (1566539523 / 1000000000000)
      | 7 => orderedInterval (6490367695 / 1000000000000) (6490367738 / 1000000000000)
      | _ => orderedInterval (1328480728 / 1000000000000) (1328481080 / 1000000000000)
    | 1 =>
      match b.val with
      | 0 => orderedInterval (27115937103 / 1000000000000) (27115937670 / 1000000000000)
      | 1 => orderedInterval (5078978989 / 1000000000000) (5078979129 / 1000000000000)
      | 2 => orderedInterval (2067553094 / 1000000000000) (2067553107 / 1000000000000)
      | 3 => orderedInterval (11973686772 / 1000000000000) (11973694889 / 1000000000000)
      | 4 => orderedInterval (-6737836379 / 1000000000000) (-6737835236 / 1000000000000)
      | 5 => orderedInterval (6873250130 / 1000000000000) (6873250149 / 1000000000000)
      | 6 => orderedInterval (16011695377 / 1000000000000) (16011695456 / 1000000000000)
      | 7 => orderedInterval (-1455925098 / 1000000000000) (-1455925069 / 1000000000000)
      | _ => orderedInterval (-12869064379 / 1000000000000) (-12869063922 / 1000000000000)
    | 2 =>
      match b.val with
      | 0 => orderedInterval (-13477136973 / 1000000000000) (-13477136362 / 1000000000000)
      | 1 => orderedInterval (4813128381 / 1000000000000) (4813128571 / 1000000000000)
      | 2 => orderedInterval (-7871641113 / 1000000000000) (-7871641089 / 1000000000000)
      | 3 => orderedInterval (-13576881273 / 1000000000000) (-13576863303 / 1000000000000)
      | 4 => orderedInterval (6024790203 / 1000000000000) (6024792646 / 1000000000000)
      | 5 => orderedInterval (-5005121478 / 1000000000000) (-5005121449 / 1000000000000)
      | 6 => orderedInterval (-2767616304 / 1000000000000) (-2767616233 / 1000000000000)
      | 7 => orderedInterval (-6507093990 / 1000000000000) (-6507093965 / 1000000000000)
      | _ => orderedInterval (7003855114 / 1000000000000) (7003855725 / 1000000000000)
    | 3 =>
      match b.val with
      | 0 => orderedInterval (-28508466557 / 1000000000000) (-28508465881 / 1000000000000)
      | 1 => orderedInterval (-14059242332 / 1000000000000) (-14059242043 / 1000000000000)
      | 2 => orderedInterval (-7701967375 / 1000000000000) (-7701967333 / 1000000000000)
      | 3 => orderedInterval (-45603307013 / 1000000000000) (-45603266793 / 1000000000000)
      | 4 => orderedInterval (18670398952 / 1000000000000) (18670404162 / 1000000000000)
      | 5 => orderedInterval (-15764883300 / 1000000000000) (-15764883256 / 1000000000000)
      | 6 => orderedInterval (-14440154639 / 1000000000000) (-14440154576 / 1000000000000)
      | 7 => orderedInterval (272024831 / 1000000000000) (272024853 / 1000000000000)
      | _ => orderedInterval (18327562594 / 1000000000000) (18327563428 / 1000000000000)
    | _ =>
      match b.val with
      | 0 => orderedInterval (12706475302 / 1000000000000) (12706476076 / 1000000000000)
      | 1 => orderedInterval (-9592460228 / 1000000000000) (-9592459775 / 1000000000000)
      | 2 => orderedInterval (25473227753 / 1000000000000) (25473227829 / 1000000000000)
      | 3 => orderedInterval (75963417998 / 1000000000000) (75963509118 / 1000000000000)
      | 4 => orderedInterval (-7417464012 / 1000000000000) (-7417452849 / 1000000000000)
      | 5 => orderedInterval (10956680143 / 1000000000000) (10956680211 / 1000000000000)
      | 6 => orderedInterval (3488769364 / 1000000000000) (3488769422 / 1000000000000)
      | 7 => orderedInterval (7366863520 / 1000000000000) (7366863542 / 1000000000000)
      | _ => orderedInterval (-39140995520 / 1000000000000) (-39140994338 / 1000000000000)
  coefficientTarget := fun i =>
    match i.val with
    | 0 => orderedInterval (21212814120 / 1000000000000) (21212819661 / 1000000000000)
    | 1 => orderedInterval (48058275609 / 1000000000000) (48058286173 / 1000000000000)
    | 2 => orderedInterval (-31363717433 / 1000000000000) (-31363695459 / 1000000000000)
    | 3 => orderedInterval (-88808034839 / 1000000000000) (-88807987439 / 1000000000000)
    | _ => orderedInterval (79804514320 / 1000000000000) (79804619236 / 1000000000000)

theorem compactCertificate250_stateChecks0 :
    compactCertificate250.stateChecks 0 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 40 12 (251 / 2)) (orderedInterval (41423043043 / 1000000000000) (41423043044 / 1000000000000), orderedInterval (57772972228 / 1000000000000) (57772972229 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 29 12 (369770927923151 / 4000000000000)) (orderedInterval (-70755805603 / 1000000000000) (-70755783908 / 1000000000000), orderedInterval (43744080611 / 1000000000000) (43744102306 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 48 12 (119576320667183 / 800000000000)) (orderedInterval (-33636680044 / 1000000000000) (-33636674226 / 1000000000000), orderedInterval (56038847231 / 1000000000000) (56038853050 / 1000000000000))) = true
  norm_num [besselStateAtRationalPoint, besselIntervalStepZero,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, besselZeroTransition,
    besselInitial, besselGridStateAt, besselGridStateBlock00, besselGridStateBlock01,
    besselGridStateBlock02, besselGridStateBlock03, besselGridStateBlock04,
    besselGridStateBlock05, besselGridStateBlock06, besselGridStateBlock07,
    besselGridStateBlock08, besselGridStateBlock09, besselGridStateBlock10,
    besselGridStateBlock11, besselGridStateBlock12, besselGridStateBlock13,
    besselGridStateBlock14, besselGridState009, besselGridState012, besselGridState018, besselGridState022, besselGridState023, besselGridState029, besselGridState032, besselGridState035, besselGridState040, besselGridState041, besselGridState043, besselGridState046, besselGridState048, besselGridState050, besselGridState051, besselGridState052, besselGridState058, besselGridState061, besselGridState063, besselGridState069, besselGridState074, besselGridState079, besselGridState086, besselGridState089, besselGridState092, besselStateSubset, linearInterval, widenInterval,
    rationalErrorInterval, rationalIntervalSubset, orderedInterval, Finset.sum_range_succ,
    IntervalRat.add, IntervalRat.mul, IntervalRat.scale, IntervalRat.singleton]

theorem compactCertificate250_stateChecks1 :
    compactCertificate250.stateChecks 3 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 9 12 (107898234546157 / 4000000000000)) (orderedInterval (76194530497 / 1000000000000) (76194538901 / 1000000000000), orderedInterval (-134817994594 / 1000000000000) (-134817986190 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 23 12 (289829835133129 / 4000000000000)) (orderedInterval (-78079369423 / 1000000000000) (-78079369422 / 1000000000000), orderedInterval (-51323055547 / 1000000000000) (-51323055546 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 63 12 (786944382318693 / 4000000000000)) (orderedInterval (22124728815 / 1000000000000) (22124729732 / 1000000000000), orderedInterval (-52462440671 / 1000000000000) (-52462439755 / 1000000000000))) = true
  norm_num [besselStateAtRationalPoint, besselIntervalStepZero,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, besselZeroTransition,
    besselInitial, besselGridStateAt, besselGridStateBlock00, besselGridStateBlock01,
    besselGridStateBlock02, besselGridStateBlock03, besselGridStateBlock04,
    besselGridStateBlock05, besselGridStateBlock06, besselGridStateBlock07,
    besselGridStateBlock08, besselGridStateBlock09, besselGridStateBlock10,
    besselGridStateBlock11, besselGridStateBlock12, besselGridStateBlock13,
    besselGridStateBlock14, besselGridState009, besselGridState012, besselGridState018, besselGridState022, besselGridState023, besselGridState029, besselGridState032, besselGridState035, besselGridState040, besselGridState041, besselGridState043, besselGridState046, besselGridState048, besselGridState050, besselGridState051, besselGridState052, besselGridState058, besselGridState061, besselGridState063, besselGridState069, besselGridState074, besselGridState079, besselGridState086, besselGridState089, besselGridState092, besselStateSubset, linearInterval, widenInterval,
    rationalErrorInterval, rationalIntervalSubset, orderedInterval, Finset.sum_range_succ,
    IntervalRat.add, IntervalRat.mul, IntervalRat.scale, IntervalRat.singleton]

theorem compactCertificate250_stateChecks2 :
    compactCertificate250.stateChecks 6 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 46 12 (579659670266509 / 4000000000000)) (orderedInterval (61437983035 / 1000000000000) (61437983036 / 1000000000000), orderedInterval (24655961880 / 1000000000000) (24655961881 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 79 12 (993256724984257 / 4000000000000)) (orderedInterval (-40076405307 / 1000000000000) (-40076405306 / 1000000000000), orderedInterval (-30865186772 / 1000000000000) (-30865186771 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 58 12 (731628408093763 / 4000000000000)) (orderedInterval (58750186236 / 1000000000000) (58750186252 / 1000000000000), orderedInterval (5221432131 / 1000000000000) (5221432146 / 1000000000000))) = true
  norm_num [besselStateAtRationalPoint, besselIntervalStepZero,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, besselZeroTransition,
    besselInitial, besselGridStateAt, besselGridStateBlock00, besselGridStateBlock01,
    besselGridStateBlock02, besselGridStateBlock03, besselGridStateBlock04,
    besselGridStateBlock05, besselGridStateBlock06, besselGridStateBlock07,
    besselGridStateBlock08, besselGridStateBlock09, besselGridStateBlock10,
    besselGridStateBlock11, besselGridStateBlock12, besselGridStateBlock13,
    besselGridStateBlock14, besselGridState009, besselGridState012, besselGridState018, besselGridState022, besselGridState023, besselGridState029, besselGridState032, besselGridState035, besselGridState040, besselGridState041, besselGridState043, besselGridState046, besselGridState048, besselGridState050, besselGridState051, besselGridState052, besselGridState058, besselGridState061, besselGridState063, besselGridState069, besselGridState074, besselGridState079, besselGridState086, besselGridState089, besselGridState092, besselStateSubset, linearInterval, widenInterval,
    rationalErrorInterval, rationalIntervalSubset, orderedInterval, Finset.sum_range_succ,
    IntervalRat.add, IntervalRat.mul, IntervalRat.scale, IntervalRat.singleton]

theorem compactCertificate250_stateChecks3 :
    compactCertificate250.stateChecks 9 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 89 12 (1122506124704749 / 4000000000000)) (orderedInterval (-46276230890 / 1000000000000) (-46276228510 / 1000000000000), orderedInterval (11355126795 / 1000000000000) (11355129175 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 52 12 (648079213265221 / 4000000000000)) (orderedInterval (-33211091467 / 1000000000000) (-33211084973 / 1000000000000), orderedInterval (53265473334 / 1000000000000) (53265479828 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 92 12 (1150027936642889 / 4000000000000)) (orderedInterval (-31540413374 / 1000000000000) (-31540393579 / 1000000000000), orderedInterval (34975882395 / 1000000000000) (34975902190 / 1000000000000))) = true
  norm_num [besselStateAtRationalPoint, besselIntervalStepZero,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, besselZeroTransition,
    besselInitial, besselGridStateAt, besselGridStateBlock00, besselGridStateBlock01,
    besselGridStateBlock02, besselGridStateBlock03, besselGridStateBlock04,
    besselGridStateBlock05, besselGridStateBlock06, besselGridStateBlock07,
    besselGridStateBlock08, besselGridStateBlock09, besselGridStateBlock10,
    besselGridStateBlock11, besselGridStateBlock12, besselGridStateBlock13,
    besselGridStateBlock14, besselGridState009, besselGridState012, besselGridState018, besselGridState022, besselGridState023, besselGridState029, besselGridState032, besselGridState035, besselGridState040, besselGridState041, besselGridState043, besselGridState046, besselGridState048, besselGridState050, besselGridState051, besselGridState052, besselGridState058, besselGridState061, besselGridState063, besselGridState069, besselGridState074, besselGridState079, besselGridState086, besselGridState089, besselGridState092, besselStateSubset, linearInterval, widenInterval,
    rationalErrorInterval, rationalIntervalSubset, orderedInterval, Finset.sum_range_succ,
    IntervalRat.add, IntervalRat.mul, IntervalRat.scale, IntervalRat.singleton]

theorem compactCertificate250_stateChecks4 :
    compactCertificate250.stateChecks 12 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 86 12 (1074505276112141 / 4000000000000)) (orderedInterval (-33739014590 / 1000000000000) (-33738985661 / 1000000000000), orderedInterval (35156777883 / 1000000000000) (35156806812 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 61 12 (766817666289053 / 4000000000000)) (orderedInterval (-43370151555 / 1000000000000) (-43370151554 / 1000000000000), orderedInterval (-37832487469 / 1000000000000) (-37832487468 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 69 12 (869489505399387 / 4000000000000)) (orderedInterval (-53208973089 / 1000000000000) (-53208973084 / 1000000000000), orderedInterval (-9752015828 / 1000000000000) (-9752015823 / 1000000000000))) = true
  norm_num [besselStateAtRationalPoint, besselIntervalStepZero,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, besselZeroTransition,
    besselInitial, besselGridStateAt, besselGridStateBlock00, besselGridStateBlock01,
    besselGridStateBlock02, besselGridStateBlock03, besselGridStateBlock04,
    besselGridStateBlock05, besselGridStateBlock06, besselGridStateBlock07,
    besselGridStateBlock08, besselGridStateBlock09, besselGridStateBlock10,
    besselGridStateBlock11, besselGridStateBlock12, besselGridStateBlock13,
    besselGridStateBlock14, besselGridState009, besselGridState012, besselGridState018, besselGridState022, besselGridState023, besselGridState029, besselGridState032, besselGridState035, besselGridState040, besselGridState041, besselGridState043, besselGridState046, besselGridState048, besselGridState050, besselGridState051, besselGridState052, besselGridState058, besselGridState061, besselGridState063, besselGridState069, besselGridState074, besselGridState079, besselGridState086, besselGridState089, besselGridState092, besselStateSubset, linearInterval, widenInterval,
    rationalErrorInterval, rationalIntervalSubset, orderedInterval, Finset.sum_range_succ,
    IntervalRat.add, IntervalRat.mul, IntervalRat.scale, IntervalRat.singleton]

theorem compactCertificate250_stateChecks5 :
    compactCertificate250.stateChecks 15 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 58 12 (724889700764203 / 4000000000000)) (orderedInterval (-12079323578 / 1000000000000) (-12079323498 / 1000000000000), orderedInterval (58059369457 / 1000000000000) (58059369537 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 51 12 (640462034324263 / 4000000000000)) (orderedInterval (-39594876509 / 1000000000000) (-39594876508 / 1000000000000), orderedInterval (-48950311271 / 1000000000000) (-48950311270 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 74 12 (185630860754037 / 800000000000)) (orderedInterval (17743035550 / 1000000000000) (17743035551 / 1000000000000), orderedInterval (49244463458 / 1000000000000) (49244463459 / 1000000000000))) = true
  norm_num [besselStateAtRationalPoint, besselIntervalStepZero,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, besselZeroTransition,
    besselInitial, besselGridStateAt, besselGridStateBlock00, besselGridStateBlock01,
    besselGridStateBlock02, besselGridStateBlock03, besselGridStateBlock04,
    besselGridStateBlock05, besselGridStateBlock06, besselGridStateBlock07,
    besselGridStateBlock08, besselGridStateBlock09, besselGridStateBlock10,
    besselGridStateBlock11, besselGridStateBlock12, besselGridStateBlock13,
    besselGridStateBlock14, besselGridState009, besselGridState012, besselGridState018, besselGridState022, besselGridState023, besselGridState029, besselGridState032, besselGridState035, besselGridState040, besselGridState041, besselGridState043, besselGridState046, besselGridState048, besselGridState050, besselGridState051, besselGridState052, besselGridState058, besselGridState061, besselGridState063, besselGridState069, besselGridState074, besselGridState079, besselGridState086, besselGridState089, besselGridState092, besselStateSubset, linearInterval, widenInterval,
    rationalErrorInterval, rationalIntervalSubset, orderedInterval, Finset.sum_range_succ,
    IntervalRat.add, IntervalRat.mul, IntervalRat.scale, IntervalRat.singleton]

theorem compactCertificate250_stateChecks6 :
    compactCertificate250.stateChecks 18 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 41 12 (513464730062639 / 4000000000000)) (orderedInterval (-23837166705 / 1000000000000) (-23837166704 / 1000000000000), orderedInterval (-66173453623 / 1000000000000) (-66173453622 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 35 12 (435269738140279 / 4000000000000)) (orderedInterval (26518689116 / 1000000000000) (26518690018 / 1000000000000), orderedInterval (-71865510423 / 1000000000000) (-71865509521 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 22 12 (272371591906237 / 4000000000000)) (orderedInterval (-22849960588 / 1000000000000) (-22849960316 / 1000000000000), orderedInterval (94121946285 / 1000000000000) (94121946557 / 1000000000000))) = true
  norm_num [besselStateAtRationalPoint, besselIntervalStepZero,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, besselZeroTransition,
    besselInitial, besselGridStateAt, besselGridStateBlock00, besselGridStateBlock01,
    besselGridStateBlock02, besselGridStateBlock03, besselGridStateBlock04,
    besselGridStateBlock05, besselGridStateBlock06, besselGridStateBlock07,
    besselGridStateBlock08, besselGridStateBlock09, besselGridStateBlock10,
    besselGridStateBlock11, besselGridStateBlock12, besselGridStateBlock13,
    besselGridStateBlock14, besselGridState009, besselGridState012, besselGridState018, besselGridState022, besselGridState023, besselGridState029, besselGridState032, besselGridState035, besselGridState040, besselGridState041, besselGridState043, besselGridState046, besselGridState048, besselGridState050, besselGridState051, besselGridState052, besselGridState058, besselGridState061, besselGridState063, besselGridState069, besselGridState074, besselGridState079, besselGridState086, besselGridState089, besselGridState092, besselStateSubset, linearInterval, widenInterval,
    rationalErrorInterval, rationalIntervalSubset, orderedInterval, Finset.sum_range_succ,
    IntervalRat.add, IntervalRat.mul, IntervalRat.scale, IntervalRat.singleton]

theorem compactCertificate250_stateChecks7 :
    compactCertificate250.stateChecks 21 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 12 12 (146482347994179 / 4000000000000)) (orderedInterval (-38526087786 / 1000000000000) (-38526087105 / 1000000000000), orderedInterval (126626224556 / 1000000000000) (126626225237 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 32 12 (397728069679537 / 4000000000000)) (orderedInterval (-24775395169 / 1000000000000) (-24775394577 / 1000000000000), orderedInterval (76208800208 / 1000000000000) (76208800800 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 43 12 (543063676328849 / 4000000000000)) (orderedInterval (-68071241655 / 1000000000000) (-68071241647 / 1000000000000), orderedInterval (-7190650622 / 1000000000000) (-7190650614 / 1000000000000))) = true
  norm_num [besselStateAtRationalPoint, besselIntervalStepZero,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, besselZeroTransition,
    besselInitial, besselGridStateAt, besselGridStateBlock00, besselGridStateBlock01,
    besselGridStateBlock02, besselGridStateBlock03, besselGridStateBlock04,
    besselGridStateBlock05, besselGridStateBlock06, besselGridStateBlock07,
    besselGridStateBlock08, besselGridStateBlock09, besselGridStateBlock10,
    besselGridStateBlock11, besselGridStateBlock12, besselGridStateBlock13,
    besselGridStateBlock14, besselGridState009, besselGridState012, besselGridState018, besselGridState022, besselGridState023, besselGridState029, besselGridState032, besselGridState035, besselGridState040, besselGridState041, besselGridState043, besselGridState046, besselGridState048, besselGridState050, besselGridState051, besselGridState052, besselGridState058, besselGridState061, besselGridState063, besselGridState069, besselGridState074, besselGridState079, besselGridState086, besselGridState089, besselGridState092, besselStateSubset, linearInterval, widenInterval,
    rationalErrorInterval, rationalIntervalSubset, orderedInterval, Finset.sum_range_succ,
    IntervalRat.add, IntervalRat.mul, IntervalRat.scale, IntervalRat.singleton]

theorem compactCertificate250_stateChecks8 :
    compactCertificate250.stateChecks 24 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 18 12 (229628408093763 / 4000000000000)) (orderedInterval (105040748428 / 1000000000000) (105040748497 / 1000000000000), orderedInterval (-8370654826 / 1000000000000) (-8370654757 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 74 12 (933426730313123 / 4000000000000)) (orderedInterval (52005943135 / 1000000000000) (52005943443 / 1000000000000), orderedInterval (-4956341039 / 1000000000000) (-4956340730 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 50 12 (623485797061357 / 4000000000000)) (orderedInterval (-26268338711 / 1000000000000) (-26268337163 / 1000000000000), orderedInterval (58344452681 / 1000000000000) (58344454229 / 1000000000000))) = true
  norm_num [besselStateAtRationalPoint, besselIntervalStepZero,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, besselZeroTransition,
    besselInitial, besselGridStateAt, besselGridStateBlock00, besselGridStateBlock01,
    besselGridStateBlock02, besselGridStateBlock03, besselGridStateBlock04,
    besselGridStateBlock05, besselGridStateBlock06, besselGridStateBlock07,
    besselGridStateBlock08, besselGridStateBlock09, besselGridStateBlock10,
    besselGridStateBlock11, besselGridStateBlock12, besselGridStateBlock13,
    besselGridStateBlock14, besselGridState009, besselGridState012, besselGridState018, besselGridState022, besselGridState023, besselGridState029, besselGridState032, besselGridState035, besselGridState040, besselGridState041, besselGridState043, besselGridState046, besselGridState048, besselGridState050, besselGridState051, besselGridState052, besselGridState058, besselGridState061, besselGridState063, besselGridState069, besselGridState074, besselGridState079, besselGridState086, besselGridState089, besselGridState092, besselStateSubset, linearInterval, widenInterval,
    rationalErrorInterval, rationalIntervalSubset, orderedInterval, Finset.sum_range_succ,
    IntervalRat.add, IntervalRat.mul, IntervalRat.scale, IntervalRat.singleton]

theorem compactCertificate250_states : ∀ j,
    BesselStateValid (compactCertificate250.point j) (compactCertificate250.state j) :=
  compactCertificate250.statesValid_of_checks3 compactCertificate250_stateChecks0
    compactCertificate250_stateChecks1 compactCertificate250_stateChecks2
    compactCertificate250_stateChecks3 compactCertificate250_stateChecks4
    compactCertificate250_stateChecks5 compactCertificate250_stateChecks6
    compactCertificate250_stateChecks7 compactCertificate250_stateChecks8

theorem compactCertificate250_chunkChecks0_0 :
    compactCertificate250.chunkChecks (0 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 0) <| besselDerivativeNearFromState (251 / 2) 0 (IntervalRat.scale (251 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (41423043043 / 1000000000000) (41423043044 / 1000000000000), orderedInterval (57772972228 / 1000000000000) (57772972229 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 0) <| besselDerivativeNearFromState (369770927923151 / 4000000000000) 0 (IntervalRat.scale (251 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-70755805603 / 1000000000000) (-70755783908 / 1000000000000), orderedInterval (43744080611 / 1000000000000) (43744102306 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 0) <| besselDerivativeNearFromState (119576320667183 / 800000000000) 0 (IntervalRat.scale (251 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-33636680044 / 1000000000000) (-33636674226 / 1000000000000), orderedInterval (56038847231 / 1000000000000) (56038853050 / 1000000000000)))) (orderedInterval (13785498588 / 1000000000000) (13785499142 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 0) <| besselDerivativeNearFromState (107898234546157 / 4000000000000) 0 (IntervalRat.scale (251 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (76194530497 / 1000000000000) (76194538901 / 1000000000000), orderedInterval (-134817994594 / 1000000000000) (-134817986190 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 0) <| besselDerivativeNearFromState (289829835133129 / 4000000000000) 0 (IntervalRat.scale (251 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-78079369423 / 1000000000000) (-78079369422 / 1000000000000), orderedInterval (-51323055547 / 1000000000000) (-51323055546 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 0) <| besselDerivativeNearFromState (786944382318693 / 4000000000000) 0 (IntervalRat.scale (251 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (22124728815 / 1000000000000) (22124729732 / 1000000000000), orderedInterval (-52462440671 / 1000000000000) (-52462439755 / 1000000000000)))) (orderedInterval (-5250309931 / 1000000000000) (-5250309759 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 0) <| besselDerivativeNearFromState (579659670266509 / 4000000000000) 0 (IntervalRat.scale (251 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (61437983035 / 1000000000000) (61437983036 / 1000000000000), orderedInterval (24655961880 / 1000000000000) (24655961881 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 0) <| besselDerivativeNearFromState (993256724984257 / 4000000000000) 0 (IntervalRat.scale (251 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-40076405307 / 1000000000000) (-40076405306 / 1000000000000), orderedInterval (-30865186772 / 1000000000000) (-30865186771 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 0) <| besselDerivativeNearFromState (731628408093763 / 4000000000000) 0 (IntervalRat.scale (251 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (58750186236 / 1000000000000) (58750186252 / 1000000000000), orderedInterval (5221432131 / 1000000000000) (5221432146 / 1000000000000)))) (orderedInterval (2655992769 / 1000000000000) (2655992777 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate250_chunkChecks0_1 :
    compactCertificate250.chunkChecks (0 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 0) <| besselDerivativeNearFromState (1122506124704749 / 4000000000000) 0 (IntervalRat.scale (251 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-46276230890 / 1000000000000) (-46276228510 / 1000000000000), orderedInterval (11355126795 / 1000000000000) (11355129175 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 0) <| besselDerivativeNearFromState (648079213265221 / 4000000000000) 0 (IntervalRat.scale (251 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-33211091467 / 1000000000000) (-33211084973 / 1000000000000), orderedInterval (53265473334 / 1000000000000) (53265479828 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 0) <| besselDerivativeNearFromState (1150027936642889 / 4000000000000) 0 (IntervalRat.scale (251 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-31540413374 / 1000000000000) (-31540393579 / 1000000000000), orderedInterval (34975882395 / 1000000000000) (34975902190 / 1000000000000)))) (orderedInterval (1278402861 / 1000000000000) (1278406629 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 0) <| besselDerivativeNearFromState (1074505276112141 / 4000000000000) 0 (IntervalRat.scale (251 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-33739014590 / 1000000000000) (-33738985661 / 1000000000000), orderedInterval (35156777883 / 1000000000000) (35156806812 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 0) <| besselDerivativeNearFromState (766817666289053 / 4000000000000) 0 (IntervalRat.scale (251 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-43370151555 / 1000000000000) (-43370151554 / 1000000000000), orderedInterval (-37832487469 / 1000000000000) (-37832487468 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 0) <| besselDerivativeNearFromState (869489505399387 / 4000000000000) 0 (IntervalRat.scale (251 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-53208973089 / 1000000000000) (-53208973084 / 1000000000000), orderedInterval (-9752015828 / 1000000000000) (-9752015823 / 1000000000000)))) (orderedInterval (-3222844976 / 1000000000000) (-3222844438 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 0) <| besselDerivativeNearFromState (724889700764203 / 4000000000000) 0 (IntervalRat.scale (251 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-12079323578 / 1000000000000) (-12079323498 / 1000000000000), orderedInterval (58059369457 / 1000000000000) (58059369537 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 0) <| besselDerivativeNearFromState (640462034324263 / 4000000000000) 0 (IntervalRat.scale (251 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-39594876509 / 1000000000000) (-39594876508 / 1000000000000), orderedInterval (-48950311271 / 1000000000000) (-48950311270 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 0) <| besselDerivativeNearFromState (185630860754037 / 800000000000) 0 (IntervalRat.scale (251 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (17743035550 / 1000000000000) (17743035551 / 1000000000000), orderedInterval (49244463458 / 1000000000000) (49244463459 / 1000000000000)))) (orderedInterval (2580686955 / 1000000000000) (2580686969 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate250_chunkChecks0_2 :
    compactCertificate250.chunkChecks (0 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 0) <| besselDerivativeNearFromState (513464730062639 / 4000000000000) 0 (IntervalRat.scale (251 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-23837166705 / 1000000000000) (-23837166704 / 1000000000000), orderedInterval (-66173453623 / 1000000000000) (-66173453622 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 0) <| besselDerivativeNearFromState (435269738140279 / 4000000000000) 0 (IntervalRat.scale (251 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (26518689116 / 1000000000000) (26518690018 / 1000000000000), orderedInterval (-71865510423 / 1000000000000) (-71865509521 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 0) <| besselDerivativeNearFromState (272371591906237 / 4000000000000) 0 (IntervalRat.scale (251 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-22849960588 / 1000000000000) (-22849960316 / 1000000000000), orderedInterval (94121946285 / 1000000000000) (94121946557 / 1000000000000)))) (orderedInterval (1566539431 / 1000000000000) (1566539523 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 0) <| besselDerivativeNearFromState (146482347994179 / 4000000000000) 0 (IntervalRat.scale (251 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-38526087786 / 1000000000000) (-38526087105 / 1000000000000), orderedInterval (126626224556 / 1000000000000) (126626225237 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 0) <| besselDerivativeNearFromState (397728069679537 / 4000000000000) 0 (IntervalRat.scale (251 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-24775395169 / 1000000000000) (-24775394577 / 1000000000000), orderedInterval (76208800208 / 1000000000000) (76208800800 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 0) <| besselDerivativeNearFromState (543063676328849 / 4000000000000) 0 (IntervalRat.scale (251 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-68071241655 / 1000000000000) (-68071241647 / 1000000000000), orderedInterval (-7190650622 / 1000000000000) (-7190650614 / 1000000000000)))) (orderedInterval (6490367695 / 1000000000000) (6490367738 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 0) <| besselDerivativeNearFromState (229628408093763 / 4000000000000) 0 (IntervalRat.scale (251 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (105040748428 / 1000000000000) (105040748497 / 1000000000000), orderedInterval (-8370654826 / 1000000000000) (-8370654757 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 0) <| besselDerivativeNearFromState (933426730313123 / 4000000000000) 0 (IntervalRat.scale (251 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (52005943135 / 1000000000000) (52005943443 / 1000000000000), orderedInterval (-4956341039 / 1000000000000) (-4956340730 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 0) <| besselDerivativeNearFromState (623485797061357 / 4000000000000) 0 (IntervalRat.scale (251 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-26268338711 / 1000000000000) (-26268337163 / 1000000000000), orderedInterval (58344452681 / 1000000000000) (58344454229 / 1000000000000)))) (orderedInterval (1328480728 / 1000000000000) (1328481080 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate250_chunkChecks0 :
    compactCertificate250.chunkChecks (0 : Fin 5) 0 9 = true :=
  compactCertificate250.chunkChecks_nine_of_three (0 : Fin 5) compactCertificate250_chunkChecks0_0
    compactCertificate250_chunkChecks0_1 compactCertificate250_chunkChecks0_2

theorem compactCertificate250_chunkChecks1_0 :
    compactCertificate250.chunkChecks (1 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 1) <| besselDerivativeNearFromState (251 / 2) 1 (IntervalRat.scale (251 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (41423043043 / 1000000000000) (41423043044 / 1000000000000), orderedInterval (57772972228 / 1000000000000) (57772972229 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 1) <| besselDerivativeNearFromState (369770927923151 / 4000000000000) 1 (IntervalRat.scale (251 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-70755805603 / 1000000000000) (-70755783908 / 1000000000000), orderedInterval (43744080611 / 1000000000000) (43744102306 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 1) <| besselDerivativeNearFromState (119576320667183 / 800000000000) 1 (IntervalRat.scale (251 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-33636680044 / 1000000000000) (-33636674226 / 1000000000000), orderedInterval (56038847231 / 1000000000000) (56038853050 / 1000000000000)))) (orderedInterval (27115937103 / 1000000000000) (27115937670 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 1) <| besselDerivativeNearFromState (107898234546157 / 4000000000000) 1 (IntervalRat.scale (251 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (76194530497 / 1000000000000) (76194538901 / 1000000000000), orderedInterval (-134817994594 / 1000000000000) (-134817986190 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 1) <| besselDerivativeNearFromState (289829835133129 / 4000000000000) 1 (IntervalRat.scale (251 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-78079369423 / 1000000000000) (-78079369422 / 1000000000000), orderedInterval (-51323055547 / 1000000000000) (-51323055546 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 1) <| besselDerivativeNearFromState (786944382318693 / 4000000000000) 1 (IntervalRat.scale (251 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (22124728815 / 1000000000000) (22124729732 / 1000000000000), orderedInterval (-52462440671 / 1000000000000) (-52462439755 / 1000000000000)))) (orderedInterval (5078978989 / 1000000000000) (5078979129 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 1) <| besselDerivativeNearFromState (579659670266509 / 4000000000000) 1 (IntervalRat.scale (251 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (61437983035 / 1000000000000) (61437983036 / 1000000000000), orderedInterval (24655961880 / 1000000000000) (24655961881 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 1) <| besselDerivativeNearFromState (993256724984257 / 4000000000000) 1 (IntervalRat.scale (251 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-40076405307 / 1000000000000) (-40076405306 / 1000000000000), orderedInterval (-30865186772 / 1000000000000) (-30865186771 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 1) <| besselDerivativeNearFromState (731628408093763 / 4000000000000) 1 (IntervalRat.scale (251 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (58750186236 / 1000000000000) (58750186252 / 1000000000000), orderedInterval (5221432131 / 1000000000000) (5221432146 / 1000000000000)))) (orderedInterval (2067553094 / 1000000000000) (2067553107 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate250_chunkChecks1_1 :
    compactCertificate250.chunkChecks (1 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 1) <| besselDerivativeNearFromState (1122506124704749 / 4000000000000) 1 (IntervalRat.scale (251 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-46276230890 / 1000000000000) (-46276228510 / 1000000000000), orderedInterval (11355126795 / 1000000000000) (11355129175 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 1) <| besselDerivativeNearFromState (648079213265221 / 4000000000000) 1 (IntervalRat.scale (251 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-33211091467 / 1000000000000) (-33211084973 / 1000000000000), orderedInterval (53265473334 / 1000000000000) (53265479828 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 1) <| besselDerivativeNearFromState (1150027936642889 / 4000000000000) 1 (IntervalRat.scale (251 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-31540413374 / 1000000000000) (-31540393579 / 1000000000000), orderedInterval (34975882395 / 1000000000000) (34975902190 / 1000000000000)))) (orderedInterval (11973686772 / 1000000000000) (11973694889 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 1) <| besselDerivativeNearFromState (1074505276112141 / 4000000000000) 1 (IntervalRat.scale (251 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-33739014590 / 1000000000000) (-33738985661 / 1000000000000), orderedInterval (35156777883 / 1000000000000) (35156806812 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 1) <| besselDerivativeNearFromState (766817666289053 / 4000000000000) 1 (IntervalRat.scale (251 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-43370151555 / 1000000000000) (-43370151554 / 1000000000000), orderedInterval (-37832487469 / 1000000000000) (-37832487468 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 1) <| besselDerivativeNearFromState (869489505399387 / 4000000000000) 1 (IntervalRat.scale (251 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-53208973089 / 1000000000000) (-53208973084 / 1000000000000), orderedInterval (-9752015828 / 1000000000000) (-9752015823 / 1000000000000)))) (orderedInterval (-6737836379 / 1000000000000) (-6737835236 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 1) <| besselDerivativeNearFromState (724889700764203 / 4000000000000) 1 (IntervalRat.scale (251 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-12079323578 / 1000000000000) (-12079323498 / 1000000000000), orderedInterval (58059369457 / 1000000000000) (58059369537 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 1) <| besselDerivativeNearFromState (640462034324263 / 4000000000000) 1 (IntervalRat.scale (251 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-39594876509 / 1000000000000) (-39594876508 / 1000000000000), orderedInterval (-48950311271 / 1000000000000) (-48950311270 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 1) <| besselDerivativeNearFromState (185630860754037 / 800000000000) 1 (IntervalRat.scale (251 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (17743035550 / 1000000000000) (17743035551 / 1000000000000), orderedInterval (49244463458 / 1000000000000) (49244463459 / 1000000000000)))) (orderedInterval (6873250130 / 1000000000000) (6873250149 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate250_chunkChecks1_2 :
    compactCertificate250.chunkChecks (1 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 1) <| besselDerivativeNearFromState (513464730062639 / 4000000000000) 1 (IntervalRat.scale (251 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-23837166705 / 1000000000000) (-23837166704 / 1000000000000), orderedInterval (-66173453623 / 1000000000000) (-66173453622 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 1) <| besselDerivativeNearFromState (435269738140279 / 4000000000000) 1 (IntervalRat.scale (251 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (26518689116 / 1000000000000) (26518690018 / 1000000000000), orderedInterval (-71865510423 / 1000000000000) (-71865509521 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 1) <| besselDerivativeNearFromState (272371591906237 / 4000000000000) 1 (IntervalRat.scale (251 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-22849960588 / 1000000000000) (-22849960316 / 1000000000000), orderedInterval (94121946285 / 1000000000000) (94121946557 / 1000000000000)))) (orderedInterval (16011695377 / 1000000000000) (16011695456 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 1) <| besselDerivativeNearFromState (146482347994179 / 4000000000000) 1 (IntervalRat.scale (251 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-38526087786 / 1000000000000) (-38526087105 / 1000000000000), orderedInterval (126626224556 / 1000000000000) (126626225237 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 1) <| besselDerivativeNearFromState (397728069679537 / 4000000000000) 1 (IntervalRat.scale (251 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-24775395169 / 1000000000000) (-24775394577 / 1000000000000), orderedInterval (76208800208 / 1000000000000) (76208800800 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 1) <| besselDerivativeNearFromState (543063676328849 / 4000000000000) 1 (IntervalRat.scale (251 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-68071241655 / 1000000000000) (-68071241647 / 1000000000000), orderedInterval (-7190650622 / 1000000000000) (-7190650614 / 1000000000000)))) (orderedInterval (-1455925098 / 1000000000000) (-1455925069 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 1) <| besselDerivativeNearFromState (229628408093763 / 4000000000000) 1 (IntervalRat.scale (251 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (105040748428 / 1000000000000) (105040748497 / 1000000000000), orderedInterval (-8370654826 / 1000000000000) (-8370654757 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 1) <| besselDerivativeNearFromState (933426730313123 / 4000000000000) 1 (IntervalRat.scale (251 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (52005943135 / 1000000000000) (52005943443 / 1000000000000), orderedInterval (-4956341039 / 1000000000000) (-4956340730 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 1) <| besselDerivativeNearFromState (623485797061357 / 4000000000000) 1 (IntervalRat.scale (251 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-26268338711 / 1000000000000) (-26268337163 / 1000000000000), orderedInterval (58344452681 / 1000000000000) (58344454229 / 1000000000000)))) (orderedInterval (-12869064379 / 1000000000000) (-12869063922 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate250_chunkChecks1 :
    compactCertificate250.chunkChecks (1 : Fin 5) 0 9 = true :=
  compactCertificate250.chunkChecks_nine_of_three (1 : Fin 5) compactCertificate250_chunkChecks1_0
    compactCertificate250_chunkChecks1_1 compactCertificate250_chunkChecks1_2

theorem compactCertificate250_chunkChecks2_0 :
    compactCertificate250.chunkChecks (2 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 2) <| besselDerivativeNearFromState (251 / 2) 2 (IntervalRat.scale (251 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (41423043043 / 1000000000000) (41423043044 / 1000000000000), orderedInterval (57772972228 / 1000000000000) (57772972229 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 2) <| besselDerivativeNearFromState (369770927923151 / 4000000000000) 2 (IntervalRat.scale (251 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-70755805603 / 1000000000000) (-70755783908 / 1000000000000), orderedInterval (43744080611 / 1000000000000) (43744102306 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 2) <| besselDerivativeNearFromState (119576320667183 / 800000000000) 2 (IntervalRat.scale (251 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-33636680044 / 1000000000000) (-33636674226 / 1000000000000), orderedInterval (56038847231 / 1000000000000) (56038853050 / 1000000000000)))) (orderedInterval (-13477136973 / 1000000000000) (-13477136362 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 2) <| besselDerivativeNearFromState (107898234546157 / 4000000000000) 2 (IntervalRat.scale (251 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (76194530497 / 1000000000000) (76194538901 / 1000000000000), orderedInterval (-134817994594 / 1000000000000) (-134817986190 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 2) <| besselDerivativeNearFromState (289829835133129 / 4000000000000) 2 (IntervalRat.scale (251 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-78079369423 / 1000000000000) (-78079369422 / 1000000000000), orderedInterval (-51323055547 / 1000000000000) (-51323055546 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 2) <| besselDerivativeNearFromState (786944382318693 / 4000000000000) 2 (IntervalRat.scale (251 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (22124728815 / 1000000000000) (22124729732 / 1000000000000), orderedInterval (-52462440671 / 1000000000000) (-52462439755 / 1000000000000)))) (orderedInterval (4813128381 / 1000000000000) (4813128571 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 2) <| besselDerivativeNearFromState (579659670266509 / 4000000000000) 2 (IntervalRat.scale (251 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (61437983035 / 1000000000000) (61437983036 / 1000000000000), orderedInterval (24655961880 / 1000000000000) (24655961881 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 2) <| besselDerivativeNearFromState (993256724984257 / 4000000000000) 2 (IntervalRat.scale (251 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-40076405307 / 1000000000000) (-40076405306 / 1000000000000), orderedInterval (-30865186772 / 1000000000000) (-30865186771 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 2) <| besselDerivativeNearFromState (731628408093763 / 4000000000000) 2 (IntervalRat.scale (251 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (58750186236 / 1000000000000) (58750186252 / 1000000000000), orderedInterval (5221432131 / 1000000000000) (5221432146 / 1000000000000)))) (orderedInterval (-7871641113 / 1000000000000) (-7871641089 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate250_chunkChecks2_1 :
    compactCertificate250.chunkChecks (2 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 2) <| besselDerivativeNearFromState (1122506124704749 / 4000000000000) 2 (IntervalRat.scale (251 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-46276230890 / 1000000000000) (-46276228510 / 1000000000000), orderedInterval (11355126795 / 1000000000000) (11355129175 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 2) <| besselDerivativeNearFromState (648079213265221 / 4000000000000) 2 (IntervalRat.scale (251 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-33211091467 / 1000000000000) (-33211084973 / 1000000000000), orderedInterval (53265473334 / 1000000000000) (53265479828 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 2) <| besselDerivativeNearFromState (1150027936642889 / 4000000000000) 2 (IntervalRat.scale (251 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-31540413374 / 1000000000000) (-31540393579 / 1000000000000), orderedInterval (34975882395 / 1000000000000) (34975902190 / 1000000000000)))) (orderedInterval (-13576881273 / 1000000000000) (-13576863303 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 2) <| besselDerivativeNearFromState (1074505276112141 / 4000000000000) 2 (IntervalRat.scale (251 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-33739014590 / 1000000000000) (-33738985661 / 1000000000000), orderedInterval (35156777883 / 1000000000000) (35156806812 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 2) <| besselDerivativeNearFromState (766817666289053 / 4000000000000) 2 (IntervalRat.scale (251 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-43370151555 / 1000000000000) (-43370151554 / 1000000000000), orderedInterval (-37832487469 / 1000000000000) (-37832487468 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 2) <| besselDerivativeNearFromState (869489505399387 / 4000000000000) 2 (IntervalRat.scale (251 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-53208973089 / 1000000000000) (-53208973084 / 1000000000000), orderedInterval (-9752015828 / 1000000000000) (-9752015823 / 1000000000000)))) (orderedInterval (6024790203 / 1000000000000) (6024792646 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 2) <| besselDerivativeNearFromState (724889700764203 / 4000000000000) 2 (IntervalRat.scale (251 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-12079323578 / 1000000000000) (-12079323498 / 1000000000000), orderedInterval (58059369457 / 1000000000000) (58059369537 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 2) <| besselDerivativeNearFromState (640462034324263 / 4000000000000) 2 (IntervalRat.scale (251 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-39594876509 / 1000000000000) (-39594876508 / 1000000000000), orderedInterval (-48950311271 / 1000000000000) (-48950311270 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 2) <| besselDerivativeNearFromState (185630860754037 / 800000000000) 2 (IntervalRat.scale (251 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (17743035550 / 1000000000000) (17743035551 / 1000000000000), orderedInterval (49244463458 / 1000000000000) (49244463459 / 1000000000000)))) (orderedInterval (-5005121478 / 1000000000000) (-5005121449 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate250_chunkChecks2_2 :
    compactCertificate250.chunkChecks (2 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 2) <| besselDerivativeNearFromState (513464730062639 / 4000000000000) 2 (IntervalRat.scale (251 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-23837166705 / 1000000000000) (-23837166704 / 1000000000000), orderedInterval (-66173453623 / 1000000000000) (-66173453622 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 2) <| besselDerivativeNearFromState (435269738140279 / 4000000000000) 2 (IntervalRat.scale (251 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (26518689116 / 1000000000000) (26518690018 / 1000000000000), orderedInterval (-71865510423 / 1000000000000) (-71865509521 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 2) <| besselDerivativeNearFromState (272371591906237 / 4000000000000) 2 (IntervalRat.scale (251 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-22849960588 / 1000000000000) (-22849960316 / 1000000000000), orderedInterval (94121946285 / 1000000000000) (94121946557 / 1000000000000)))) (orderedInterval (-2767616304 / 1000000000000) (-2767616233 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 2) <| besselDerivativeNearFromState (146482347994179 / 4000000000000) 2 (IntervalRat.scale (251 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-38526087786 / 1000000000000) (-38526087105 / 1000000000000), orderedInterval (126626224556 / 1000000000000) (126626225237 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 2) <| besselDerivativeNearFromState (397728069679537 / 4000000000000) 2 (IntervalRat.scale (251 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-24775395169 / 1000000000000) (-24775394577 / 1000000000000), orderedInterval (76208800208 / 1000000000000) (76208800800 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 2) <| besselDerivativeNearFromState (543063676328849 / 4000000000000) 2 (IntervalRat.scale (251 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-68071241655 / 1000000000000) (-68071241647 / 1000000000000), orderedInterval (-7190650622 / 1000000000000) (-7190650614 / 1000000000000)))) (orderedInterval (-6507093990 / 1000000000000) (-6507093965 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 2) <| besselDerivativeNearFromState (229628408093763 / 4000000000000) 2 (IntervalRat.scale (251 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (105040748428 / 1000000000000) (105040748497 / 1000000000000), orderedInterval (-8370654826 / 1000000000000) (-8370654757 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 2) <| besselDerivativeNearFromState (933426730313123 / 4000000000000) 2 (IntervalRat.scale (251 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (52005943135 / 1000000000000) (52005943443 / 1000000000000), orderedInterval (-4956341039 / 1000000000000) (-4956340730 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 2) <| besselDerivativeNearFromState (623485797061357 / 4000000000000) 2 (IntervalRat.scale (251 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-26268338711 / 1000000000000) (-26268337163 / 1000000000000), orderedInterval (58344452681 / 1000000000000) (58344454229 / 1000000000000)))) (orderedInterval (7003855114 / 1000000000000) (7003855725 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate250_chunkChecks2 :
    compactCertificate250.chunkChecks (2 : Fin 5) 0 9 = true :=
  compactCertificate250.chunkChecks_nine_of_three (2 : Fin 5) compactCertificate250_chunkChecks2_0
    compactCertificate250_chunkChecks2_1 compactCertificate250_chunkChecks2_2

theorem compactCertificate250_chunkChecks3_0 :
    compactCertificate250.chunkChecks (3 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 3) <| besselDerivativeNearFromState (251 / 2) 3 (IntervalRat.scale (251 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (41423043043 / 1000000000000) (41423043044 / 1000000000000), orderedInterval (57772972228 / 1000000000000) (57772972229 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 3) <| besselDerivativeNearFromState (369770927923151 / 4000000000000) 3 (IntervalRat.scale (251 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-70755805603 / 1000000000000) (-70755783908 / 1000000000000), orderedInterval (43744080611 / 1000000000000) (43744102306 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 3) <| besselDerivativeNearFromState (119576320667183 / 800000000000) 3 (IntervalRat.scale (251 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-33636680044 / 1000000000000) (-33636674226 / 1000000000000), orderedInterval (56038847231 / 1000000000000) (56038853050 / 1000000000000)))) (orderedInterval (-28508466557 / 1000000000000) (-28508465881 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 3) <| besselDerivativeNearFromState (107898234546157 / 4000000000000) 3 (IntervalRat.scale (251 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (76194530497 / 1000000000000) (76194538901 / 1000000000000), orderedInterval (-134817994594 / 1000000000000) (-134817986190 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 3) <| besselDerivativeNearFromState (289829835133129 / 4000000000000) 3 (IntervalRat.scale (251 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-78079369423 / 1000000000000) (-78079369422 / 1000000000000), orderedInterval (-51323055547 / 1000000000000) (-51323055546 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 3) <| besselDerivativeNearFromState (786944382318693 / 4000000000000) 3 (IntervalRat.scale (251 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (22124728815 / 1000000000000) (22124729732 / 1000000000000), orderedInterval (-52462440671 / 1000000000000) (-52462439755 / 1000000000000)))) (orderedInterval (-14059242332 / 1000000000000) (-14059242043 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 3) <| besselDerivativeNearFromState (579659670266509 / 4000000000000) 3 (IntervalRat.scale (251 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (61437983035 / 1000000000000) (61437983036 / 1000000000000), orderedInterval (24655961880 / 1000000000000) (24655961881 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 3) <| besselDerivativeNearFromState (993256724984257 / 4000000000000) 3 (IntervalRat.scale (251 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-40076405307 / 1000000000000) (-40076405306 / 1000000000000), orderedInterval (-30865186772 / 1000000000000) (-30865186771 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 3) <| besselDerivativeNearFromState (731628408093763 / 4000000000000) 3 (IntervalRat.scale (251 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (58750186236 / 1000000000000) (58750186252 / 1000000000000), orderedInterval (5221432131 / 1000000000000) (5221432146 / 1000000000000)))) (orderedInterval (-7701967375 / 1000000000000) (-7701967333 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate250_chunkChecks3_1 :
    compactCertificate250.chunkChecks (3 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 3) <| besselDerivativeNearFromState (1122506124704749 / 4000000000000) 3 (IntervalRat.scale (251 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-46276230890 / 1000000000000) (-46276228510 / 1000000000000), orderedInterval (11355126795 / 1000000000000) (11355129175 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 3) <| besselDerivativeNearFromState (648079213265221 / 4000000000000) 3 (IntervalRat.scale (251 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-33211091467 / 1000000000000) (-33211084973 / 1000000000000), orderedInterval (53265473334 / 1000000000000) (53265479828 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 3) <| besselDerivativeNearFromState (1150027936642889 / 4000000000000) 3 (IntervalRat.scale (251 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-31540413374 / 1000000000000) (-31540393579 / 1000000000000), orderedInterval (34975882395 / 1000000000000) (34975902190 / 1000000000000)))) (orderedInterval (-45603307013 / 1000000000000) (-45603266793 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 3) <| besselDerivativeNearFromState (1074505276112141 / 4000000000000) 3 (IntervalRat.scale (251 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-33739014590 / 1000000000000) (-33738985661 / 1000000000000), orderedInterval (35156777883 / 1000000000000) (35156806812 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 3) <| besselDerivativeNearFromState (766817666289053 / 4000000000000) 3 (IntervalRat.scale (251 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-43370151555 / 1000000000000) (-43370151554 / 1000000000000), orderedInterval (-37832487469 / 1000000000000) (-37832487468 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 3) <| besselDerivativeNearFromState (869489505399387 / 4000000000000) 3 (IntervalRat.scale (251 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-53208973089 / 1000000000000) (-53208973084 / 1000000000000), orderedInterval (-9752015828 / 1000000000000) (-9752015823 / 1000000000000)))) (orderedInterval (18670398952 / 1000000000000) (18670404162 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 3) <| besselDerivativeNearFromState (724889700764203 / 4000000000000) 3 (IntervalRat.scale (251 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-12079323578 / 1000000000000) (-12079323498 / 1000000000000), orderedInterval (58059369457 / 1000000000000) (58059369537 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 3) <| besselDerivativeNearFromState (640462034324263 / 4000000000000) 3 (IntervalRat.scale (251 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-39594876509 / 1000000000000) (-39594876508 / 1000000000000), orderedInterval (-48950311271 / 1000000000000) (-48950311270 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 3) <| besselDerivativeNearFromState (185630860754037 / 800000000000) 3 (IntervalRat.scale (251 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (17743035550 / 1000000000000) (17743035551 / 1000000000000), orderedInterval (49244463458 / 1000000000000) (49244463459 / 1000000000000)))) (orderedInterval (-15764883300 / 1000000000000) (-15764883256 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate250_chunkChecks3_2 :
    compactCertificate250.chunkChecks (3 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 3) <| besselDerivativeNearFromState (513464730062639 / 4000000000000) 3 (IntervalRat.scale (251 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-23837166705 / 1000000000000) (-23837166704 / 1000000000000), orderedInterval (-66173453623 / 1000000000000) (-66173453622 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 3) <| besselDerivativeNearFromState (435269738140279 / 4000000000000) 3 (IntervalRat.scale (251 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (26518689116 / 1000000000000) (26518690018 / 1000000000000), orderedInterval (-71865510423 / 1000000000000) (-71865509521 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 3) <| besselDerivativeNearFromState (272371591906237 / 4000000000000) 3 (IntervalRat.scale (251 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-22849960588 / 1000000000000) (-22849960316 / 1000000000000), orderedInterval (94121946285 / 1000000000000) (94121946557 / 1000000000000)))) (orderedInterval (-14440154639 / 1000000000000) (-14440154576 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 3) <| besselDerivativeNearFromState (146482347994179 / 4000000000000) 3 (IntervalRat.scale (251 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-38526087786 / 1000000000000) (-38526087105 / 1000000000000), orderedInterval (126626224556 / 1000000000000) (126626225237 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 3) <| besselDerivativeNearFromState (397728069679537 / 4000000000000) 3 (IntervalRat.scale (251 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-24775395169 / 1000000000000) (-24775394577 / 1000000000000), orderedInterval (76208800208 / 1000000000000) (76208800800 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 3) <| besselDerivativeNearFromState (543063676328849 / 4000000000000) 3 (IntervalRat.scale (251 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-68071241655 / 1000000000000) (-68071241647 / 1000000000000), orderedInterval (-7190650622 / 1000000000000) (-7190650614 / 1000000000000)))) (orderedInterval (272024831 / 1000000000000) (272024853 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 3) <| besselDerivativeNearFromState (229628408093763 / 4000000000000) 3 (IntervalRat.scale (251 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (105040748428 / 1000000000000) (105040748497 / 1000000000000), orderedInterval (-8370654826 / 1000000000000) (-8370654757 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 3) <| besselDerivativeNearFromState (933426730313123 / 4000000000000) 3 (IntervalRat.scale (251 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (52005943135 / 1000000000000) (52005943443 / 1000000000000), orderedInterval (-4956341039 / 1000000000000) (-4956340730 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 3) <| besselDerivativeNearFromState (623485797061357 / 4000000000000) 3 (IntervalRat.scale (251 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-26268338711 / 1000000000000) (-26268337163 / 1000000000000), orderedInterval (58344452681 / 1000000000000) (58344454229 / 1000000000000)))) (orderedInterval (18327562594 / 1000000000000) (18327563428 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate250_chunkChecks3 :
    compactCertificate250.chunkChecks (3 : Fin 5) 0 9 = true :=
  compactCertificate250.chunkChecks_nine_of_three (3 : Fin 5) compactCertificate250_chunkChecks3_0
    compactCertificate250_chunkChecks3_1 compactCertificate250_chunkChecks3_2

theorem compactCertificate250_chunkChecks4_0 :
    compactCertificate250.chunkChecks (4 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 4) <| besselDerivativeNearFromState (251 / 2) 4 (IntervalRat.scale (251 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (41423043043 / 1000000000000) (41423043044 / 1000000000000), orderedInterval (57772972228 / 1000000000000) (57772972229 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 4) <| besselDerivativeNearFromState (369770927923151 / 4000000000000) 4 (IntervalRat.scale (251 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-70755805603 / 1000000000000) (-70755783908 / 1000000000000), orderedInterval (43744080611 / 1000000000000) (43744102306 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 4) <| besselDerivativeNearFromState (119576320667183 / 800000000000) 4 (IntervalRat.scale (251 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-33636680044 / 1000000000000) (-33636674226 / 1000000000000), orderedInterval (56038847231 / 1000000000000) (56038853050 / 1000000000000)))) (orderedInterval (12706475302 / 1000000000000) (12706476076 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 4) <| besselDerivativeNearFromState (107898234546157 / 4000000000000) 4 (IntervalRat.scale (251 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (76194530497 / 1000000000000) (76194538901 / 1000000000000), orderedInterval (-134817994594 / 1000000000000) (-134817986190 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 4) <| besselDerivativeNearFromState (289829835133129 / 4000000000000) 4 (IntervalRat.scale (251 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-78079369423 / 1000000000000) (-78079369422 / 1000000000000), orderedInterval (-51323055547 / 1000000000000) (-51323055546 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 4) <| besselDerivativeNearFromState (786944382318693 / 4000000000000) 4 (IntervalRat.scale (251 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (22124728815 / 1000000000000) (22124729732 / 1000000000000), orderedInterval (-52462440671 / 1000000000000) (-52462439755 / 1000000000000)))) (orderedInterval (-9592460228 / 1000000000000) (-9592459775 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 4) <| besselDerivativeNearFromState (579659670266509 / 4000000000000) 4 (IntervalRat.scale (251 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (61437983035 / 1000000000000) (61437983036 / 1000000000000), orderedInterval (24655961880 / 1000000000000) (24655961881 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 4) <| besselDerivativeNearFromState (993256724984257 / 4000000000000) 4 (IntervalRat.scale (251 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-40076405307 / 1000000000000) (-40076405306 / 1000000000000), orderedInterval (-30865186772 / 1000000000000) (-30865186771 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 4) <| besselDerivativeNearFromState (731628408093763 / 4000000000000) 4 (IntervalRat.scale (251 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (58750186236 / 1000000000000) (58750186252 / 1000000000000), orderedInterval (5221432131 / 1000000000000) (5221432146 / 1000000000000)))) (orderedInterval (25473227753 / 1000000000000) (25473227829 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate250_chunkChecks4_1 :
    compactCertificate250.chunkChecks (4 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 4) <| besselDerivativeNearFromState (1122506124704749 / 4000000000000) 4 (IntervalRat.scale (251 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-46276230890 / 1000000000000) (-46276228510 / 1000000000000), orderedInterval (11355126795 / 1000000000000) (11355129175 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 4) <| besselDerivativeNearFromState (648079213265221 / 4000000000000) 4 (IntervalRat.scale (251 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-33211091467 / 1000000000000) (-33211084973 / 1000000000000), orderedInterval (53265473334 / 1000000000000) (53265479828 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 4) <| besselDerivativeNearFromState (1150027936642889 / 4000000000000) 4 (IntervalRat.scale (251 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-31540413374 / 1000000000000) (-31540393579 / 1000000000000), orderedInterval (34975882395 / 1000000000000) (34975902190 / 1000000000000)))) (orderedInterval (75963417998 / 1000000000000) (75963509118 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 4) <| besselDerivativeNearFromState (1074505276112141 / 4000000000000) 4 (IntervalRat.scale (251 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-33739014590 / 1000000000000) (-33738985661 / 1000000000000), orderedInterval (35156777883 / 1000000000000) (35156806812 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 4) <| besselDerivativeNearFromState (766817666289053 / 4000000000000) 4 (IntervalRat.scale (251 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-43370151555 / 1000000000000) (-43370151554 / 1000000000000), orderedInterval (-37832487469 / 1000000000000) (-37832487468 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 4) <| besselDerivativeNearFromState (869489505399387 / 4000000000000) 4 (IntervalRat.scale (251 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-53208973089 / 1000000000000) (-53208973084 / 1000000000000), orderedInterval (-9752015828 / 1000000000000) (-9752015823 / 1000000000000)))) (orderedInterval (-7417464012 / 1000000000000) (-7417452849 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 4) <| besselDerivativeNearFromState (724889700764203 / 4000000000000) 4 (IntervalRat.scale (251 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-12079323578 / 1000000000000) (-12079323498 / 1000000000000), orderedInterval (58059369457 / 1000000000000) (58059369537 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 4) <| besselDerivativeNearFromState (640462034324263 / 4000000000000) 4 (IntervalRat.scale (251 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-39594876509 / 1000000000000) (-39594876508 / 1000000000000), orderedInterval (-48950311271 / 1000000000000) (-48950311270 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 4) <| besselDerivativeNearFromState (185630860754037 / 800000000000) 4 (IntervalRat.scale (251 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (17743035550 / 1000000000000) (17743035551 / 1000000000000), orderedInterval (49244463458 / 1000000000000) (49244463459 / 1000000000000)))) (orderedInterval (10956680143 / 1000000000000) (10956680211 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate250_chunkChecks4_2 :
    compactCertificate250.chunkChecks (4 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 4) <| besselDerivativeNearFromState (513464730062639 / 4000000000000) 4 (IntervalRat.scale (251 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-23837166705 / 1000000000000) (-23837166704 / 1000000000000), orderedInterval (-66173453623 / 1000000000000) (-66173453622 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 4) <| besselDerivativeNearFromState (435269738140279 / 4000000000000) 4 (IntervalRat.scale (251 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (26518689116 / 1000000000000) (26518690018 / 1000000000000), orderedInterval (-71865510423 / 1000000000000) (-71865509521 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 4) <| besselDerivativeNearFromState (272371591906237 / 4000000000000) 4 (IntervalRat.scale (251 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-22849960588 / 1000000000000) (-22849960316 / 1000000000000), orderedInterval (94121946285 / 1000000000000) (94121946557 / 1000000000000)))) (orderedInterval (3488769364 / 1000000000000) (3488769422 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 4) <| besselDerivativeNearFromState (146482347994179 / 4000000000000) 4 (IntervalRat.scale (251 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-38526087786 / 1000000000000) (-38526087105 / 1000000000000), orderedInterval (126626224556 / 1000000000000) (126626225237 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 4) <| besselDerivativeNearFromState (397728069679537 / 4000000000000) 4 (IntervalRat.scale (251 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-24775395169 / 1000000000000) (-24775394577 / 1000000000000), orderedInterval (76208800208 / 1000000000000) (76208800800 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 4) <| besselDerivativeNearFromState (543063676328849 / 4000000000000) 4 (IntervalRat.scale (251 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-68071241655 / 1000000000000) (-68071241647 / 1000000000000), orderedInterval (-7190650622 / 1000000000000) (-7190650614 / 1000000000000)))) (orderedInterval (7366863520 / 1000000000000) (7366863542 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 4) <| besselDerivativeNearFromState (229628408093763 / 4000000000000) 4 (IntervalRat.scale (251 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (105040748428 / 1000000000000) (105040748497 / 1000000000000), orderedInterval (-8370654826 / 1000000000000) (-8370654757 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 4) <| besselDerivativeNearFromState (933426730313123 / 4000000000000) 4 (IntervalRat.scale (251 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (52005943135 / 1000000000000) (52005943443 / 1000000000000), orderedInterval (-4956341039 / 1000000000000) (-4956340730 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 4) <| besselDerivativeNearFromState (623485797061357 / 4000000000000) 4 (IntervalRat.scale (251 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-26268338711 / 1000000000000) (-26268337163 / 1000000000000), orderedInterval (58344452681 / 1000000000000) (58344454229 / 1000000000000)))) (orderedInterval (-39140995520 / 1000000000000) (-39140994338 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate250_chunkChecks4 :
    compactCertificate250.chunkChecks (4 : Fin 5) 0 9 = true :=
  compactCertificate250.chunkChecks_nine_of_three (4 : Fin 5) compactCertificate250_chunkChecks4_0
    compactCertificate250_chunkChecks4_1 compactCertificate250_chunkChecks4_2

theorem compactCertificate250_chunks :
    ∀ r : Fin 5, ∀ b, compactCertificate250.chunkCheck r b = true :=
  compactCertificate250.chunkChecks_all (by
    intro r
    fin_cases r
    · exact compactCertificate250_chunkChecks0
    · exact compactCertificate250_chunkChecks1
    · exact compactCertificate250_chunkChecks2
    · exact compactCertificate250_chunkChecks3
    · exact compactCertificate250_chunkChecks4)

theorem compactCertificate250_coefficient0 :
    compactCertificate250.coefficientCheck (0 : Fin 5) = true := by
  norm_num [CompactCertificate.coefficientCheck, intervalFinSumHull,
    compactCertificate250, rationalIntervalSubset, orderedInterval, Fin.sum_univ_succ]

theorem compactCertificate250_coefficient1 :
    compactCertificate250.coefficientCheck (1 : Fin 5) = true := by
  norm_num [CompactCertificate.coefficientCheck, intervalFinSumHull,
    compactCertificate250, rationalIntervalSubset, orderedInterval, Fin.sum_univ_succ]

theorem compactCertificate250_coefficient2 :
    compactCertificate250.coefficientCheck (2 : Fin 5) = true := by
  norm_num [CompactCertificate.coefficientCheck, intervalFinSumHull,
    compactCertificate250, rationalIntervalSubset, orderedInterval, Fin.sum_univ_succ]

theorem compactCertificate250_coefficient3 :
    compactCertificate250.coefficientCheck (3 : Fin 5) = true := by
  norm_num [CompactCertificate.coefficientCheck, intervalFinSumHull,
    compactCertificate250, rationalIntervalSubset, orderedInterval, Fin.sum_univ_succ]

theorem compactCertificate250_coefficient4 :
    compactCertificate250.coefficientCheck (4 : Fin 5) = true := by
  norm_num [CompactCertificate.coefficientCheck, intervalFinSumHull,
    compactCertificate250, rationalIntervalSubset, orderedInterval, Fin.sum_univ_succ]

theorem compactCertificate250_coefficients : ∀ r : Fin 5,
    compactCertificate250.coefficientCheck r = true := by
  intro r
  fin_cases r
  · exact compactCertificate250_coefficient0
  · exact compactCertificate250_coefficient1
  · exact compactCertificate250_coefficient2
  · exact compactCertificate250_coefficient3
  · exact compactCertificate250_coefficient4

theorem compactCertificate250_lower : (1 : ℚ) ≤ compactCertificate250.output.lo := by
  norm_num [CompactCertificate.output, CompactCertificate.interval,
    CompactCertificate.coefficientTargetNat, compactCertificate250, dualConstant,
    intervalTaylorSum, intervalPow, intervalSub, intervalMaxAbs, widenInterval,
    rationalErrorInterval, orderedInterval, IntervalRat.add, IntervalRat.mul, IntervalRat.scale,
    IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4]

theorem compactCertificate250_proves {t : ℝ} (ht : t ∈ compactCertificate250.interval) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t :=
  compactCertificate250.proves compactCertificate250_states compactCertificate250_chunks
    compactCertificate250_coefficients compactCertificate250_lower ht

end Erdos232
