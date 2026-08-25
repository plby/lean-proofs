/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, OpenAI Codex
-/
import ErdosProblems.Erdos232.CompactBase

open LeanCert.Core
namespace Erdos232

def compactCertificate267 : CompactCertificate where
  left := 141
  right := 142
  center := 283 / 2
  grid := fun i =>
    match i.val with
    | 0 => 45
    | 1 => 33
    | 2 => 54
    | 3 => 10
    | 4 => 26
    | 5 => 71
    | 6 => 52
    | 7 => 89
    | 8 => 66
    | 9 => 101
    | 10 => 58
    | 11 => 103
    | 12 => 96
    | 13 => 69
    | 14 => 78
    | 15 => 65
    | 16 => 57
    | 17 => 83
    | 18 => 46
    | 19 => 39
    | 20 => 24
    | 21 => 13
    | 22 => 36
    | 23 => 49
    | 24 => 21
    | 25 => 84
    | _ => 56
  point := fun i =>
    match i.val with
    | 0 => 283 / 2
    | 1 => 416913038255983 / 4000000000000
    | 2 => 134821110553039 / 800000000000
    | 3 => 121654184767181 / 4000000000000
    | 4 => 326780252361257 / 4000000000000
    | 5 => 887271952972869 / 4000000000000
    | 6 => 653560504722797 / 4000000000000
    | 7 => 1119887064424481 / 4000000000000
    | 8 => 824903742990179 / 4000000000000
    | 9 => 1265614475264717 / 4000000000000
    | 10 => 730702857984293 / 4000000000000
    | 11 => 1296645044103337 / 4000000000000
    | 12 => 1211493996572653 / 4000000000000
    | 13 => 864579281114749 / 4000000000000
    | 14 => 980340757083771 / 4000000000000
    | 15 => 817305917594699 / 4000000000000
    | 16 => 722114564596679 / 4000000000000
    | 17 => 209296946587221 / 800000000000
    | 18 => 578926368955087 / 4000000000000
    | 19 => 490762294397207 / 4000000000000
    | 20 => 307096257009821 / 4000000000000
    | 21 => 165157388375907 / 4000000000000
    | 22 => 448434437128721 / 4000000000000
    | 23 => 612298886060017 / 4000000000000
    | 24 => 258903742990179 / 4000000000000
    | 25 => 1052429341349059 / 4000000000000
    | _ => 702974026168781 / 4000000000000
  state := fun i =>
    match i.val with
    | 0 => (orderedInterval (-53072860794 / 1000000000000) (-53072860793 / 1000000000000), orderedInterval (-40828853054 / 1000000000000) (-40828853053 / 1000000000000))
    | 1 => (orderedInterval (-76078819822 / 1000000000000) (-76078819820 / 1000000000000), orderedInterval (-17520473070 / 1000000000000) (-17520473068 / 1000000000000))
    | 2 => (orderedInterval (-20204339112 / 1000000000000) (-20204338618 / 1000000000000), orderedInterval (58106175081 / 1000000000000) (58106175575 / 1000000000000))
    | 3 => (orderedInterval (-31725043373 / 1000000000000) (-31725043103 / 1000000000000), orderedInterval (141688649539 / 1000000000000) (141688649809 / 1000000000000))
    | 4 => (orderedInterval (63172084504 / 1000000000000) (63172084505 / 1000000000000), orderedInterval (61273082370 / 1000000000000) (61273082371 / 1000000000000))
    | 5 => (orderedInterval (23314473392 / 1000000000000) (23314474828 / 1000000000000), orderedInterval (-48285835669 / 1000000000000) (-48285834233 / 1000000000000))
    | 6 => (orderedInterval (45293720030 / 1000000000000) (45293720031 / 1000000000000), orderedInterval (42812474861 / 1000000000000) (42812474862 / 1000000000000))
    | 7 => (orderedInterval (-43621532518 / 1000000000000) (-43621532517 / 1000000000000), orderedInterval (-19184256306 / 1000000000000) (-19184256305 / 1000000000000))
    | 8 => (orderedInterval (-18234498009 / 1000000000000) (-18234497623 / 1000000000000), orderedInterval (52527651736 / 1000000000000) (52527652122 / 1000000000000))
    | 9 => (orderedInterval (5023882119 / 1000000000000) (5023882126 / 1000000000000), orderedInterval (-44581615676 / 1000000000000) (-44581615669 / 1000000000000))
    | 10 => (orderedInterval (55985602387 / 1000000000000) (55985602388 / 1000000000000), orderedInterval (18570385454 / 1000000000000) (18570385455 / 1000000000000))
    | 11 => (orderedInterval (-43355489809 / 1000000000000) (-43355489801 / 1000000000000), orderedInterval (-9109059402 / 1000000000000) (-9109059394 / 1000000000000))
    | 12 => (orderedInterval (40348236719 / 1000000000000) (40348271387 / 1000000000000), orderedInterval (-21837010987 / 1000000000000) (-21836976319 / 1000000000000))
    | 13 => (orderedInterval (-8632789695 / 1000000000000) (-8632789694 / 1000000000000), orderedInterval (-53560077220 / 1000000000000) (-53560077218 / 1000000000000))
    | 14 => (orderedInterval (37466404890 / 1000000000000) (37466404891 / 1000000000000), orderedInterval (34475162817 / 1000000000000) (34475162818 / 1000000000000))
    | 15 => (orderedInterval (-43991383168 / 1000000000000) (-43991383167 / 1000000000000), orderedInterval (-34250097854 / 1000000000000) (-34250097853 / 1000000000000))
    | 16 => (orderedInterval (-46480840895 / 1000000000000) (-46480746246 / 1000000000000), orderedInterval (37087478044 / 1000000000000) (37087572692 / 1000000000000))
    | 17 => (orderedInterval (-49158806918 / 1000000000000) (-49158806591 / 1000000000000), orderedInterval (4189326867 / 1000000000000) (4189327194 / 1000000000000))
    | 18 => (orderedInterval (55910395902 / 1000000000000) (55910395903 / 1000000000000), orderedInterval (35480930507 / 1000000000000) (35480930508 / 1000000000000))
    | 19 => (orderedInterval (-58711654667 / 1000000000000) (-58711654666 / 1000000000000), orderedInterval (-41495030603 / 1000000000000) (-41495030602 / 1000000000000))
    | 20 => (orderedInterval (75725550428 / 1000000000000) (75725579459 / 1000000000000), orderedInterval (-51066789489 / 1000000000000) (-51066760458 / 1000000000000))
    | 21 => (orderedInterval (-117067759711 / 1000000000000) (-117067759710 / 1000000000000), orderedInterval (-39968067610 / 1000000000000) (-39968067609 / 1000000000000))
    | 22 => (orderedInterval (-15298932718 / 1000000000000) (-15298932589 / 1000000000000), orderedInterval (73855715940 / 1000000000000) (73855716068 / 1000000000000))
    | 23 => (orderedInterval (5072438382 / 1000000000000) (5072438396 / 1000000000000), orderedInterval (-64306339883 / 1000000000000) (-64306339868 / 1000000000000))
    | 24 => (orderedInterval (44386661073 / 1000000000000) (44386665072 / 1000000000000), orderedInterval (-89031199050 / 1000000000000) (-89031195050 / 1000000000000))
    | 25 => (orderedInterval (-74988938 / 1000000000000) (-74988936 / 1000000000000), orderedInterval (49189762872 / 1000000000000) (49189762874 / 1000000000000))
    | _ => (orderedInterval (33934439579 / 1000000000000) (33934439580 / 1000000000000), orderedInterval (49611564448 / 1000000000000) (49611564449 / 1000000000000))
  chunkTarget := fun r b =>
    match r.val with
    | 0 =>
      match b.val with
      | 0 => orderedInterval (-22930744762 / 1000000000000) (-22930744722 / 1000000000000)
      | 1 => orderedInterval (993299674 / 1000000000000) (993299797 / 1000000000000)
      | 2 => orderedInterval (904770748 / 1000000000000) (904770766 / 1000000000000)
      | 3 => orderedInterval (-2907849119 / 1000000000000) (-2907849060 / 1000000000000)
      | 4 => orderedInterval (-1734353747 / 1000000000000) (-1734353103 / 1000000000000)
      | 5 => orderedInterval (893281035 / 1000000000000) (893286474 / 1000000000000)
      | 6 => orderedInterval (-3151306866 / 1000000000000) (-3151305884 / 1000000000000)
      | 7 => orderedInterval (2120008697 / 1000000000000) (2120008718 / 1000000000000)
      | _ => orderedInterval (-6093319480 / 1000000000000) (-6093319415 / 1000000000000)
    | 1 =>
      match b.val with
      | 0 => orderedInterval (-12242388705 / 1000000000000) (-12242388658 / 1000000000000)
      | 1 => orderedInterval (6342277315 / 1000000000000) (6342277495 / 1000000000000)
      | 2 => orderedInterval (3020963792 / 1000000000000) (3020963821 / 1000000000000)
      | 3 => orderedInterval (16523073647 / 1000000000000) (16523073770 / 1000000000000)
      | 4 => orderedInterval (-7194964080 / 1000000000000) (-7194962712 / 1000000000000)
      | 5 => orderedInterval (-3080595740 / 1000000000000) (-3080588793 / 1000000000000)
      | 6 => orderedInterval (-4668301923 / 1000000000000) (-4668301376 / 1000000000000)
      | 7 => orderedInterval (4219337202 / 1000000000000) (4219337222 / 1000000000000)
      | _ => orderedInterval (-19251978292 / 1000000000000) (-19251978224 / 1000000000000)
    | 2 =>
      match b.val with
      | 0 => orderedInterval (23189144629 / 1000000000000) (23189144685 / 1000000000000)
      | 1 => orderedInterval (3243418989 / 1000000000000) (3243419268 / 1000000000000)
      | 2 => orderedInterval (-4352568708 / 1000000000000) (-4352568663 / 1000000000000)
      | 3 => orderedInterval (29779021597 / 1000000000000) (29779021859 / 1000000000000)
      | 4 => orderedInterval (5861675471 / 1000000000000) (5861678394 / 1000000000000)
      | 5 => orderedInterval (1054081777 / 1000000000000) (1054090701 / 1000000000000)
      | 6 => orderedInterval (6161564229 / 1000000000000) (6161564543 / 1000000000000)
      | 7 => orderedInterval (23198784 / 1000000000000) (23198803 / 1000000000000)
      | _ => orderedInterval (9880526846 / 1000000000000) (9880526933 / 1000000000000)
    | 3 =>
      match b.val with
      | 0 => orderedInterval (10323447760 / 1000000000000) (10323447825 / 1000000000000)
      | 1 => orderedInterval (-13661406726 / 1000000000000) (-13661406290 / 1000000000000)
      | 2 => orderedInterval (-8482477085 / 1000000000000) (-8482477011 / 1000000000000)
      | 3 => orderedInterval (-76167764127 / 1000000000000) (-76167763552 / 1000000000000)
      | 4 => orderedInterval (15050851418 / 1000000000000) (15050857654 / 1000000000000)
      | 5 => orderedInterval (4912828031 / 1000000000000) (4912839440 / 1000000000000)
      | 6 => orderedInterval (4761528170 / 1000000000000) (4761528354 / 1000000000000)
      | 7 => orderedInterval (-5424397174 / 1000000000000) (-5424397155 / 1000000000000)
      | _ => orderedInterval (43556210905 / 1000000000000) (43556211035 / 1000000000000)
    | _ =>
      match b.val with
      | 0 => orderedInterval (-23775220989 / 1000000000000) (-23775220911 / 1000000000000)
      | 1 => orderedInterval (-9558790220 / 1000000000000) (-9558789535 / 1000000000000)
      | 2 => orderedInterval (18752045106 / 1000000000000) (18752045232 / 1000000000000)
      | 3 => orderedInterval (-179473585103 / 1000000000000) (-179473583827 / 1000000000000)
      | 4 => orderedInterval (-21652963055 / 1000000000000) (-21652949697 / 1000000000000)
      | 5 => orderedInterval (-9939349311 / 1000000000000) (-9939334633 / 1000000000000)
      | 6 => orderedInterval (-7759781840 / 1000000000000) (-7759781725 / 1000000000000)
      | 7 => orderedInterval (-303316252 / 1000000000000) (-303316232 / 1000000000000)
      | _ => orderedInterval (-15680928849 / 1000000000000) (-15680928644 / 1000000000000)
  coefficientTarget := fun i =>
    match i.val with
    | 0 => orderedInterval (-31906213820 / 1000000000000) (-31906206429 / 1000000000000)
    | 1 => orderedInterval (-16332576784 / 1000000000000) (-16332567455 / 1000000000000)
    | 2 => orderedInterval (74840063614 / 1000000000000) (74840076523 / 1000000000000)
    | 3 => orderedInterval (-25131178828 / 1000000000000) (-25131159700 / 1000000000000)
    | _ => orderedInterval (-249391890513 / 1000000000000) (-249391859972 / 1000000000000)

theorem compactCertificate267_stateChecks0 :
    compactCertificate267.stateChecks 0 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 45 12 (283 / 2)) (orderedInterval (-53072860794 / 1000000000000) (-53072860793 / 1000000000000), orderedInterval (-40828853054 / 1000000000000) (-40828853053 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 33 12 (416913038255983 / 4000000000000)) (orderedInterval (-76078819822 / 1000000000000) (-76078819820 / 1000000000000), orderedInterval (-17520473070 / 1000000000000) (-17520473068 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 54 12 (134821110553039 / 800000000000)) (orderedInterval (-20204339112 / 1000000000000) (-20204338618 / 1000000000000), orderedInterval (58106175081 / 1000000000000) (58106175575 / 1000000000000))) = true
  norm_num [besselStateAtRationalPoint, besselIntervalStepZero,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, besselZeroTransition,
    besselInitial, besselGridStateAt, besselGridStateBlock00, besselGridStateBlock01,
    besselGridStateBlock02, besselGridStateBlock03, besselGridStateBlock04,
    besselGridStateBlock05, besselGridStateBlock06, besselGridStateBlock07,
    besselGridStateBlock08, besselGridStateBlock09, besselGridStateBlock10,
    besselGridStateBlock11, besselGridStateBlock12, besselGridStateBlock13,
    besselGridStateBlock14, besselGridState010, besselGridState013, besselGridState021, besselGridState024, besselGridState026, besselGridState033, besselGridState036, besselGridState039, besselGridState045, besselGridState046, besselGridState049, besselGridState052, besselGridState054, besselGridState056, besselGridState057, besselGridState058, besselGridState065, besselGridState066, besselGridState069, besselGridState071, besselGridState078, besselGridState083, besselGridState084, besselGridState089, besselGridState096, besselGridState101, besselGridState103, besselStateSubset, linearInterval, widenInterval,
    rationalErrorInterval, rationalIntervalSubset, orderedInterval, Finset.sum_range_succ,
    IntervalRat.add, IntervalRat.mul, IntervalRat.scale, IntervalRat.singleton]

theorem compactCertificate267_stateChecks1 :
    compactCertificate267.stateChecks 3 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 10 12 (121654184767181 / 4000000000000)) (orderedInterval (-31725043373 / 1000000000000) (-31725043103 / 1000000000000), orderedInterval (141688649539 / 1000000000000) (141688649809 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 26 12 (326780252361257 / 4000000000000)) (orderedInterval (63172084504 / 1000000000000) (63172084505 / 1000000000000), orderedInterval (61273082370 / 1000000000000) (61273082371 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 71 12 (887271952972869 / 4000000000000)) (orderedInterval (23314473392 / 1000000000000) (23314474828 / 1000000000000), orderedInterval (-48285835669 / 1000000000000) (-48285834233 / 1000000000000))) = true
  norm_num [besselStateAtRationalPoint, besselIntervalStepZero,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, besselZeroTransition,
    besselInitial, besselGridStateAt, besselGridStateBlock00, besselGridStateBlock01,
    besselGridStateBlock02, besselGridStateBlock03, besselGridStateBlock04,
    besselGridStateBlock05, besselGridStateBlock06, besselGridStateBlock07,
    besselGridStateBlock08, besselGridStateBlock09, besselGridStateBlock10,
    besselGridStateBlock11, besselGridStateBlock12, besselGridStateBlock13,
    besselGridStateBlock14, besselGridState010, besselGridState013, besselGridState021, besselGridState024, besselGridState026, besselGridState033, besselGridState036, besselGridState039, besselGridState045, besselGridState046, besselGridState049, besselGridState052, besselGridState054, besselGridState056, besselGridState057, besselGridState058, besselGridState065, besselGridState066, besselGridState069, besselGridState071, besselGridState078, besselGridState083, besselGridState084, besselGridState089, besselGridState096, besselGridState101, besselGridState103, besselStateSubset, linearInterval, widenInterval,
    rationalErrorInterval, rationalIntervalSubset, orderedInterval, Finset.sum_range_succ,
    IntervalRat.add, IntervalRat.mul, IntervalRat.scale, IntervalRat.singleton]

theorem compactCertificate267_stateChecks2 :
    compactCertificate267.stateChecks 6 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 52 12 (653560504722797 / 4000000000000)) (orderedInterval (45293720030 / 1000000000000) (45293720031 / 1000000000000), orderedInterval (42812474861 / 1000000000000) (42812474862 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 89 12 (1119887064424481 / 4000000000000)) (orderedInterval (-43621532518 / 1000000000000) (-43621532517 / 1000000000000), orderedInterval (-19184256306 / 1000000000000) (-19184256305 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 66 12 (824903742990179 / 4000000000000)) (orderedInterval (-18234498009 / 1000000000000) (-18234497623 / 1000000000000), orderedInterval (52527651736 / 1000000000000) (52527652122 / 1000000000000))) = true
  norm_num [besselStateAtRationalPoint, besselIntervalStepZero,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, besselZeroTransition,
    besselInitial, besselGridStateAt, besselGridStateBlock00, besselGridStateBlock01,
    besselGridStateBlock02, besselGridStateBlock03, besselGridStateBlock04,
    besselGridStateBlock05, besselGridStateBlock06, besselGridStateBlock07,
    besselGridStateBlock08, besselGridStateBlock09, besselGridStateBlock10,
    besselGridStateBlock11, besselGridStateBlock12, besselGridStateBlock13,
    besselGridStateBlock14, besselGridState010, besselGridState013, besselGridState021, besselGridState024, besselGridState026, besselGridState033, besselGridState036, besselGridState039, besselGridState045, besselGridState046, besselGridState049, besselGridState052, besselGridState054, besselGridState056, besselGridState057, besselGridState058, besselGridState065, besselGridState066, besselGridState069, besselGridState071, besselGridState078, besselGridState083, besselGridState084, besselGridState089, besselGridState096, besselGridState101, besselGridState103, besselStateSubset, linearInterval, widenInterval,
    rationalErrorInterval, rationalIntervalSubset, orderedInterval, Finset.sum_range_succ,
    IntervalRat.add, IntervalRat.mul, IntervalRat.scale, IntervalRat.singleton]

theorem compactCertificate267_stateChecks3 :
    compactCertificate267.stateChecks 9 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 101 12 (1265614475264717 / 4000000000000)) (orderedInterval (5023882119 / 1000000000000) (5023882126 / 1000000000000), orderedInterval (-44581615676 / 1000000000000) (-44581615669 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 58 12 (730702857984293 / 4000000000000)) (orderedInterval (55985602387 / 1000000000000) (55985602388 / 1000000000000), orderedInterval (18570385454 / 1000000000000) (18570385455 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 103 12 (1296645044103337 / 4000000000000)) (orderedInterval (-43355489809 / 1000000000000) (-43355489801 / 1000000000000), orderedInterval (-9109059402 / 1000000000000) (-9109059394 / 1000000000000))) = true
  norm_num [besselStateAtRationalPoint, besselIntervalStepZero,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, besselZeroTransition,
    besselInitial, besselGridStateAt, besselGridStateBlock00, besselGridStateBlock01,
    besselGridStateBlock02, besselGridStateBlock03, besselGridStateBlock04,
    besselGridStateBlock05, besselGridStateBlock06, besselGridStateBlock07,
    besselGridStateBlock08, besselGridStateBlock09, besselGridStateBlock10,
    besselGridStateBlock11, besselGridStateBlock12, besselGridStateBlock13,
    besselGridStateBlock14, besselGridState010, besselGridState013, besselGridState021, besselGridState024, besselGridState026, besselGridState033, besselGridState036, besselGridState039, besselGridState045, besselGridState046, besselGridState049, besselGridState052, besselGridState054, besselGridState056, besselGridState057, besselGridState058, besselGridState065, besselGridState066, besselGridState069, besselGridState071, besselGridState078, besselGridState083, besselGridState084, besselGridState089, besselGridState096, besselGridState101, besselGridState103, besselStateSubset, linearInterval, widenInterval,
    rationalErrorInterval, rationalIntervalSubset, orderedInterval, Finset.sum_range_succ,
    IntervalRat.add, IntervalRat.mul, IntervalRat.scale, IntervalRat.singleton]

theorem compactCertificate267_stateChecks4 :
    compactCertificate267.stateChecks 12 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 96 12 (1211493996572653 / 4000000000000)) (orderedInterval (40348236719 / 1000000000000) (40348271387 / 1000000000000), orderedInterval (-21837010987 / 1000000000000) (-21836976319 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 69 12 (864579281114749 / 4000000000000)) (orderedInterval (-8632789695 / 1000000000000) (-8632789694 / 1000000000000), orderedInterval (-53560077220 / 1000000000000) (-53560077218 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 78 12 (980340757083771 / 4000000000000)) (orderedInterval (37466404890 / 1000000000000) (37466404891 / 1000000000000), orderedInterval (34475162817 / 1000000000000) (34475162818 / 1000000000000))) = true
  norm_num [besselStateAtRationalPoint, besselIntervalStepZero,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, besselZeroTransition,
    besselInitial, besselGridStateAt, besselGridStateBlock00, besselGridStateBlock01,
    besselGridStateBlock02, besselGridStateBlock03, besselGridStateBlock04,
    besselGridStateBlock05, besselGridStateBlock06, besselGridStateBlock07,
    besselGridStateBlock08, besselGridStateBlock09, besselGridStateBlock10,
    besselGridStateBlock11, besselGridStateBlock12, besselGridStateBlock13,
    besselGridStateBlock14, besselGridState010, besselGridState013, besselGridState021, besselGridState024, besselGridState026, besselGridState033, besselGridState036, besselGridState039, besselGridState045, besselGridState046, besselGridState049, besselGridState052, besselGridState054, besselGridState056, besselGridState057, besselGridState058, besselGridState065, besselGridState066, besselGridState069, besselGridState071, besselGridState078, besselGridState083, besselGridState084, besselGridState089, besselGridState096, besselGridState101, besselGridState103, besselStateSubset, linearInterval, widenInterval,
    rationalErrorInterval, rationalIntervalSubset, orderedInterval, Finset.sum_range_succ,
    IntervalRat.add, IntervalRat.mul, IntervalRat.scale, IntervalRat.singleton]

theorem compactCertificate267_stateChecks5 :
    compactCertificate267.stateChecks 15 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 65 12 (817305917594699 / 4000000000000)) (orderedInterval (-43991383168 / 1000000000000) (-43991383167 / 1000000000000), orderedInterval (-34250097854 / 1000000000000) (-34250097853 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 57 12 (722114564596679 / 4000000000000)) (orderedInterval (-46480840895 / 1000000000000) (-46480746246 / 1000000000000), orderedInterval (37087478044 / 1000000000000) (37087572692 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 83 12 (209296946587221 / 800000000000)) (orderedInterval (-49158806918 / 1000000000000) (-49158806591 / 1000000000000), orderedInterval (4189326867 / 1000000000000) (4189327194 / 1000000000000))) = true
  norm_num [besselStateAtRationalPoint, besselIntervalStepZero,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, besselZeroTransition,
    besselInitial, besselGridStateAt, besselGridStateBlock00, besselGridStateBlock01,
    besselGridStateBlock02, besselGridStateBlock03, besselGridStateBlock04,
    besselGridStateBlock05, besselGridStateBlock06, besselGridStateBlock07,
    besselGridStateBlock08, besselGridStateBlock09, besselGridStateBlock10,
    besselGridStateBlock11, besselGridStateBlock12, besselGridStateBlock13,
    besselGridStateBlock14, besselGridState010, besselGridState013, besselGridState021, besselGridState024, besselGridState026, besselGridState033, besselGridState036, besselGridState039, besselGridState045, besselGridState046, besselGridState049, besselGridState052, besselGridState054, besselGridState056, besselGridState057, besselGridState058, besselGridState065, besselGridState066, besselGridState069, besselGridState071, besselGridState078, besselGridState083, besselGridState084, besselGridState089, besselGridState096, besselGridState101, besselGridState103, besselStateSubset, linearInterval, widenInterval,
    rationalErrorInterval, rationalIntervalSubset, orderedInterval, Finset.sum_range_succ,
    IntervalRat.add, IntervalRat.mul, IntervalRat.scale, IntervalRat.singleton]

theorem compactCertificate267_stateChecks6 :
    compactCertificate267.stateChecks 18 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 46 12 (578926368955087 / 4000000000000)) (orderedInterval (55910395902 / 1000000000000) (55910395903 / 1000000000000), orderedInterval (35480930507 / 1000000000000) (35480930508 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 39 12 (490762294397207 / 4000000000000)) (orderedInterval (-58711654667 / 1000000000000) (-58711654666 / 1000000000000), orderedInterval (-41495030603 / 1000000000000) (-41495030602 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 24 12 (307096257009821 / 4000000000000)) (orderedInterval (75725550428 / 1000000000000) (75725579459 / 1000000000000), orderedInterval (-51066789489 / 1000000000000) (-51066760458 / 1000000000000))) = true
  norm_num [besselStateAtRationalPoint, besselIntervalStepZero,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, besselZeroTransition,
    besselInitial, besselGridStateAt, besselGridStateBlock00, besselGridStateBlock01,
    besselGridStateBlock02, besselGridStateBlock03, besselGridStateBlock04,
    besselGridStateBlock05, besselGridStateBlock06, besselGridStateBlock07,
    besselGridStateBlock08, besselGridStateBlock09, besselGridStateBlock10,
    besselGridStateBlock11, besselGridStateBlock12, besselGridStateBlock13,
    besselGridStateBlock14, besselGridState010, besselGridState013, besselGridState021, besselGridState024, besselGridState026, besselGridState033, besselGridState036, besselGridState039, besselGridState045, besselGridState046, besselGridState049, besselGridState052, besselGridState054, besselGridState056, besselGridState057, besselGridState058, besselGridState065, besselGridState066, besselGridState069, besselGridState071, besselGridState078, besselGridState083, besselGridState084, besselGridState089, besselGridState096, besselGridState101, besselGridState103, besselStateSubset, linearInterval, widenInterval,
    rationalErrorInterval, rationalIntervalSubset, orderedInterval, Finset.sum_range_succ,
    IntervalRat.add, IntervalRat.mul, IntervalRat.scale, IntervalRat.singleton]

theorem compactCertificate267_stateChecks7 :
    compactCertificate267.stateChecks 21 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 13 12 (165157388375907 / 4000000000000)) (orderedInterval (-117067759711 / 1000000000000) (-117067759710 / 1000000000000), orderedInterval (-39968067610 / 1000000000000) (-39968067609 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 36 12 (448434437128721 / 4000000000000)) (orderedInterval (-15298932718 / 1000000000000) (-15298932589 / 1000000000000), orderedInterval (73855715940 / 1000000000000) (73855716068 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 49 12 (612298886060017 / 4000000000000)) (orderedInterval (5072438382 / 1000000000000) (5072438396 / 1000000000000), orderedInterval (-64306339883 / 1000000000000) (-64306339868 / 1000000000000))) = true
  norm_num [besselStateAtRationalPoint, besselIntervalStepZero,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, besselZeroTransition,
    besselInitial, besselGridStateAt, besselGridStateBlock00, besselGridStateBlock01,
    besselGridStateBlock02, besselGridStateBlock03, besselGridStateBlock04,
    besselGridStateBlock05, besselGridStateBlock06, besselGridStateBlock07,
    besselGridStateBlock08, besselGridStateBlock09, besselGridStateBlock10,
    besselGridStateBlock11, besselGridStateBlock12, besselGridStateBlock13,
    besselGridStateBlock14, besselGridState010, besselGridState013, besselGridState021, besselGridState024, besselGridState026, besselGridState033, besselGridState036, besselGridState039, besselGridState045, besselGridState046, besselGridState049, besselGridState052, besselGridState054, besselGridState056, besselGridState057, besselGridState058, besselGridState065, besselGridState066, besselGridState069, besselGridState071, besselGridState078, besselGridState083, besselGridState084, besselGridState089, besselGridState096, besselGridState101, besselGridState103, besselStateSubset, linearInterval, widenInterval,
    rationalErrorInterval, rationalIntervalSubset, orderedInterval, Finset.sum_range_succ,
    IntervalRat.add, IntervalRat.mul, IntervalRat.scale, IntervalRat.singleton]

theorem compactCertificate267_stateChecks8 :
    compactCertificate267.stateChecks 24 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 21 12 (258903742990179 / 4000000000000)) (orderedInterval (44386661073 / 1000000000000) (44386665072 / 1000000000000), orderedInterval (-89031199050 / 1000000000000) (-89031195050 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 84 12 (1052429341349059 / 4000000000000)) (orderedInterval (-74988938 / 1000000000000) (-74988936 / 1000000000000), orderedInterval (49189762872 / 1000000000000) (49189762874 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 56 12 (702974026168781 / 4000000000000)) (orderedInterval (33934439579 / 1000000000000) (33934439580 / 1000000000000), orderedInterval (49611564448 / 1000000000000) (49611564449 / 1000000000000))) = true
  norm_num [besselStateAtRationalPoint, besselIntervalStepZero,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, besselZeroTransition,
    besselInitial, besselGridStateAt, besselGridStateBlock00, besselGridStateBlock01,
    besselGridStateBlock02, besselGridStateBlock03, besselGridStateBlock04,
    besselGridStateBlock05, besselGridStateBlock06, besselGridStateBlock07,
    besselGridStateBlock08, besselGridStateBlock09, besselGridStateBlock10,
    besselGridStateBlock11, besselGridStateBlock12, besselGridStateBlock13,
    besselGridStateBlock14, besselGridState010, besselGridState013, besselGridState021, besselGridState024, besselGridState026, besselGridState033, besselGridState036, besselGridState039, besselGridState045, besselGridState046, besselGridState049, besselGridState052, besselGridState054, besselGridState056, besselGridState057, besselGridState058, besselGridState065, besselGridState066, besselGridState069, besselGridState071, besselGridState078, besselGridState083, besselGridState084, besselGridState089, besselGridState096, besselGridState101, besselGridState103, besselStateSubset, linearInterval, widenInterval,
    rationalErrorInterval, rationalIntervalSubset, orderedInterval, Finset.sum_range_succ,
    IntervalRat.add, IntervalRat.mul, IntervalRat.scale, IntervalRat.singleton]

theorem compactCertificate267_states : ∀ j,
    BesselStateValid (compactCertificate267.point j) (compactCertificate267.state j) :=
  compactCertificate267.statesValid_of_checks3 compactCertificate267_stateChecks0
    compactCertificate267_stateChecks1 compactCertificate267_stateChecks2
    compactCertificate267_stateChecks3 compactCertificate267_stateChecks4
    compactCertificate267_stateChecks5 compactCertificate267_stateChecks6
    compactCertificate267_stateChecks7 compactCertificate267_stateChecks8

theorem compactCertificate267_chunkChecks0_0 :
    compactCertificate267.chunkChecks (0 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 0) <| besselDerivativeNearFromState (283 / 2) 0 (IntervalRat.scale (283 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-53072860794 / 1000000000000) (-53072860793 / 1000000000000), orderedInterval (-40828853054 / 1000000000000) (-40828853053 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 0) <| besselDerivativeNearFromState (416913038255983 / 4000000000000) 0 (IntervalRat.scale (283 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-76078819822 / 1000000000000) (-76078819820 / 1000000000000), orderedInterval (-17520473070 / 1000000000000) (-17520473068 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 0) <| besselDerivativeNearFromState (134821110553039 / 800000000000) 0 (IntervalRat.scale (283 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-20204339112 / 1000000000000) (-20204338618 / 1000000000000), orderedInterval (58106175081 / 1000000000000) (58106175575 / 1000000000000)))) (orderedInterval (-22930744762 / 1000000000000) (-22930744722 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 0) <| besselDerivativeNearFromState (121654184767181 / 4000000000000) 0 (IntervalRat.scale (283 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-31725043373 / 1000000000000) (-31725043103 / 1000000000000), orderedInterval (141688649539 / 1000000000000) (141688649809 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 0) <| besselDerivativeNearFromState (326780252361257 / 4000000000000) 0 (IntervalRat.scale (283 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (63172084504 / 1000000000000) (63172084505 / 1000000000000), orderedInterval (61273082370 / 1000000000000) (61273082371 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 0) <| besselDerivativeNearFromState (887271952972869 / 4000000000000) 0 (IntervalRat.scale (283 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (23314473392 / 1000000000000) (23314474828 / 1000000000000), orderedInterval (-48285835669 / 1000000000000) (-48285834233 / 1000000000000)))) (orderedInterval (993299674 / 1000000000000) (993299797 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 0) <| besselDerivativeNearFromState (653560504722797 / 4000000000000) 0 (IntervalRat.scale (283 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (45293720030 / 1000000000000) (45293720031 / 1000000000000), orderedInterval (42812474861 / 1000000000000) (42812474862 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 0) <| besselDerivativeNearFromState (1119887064424481 / 4000000000000) 0 (IntervalRat.scale (283 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-43621532518 / 1000000000000) (-43621532517 / 1000000000000), orderedInterval (-19184256306 / 1000000000000) (-19184256305 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 0) <| besselDerivativeNearFromState (824903742990179 / 4000000000000) 0 (IntervalRat.scale (283 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-18234498009 / 1000000000000) (-18234497623 / 1000000000000), orderedInterval (52527651736 / 1000000000000) (52527652122 / 1000000000000)))) (orderedInterval (904770748 / 1000000000000) (904770766 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate267_chunkChecks0_1 :
    compactCertificate267.chunkChecks (0 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 0) <| besselDerivativeNearFromState (1265614475264717 / 4000000000000) 0 (IntervalRat.scale (283 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (5023882119 / 1000000000000) (5023882126 / 1000000000000), orderedInterval (-44581615676 / 1000000000000) (-44581615669 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 0) <| besselDerivativeNearFromState (730702857984293 / 4000000000000) 0 (IntervalRat.scale (283 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (55985602387 / 1000000000000) (55985602388 / 1000000000000), orderedInterval (18570385454 / 1000000000000) (18570385455 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 0) <| besselDerivativeNearFromState (1296645044103337 / 4000000000000) 0 (IntervalRat.scale (283 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-43355489809 / 1000000000000) (-43355489801 / 1000000000000), orderedInterval (-9109059402 / 1000000000000) (-9109059394 / 1000000000000)))) (orderedInterval (-2907849119 / 1000000000000) (-2907849060 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 0) <| besselDerivativeNearFromState (1211493996572653 / 4000000000000) 0 (IntervalRat.scale (283 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (40348236719 / 1000000000000) (40348271387 / 1000000000000), orderedInterval (-21837010987 / 1000000000000) (-21836976319 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 0) <| besselDerivativeNearFromState (864579281114749 / 4000000000000) 0 (IntervalRat.scale (283 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-8632789695 / 1000000000000) (-8632789694 / 1000000000000), orderedInterval (-53560077220 / 1000000000000) (-53560077218 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 0) <| besselDerivativeNearFromState (980340757083771 / 4000000000000) 0 (IntervalRat.scale (283 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (37466404890 / 1000000000000) (37466404891 / 1000000000000), orderedInterval (34475162817 / 1000000000000) (34475162818 / 1000000000000)))) (orderedInterval (-1734353747 / 1000000000000) (-1734353103 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 0) <| besselDerivativeNearFromState (817305917594699 / 4000000000000) 0 (IntervalRat.scale (283 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-43991383168 / 1000000000000) (-43991383167 / 1000000000000), orderedInterval (-34250097854 / 1000000000000) (-34250097853 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 0) <| besselDerivativeNearFromState (722114564596679 / 4000000000000) 0 (IntervalRat.scale (283 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-46480840895 / 1000000000000) (-46480746246 / 1000000000000), orderedInterval (37087478044 / 1000000000000) (37087572692 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 0) <| besselDerivativeNearFromState (209296946587221 / 800000000000) 0 (IntervalRat.scale (283 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-49158806918 / 1000000000000) (-49158806591 / 1000000000000), orderedInterval (4189326867 / 1000000000000) (4189327194 / 1000000000000)))) (orderedInterval (893281035 / 1000000000000) (893286474 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate267_chunkChecks0_2 :
    compactCertificate267.chunkChecks (0 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 0) <| besselDerivativeNearFromState (578926368955087 / 4000000000000) 0 (IntervalRat.scale (283 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (55910395902 / 1000000000000) (55910395903 / 1000000000000), orderedInterval (35480930507 / 1000000000000) (35480930508 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 0) <| besselDerivativeNearFromState (490762294397207 / 4000000000000) 0 (IntervalRat.scale (283 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-58711654667 / 1000000000000) (-58711654666 / 1000000000000), orderedInterval (-41495030603 / 1000000000000) (-41495030602 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 0) <| besselDerivativeNearFromState (307096257009821 / 4000000000000) 0 (IntervalRat.scale (283 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (75725550428 / 1000000000000) (75725579459 / 1000000000000), orderedInterval (-51066789489 / 1000000000000) (-51066760458 / 1000000000000)))) (orderedInterval (-3151306866 / 1000000000000) (-3151305884 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 0) <| besselDerivativeNearFromState (165157388375907 / 4000000000000) 0 (IntervalRat.scale (283 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-117067759711 / 1000000000000) (-117067759710 / 1000000000000), orderedInterval (-39968067610 / 1000000000000) (-39968067609 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 0) <| besselDerivativeNearFromState (448434437128721 / 4000000000000) 0 (IntervalRat.scale (283 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-15298932718 / 1000000000000) (-15298932589 / 1000000000000), orderedInterval (73855715940 / 1000000000000) (73855716068 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 0) <| besselDerivativeNearFromState (612298886060017 / 4000000000000) 0 (IntervalRat.scale (283 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (5072438382 / 1000000000000) (5072438396 / 1000000000000), orderedInterval (-64306339883 / 1000000000000) (-64306339868 / 1000000000000)))) (orderedInterval (2120008697 / 1000000000000) (2120008718 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 0) <| besselDerivativeNearFromState (258903742990179 / 4000000000000) 0 (IntervalRat.scale (283 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (44386661073 / 1000000000000) (44386665072 / 1000000000000), orderedInterval (-89031199050 / 1000000000000) (-89031195050 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 0) <| besselDerivativeNearFromState (1052429341349059 / 4000000000000) 0 (IntervalRat.scale (283 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-74988938 / 1000000000000) (-74988936 / 1000000000000), orderedInterval (49189762872 / 1000000000000) (49189762874 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 0) <| besselDerivativeNearFromState (702974026168781 / 4000000000000) 0 (IntervalRat.scale (283 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (33934439579 / 1000000000000) (33934439580 / 1000000000000), orderedInterval (49611564448 / 1000000000000) (49611564449 / 1000000000000)))) (orderedInterval (-6093319480 / 1000000000000) (-6093319415 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate267_chunkChecks0 :
    compactCertificate267.chunkChecks (0 : Fin 5) 0 9 = true :=
  compactCertificate267.chunkChecks_nine_of_three (0 : Fin 5) compactCertificate267_chunkChecks0_0
    compactCertificate267_chunkChecks0_1 compactCertificate267_chunkChecks0_2

theorem compactCertificate267_chunkChecks1_0 :
    compactCertificate267.chunkChecks (1 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 1) <| besselDerivativeNearFromState (283 / 2) 1 (IntervalRat.scale (283 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-53072860794 / 1000000000000) (-53072860793 / 1000000000000), orderedInterval (-40828853054 / 1000000000000) (-40828853053 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 1) <| besselDerivativeNearFromState (416913038255983 / 4000000000000) 1 (IntervalRat.scale (283 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-76078819822 / 1000000000000) (-76078819820 / 1000000000000), orderedInterval (-17520473070 / 1000000000000) (-17520473068 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 1) <| besselDerivativeNearFromState (134821110553039 / 800000000000) 1 (IntervalRat.scale (283 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-20204339112 / 1000000000000) (-20204338618 / 1000000000000), orderedInterval (58106175081 / 1000000000000) (58106175575 / 1000000000000)))) (orderedInterval (-12242388705 / 1000000000000) (-12242388658 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 1) <| besselDerivativeNearFromState (121654184767181 / 4000000000000) 1 (IntervalRat.scale (283 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-31725043373 / 1000000000000) (-31725043103 / 1000000000000), orderedInterval (141688649539 / 1000000000000) (141688649809 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 1) <| besselDerivativeNearFromState (326780252361257 / 4000000000000) 1 (IntervalRat.scale (283 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (63172084504 / 1000000000000) (63172084505 / 1000000000000), orderedInterval (61273082370 / 1000000000000) (61273082371 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 1) <| besselDerivativeNearFromState (887271952972869 / 4000000000000) 1 (IntervalRat.scale (283 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (23314473392 / 1000000000000) (23314474828 / 1000000000000), orderedInterval (-48285835669 / 1000000000000) (-48285834233 / 1000000000000)))) (orderedInterval (6342277315 / 1000000000000) (6342277495 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 1) <| besselDerivativeNearFromState (653560504722797 / 4000000000000) 1 (IntervalRat.scale (283 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (45293720030 / 1000000000000) (45293720031 / 1000000000000), orderedInterval (42812474861 / 1000000000000) (42812474862 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 1) <| besselDerivativeNearFromState (1119887064424481 / 4000000000000) 1 (IntervalRat.scale (283 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-43621532518 / 1000000000000) (-43621532517 / 1000000000000), orderedInterval (-19184256306 / 1000000000000) (-19184256305 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 1) <| besselDerivativeNearFromState (824903742990179 / 4000000000000) 1 (IntervalRat.scale (283 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-18234498009 / 1000000000000) (-18234497623 / 1000000000000), orderedInterval (52527651736 / 1000000000000) (52527652122 / 1000000000000)))) (orderedInterval (3020963792 / 1000000000000) (3020963821 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate267_chunkChecks1_1 :
    compactCertificate267.chunkChecks (1 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 1) <| besselDerivativeNearFromState (1265614475264717 / 4000000000000) 1 (IntervalRat.scale (283 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (5023882119 / 1000000000000) (5023882126 / 1000000000000), orderedInterval (-44581615676 / 1000000000000) (-44581615669 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 1) <| besselDerivativeNearFromState (730702857984293 / 4000000000000) 1 (IntervalRat.scale (283 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (55985602387 / 1000000000000) (55985602388 / 1000000000000), orderedInterval (18570385454 / 1000000000000) (18570385455 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 1) <| besselDerivativeNearFromState (1296645044103337 / 4000000000000) 1 (IntervalRat.scale (283 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-43355489809 / 1000000000000) (-43355489801 / 1000000000000), orderedInterval (-9109059402 / 1000000000000) (-9109059394 / 1000000000000)))) (orderedInterval (16523073647 / 1000000000000) (16523073770 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 1) <| besselDerivativeNearFromState (1211493996572653 / 4000000000000) 1 (IntervalRat.scale (283 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (40348236719 / 1000000000000) (40348271387 / 1000000000000), orderedInterval (-21837010987 / 1000000000000) (-21836976319 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 1) <| besselDerivativeNearFromState (864579281114749 / 4000000000000) 1 (IntervalRat.scale (283 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-8632789695 / 1000000000000) (-8632789694 / 1000000000000), orderedInterval (-53560077220 / 1000000000000) (-53560077218 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 1) <| besselDerivativeNearFromState (980340757083771 / 4000000000000) 1 (IntervalRat.scale (283 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (37466404890 / 1000000000000) (37466404891 / 1000000000000), orderedInterval (34475162817 / 1000000000000) (34475162818 / 1000000000000)))) (orderedInterval (-7194964080 / 1000000000000) (-7194962712 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 1) <| besselDerivativeNearFromState (817305917594699 / 4000000000000) 1 (IntervalRat.scale (283 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-43991383168 / 1000000000000) (-43991383167 / 1000000000000), orderedInterval (-34250097854 / 1000000000000) (-34250097853 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 1) <| besselDerivativeNearFromState (722114564596679 / 4000000000000) 1 (IntervalRat.scale (283 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-46480840895 / 1000000000000) (-46480746246 / 1000000000000), orderedInterval (37087478044 / 1000000000000) (37087572692 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 1) <| besselDerivativeNearFromState (209296946587221 / 800000000000) 1 (IntervalRat.scale (283 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-49158806918 / 1000000000000) (-49158806591 / 1000000000000), orderedInterval (4189326867 / 1000000000000) (4189327194 / 1000000000000)))) (orderedInterval (-3080595740 / 1000000000000) (-3080588793 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate267_chunkChecks1_2 :
    compactCertificate267.chunkChecks (1 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 1) <| besselDerivativeNearFromState (578926368955087 / 4000000000000) 1 (IntervalRat.scale (283 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (55910395902 / 1000000000000) (55910395903 / 1000000000000), orderedInterval (35480930507 / 1000000000000) (35480930508 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 1) <| besselDerivativeNearFromState (490762294397207 / 4000000000000) 1 (IntervalRat.scale (283 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-58711654667 / 1000000000000) (-58711654666 / 1000000000000), orderedInterval (-41495030603 / 1000000000000) (-41495030602 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 1) <| besselDerivativeNearFromState (307096257009821 / 4000000000000) 1 (IntervalRat.scale (283 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (75725550428 / 1000000000000) (75725579459 / 1000000000000), orderedInterval (-51066789489 / 1000000000000) (-51066760458 / 1000000000000)))) (orderedInterval (-4668301923 / 1000000000000) (-4668301376 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 1) <| besselDerivativeNearFromState (165157388375907 / 4000000000000) 1 (IntervalRat.scale (283 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-117067759711 / 1000000000000) (-117067759710 / 1000000000000), orderedInterval (-39968067610 / 1000000000000) (-39968067609 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 1) <| besselDerivativeNearFromState (448434437128721 / 4000000000000) 1 (IntervalRat.scale (283 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-15298932718 / 1000000000000) (-15298932589 / 1000000000000), orderedInterval (73855715940 / 1000000000000) (73855716068 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 1) <| besselDerivativeNearFromState (612298886060017 / 4000000000000) 1 (IntervalRat.scale (283 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (5072438382 / 1000000000000) (5072438396 / 1000000000000), orderedInterval (-64306339883 / 1000000000000) (-64306339868 / 1000000000000)))) (orderedInterval (4219337202 / 1000000000000) (4219337222 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 1) <| besselDerivativeNearFromState (258903742990179 / 4000000000000) 1 (IntervalRat.scale (283 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (44386661073 / 1000000000000) (44386665072 / 1000000000000), orderedInterval (-89031199050 / 1000000000000) (-89031195050 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 1) <| besselDerivativeNearFromState (1052429341349059 / 4000000000000) 1 (IntervalRat.scale (283 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-74988938 / 1000000000000) (-74988936 / 1000000000000), orderedInterval (49189762872 / 1000000000000) (49189762874 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 1) <| besselDerivativeNearFromState (702974026168781 / 4000000000000) 1 (IntervalRat.scale (283 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (33934439579 / 1000000000000) (33934439580 / 1000000000000), orderedInterval (49611564448 / 1000000000000) (49611564449 / 1000000000000)))) (orderedInterval (-19251978292 / 1000000000000) (-19251978224 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate267_chunkChecks1 :
    compactCertificate267.chunkChecks (1 : Fin 5) 0 9 = true :=
  compactCertificate267.chunkChecks_nine_of_three (1 : Fin 5) compactCertificate267_chunkChecks1_0
    compactCertificate267_chunkChecks1_1 compactCertificate267_chunkChecks1_2

theorem compactCertificate267_chunkChecks2_0 :
    compactCertificate267.chunkChecks (2 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 2) <| besselDerivativeNearFromState (283 / 2) 2 (IntervalRat.scale (283 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-53072860794 / 1000000000000) (-53072860793 / 1000000000000), orderedInterval (-40828853054 / 1000000000000) (-40828853053 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 2) <| besselDerivativeNearFromState (416913038255983 / 4000000000000) 2 (IntervalRat.scale (283 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-76078819822 / 1000000000000) (-76078819820 / 1000000000000), orderedInterval (-17520473070 / 1000000000000) (-17520473068 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 2) <| besselDerivativeNearFromState (134821110553039 / 800000000000) 2 (IntervalRat.scale (283 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-20204339112 / 1000000000000) (-20204338618 / 1000000000000), orderedInterval (58106175081 / 1000000000000) (58106175575 / 1000000000000)))) (orderedInterval (23189144629 / 1000000000000) (23189144685 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 2) <| besselDerivativeNearFromState (121654184767181 / 4000000000000) 2 (IntervalRat.scale (283 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-31725043373 / 1000000000000) (-31725043103 / 1000000000000), orderedInterval (141688649539 / 1000000000000) (141688649809 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 2) <| besselDerivativeNearFromState (326780252361257 / 4000000000000) 2 (IntervalRat.scale (283 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (63172084504 / 1000000000000) (63172084505 / 1000000000000), orderedInterval (61273082370 / 1000000000000) (61273082371 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 2) <| besselDerivativeNearFromState (887271952972869 / 4000000000000) 2 (IntervalRat.scale (283 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (23314473392 / 1000000000000) (23314474828 / 1000000000000), orderedInterval (-48285835669 / 1000000000000) (-48285834233 / 1000000000000)))) (orderedInterval (3243418989 / 1000000000000) (3243419268 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 2) <| besselDerivativeNearFromState (653560504722797 / 4000000000000) 2 (IntervalRat.scale (283 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (45293720030 / 1000000000000) (45293720031 / 1000000000000), orderedInterval (42812474861 / 1000000000000) (42812474862 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 2) <| besselDerivativeNearFromState (1119887064424481 / 4000000000000) 2 (IntervalRat.scale (283 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-43621532518 / 1000000000000) (-43621532517 / 1000000000000), orderedInterval (-19184256306 / 1000000000000) (-19184256305 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 2) <| besselDerivativeNearFromState (824903742990179 / 4000000000000) 2 (IntervalRat.scale (283 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-18234498009 / 1000000000000) (-18234497623 / 1000000000000), orderedInterval (52527651736 / 1000000000000) (52527652122 / 1000000000000)))) (orderedInterval (-4352568708 / 1000000000000) (-4352568663 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate267_chunkChecks2_1 :
    compactCertificate267.chunkChecks (2 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 2) <| besselDerivativeNearFromState (1265614475264717 / 4000000000000) 2 (IntervalRat.scale (283 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (5023882119 / 1000000000000) (5023882126 / 1000000000000), orderedInterval (-44581615676 / 1000000000000) (-44581615669 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 2) <| besselDerivativeNearFromState (730702857984293 / 4000000000000) 2 (IntervalRat.scale (283 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (55985602387 / 1000000000000) (55985602388 / 1000000000000), orderedInterval (18570385454 / 1000000000000) (18570385455 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 2) <| besselDerivativeNearFromState (1296645044103337 / 4000000000000) 2 (IntervalRat.scale (283 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-43355489809 / 1000000000000) (-43355489801 / 1000000000000), orderedInterval (-9109059402 / 1000000000000) (-9109059394 / 1000000000000)))) (orderedInterval (29779021597 / 1000000000000) (29779021859 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 2) <| besselDerivativeNearFromState (1211493996572653 / 4000000000000) 2 (IntervalRat.scale (283 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (40348236719 / 1000000000000) (40348271387 / 1000000000000), orderedInterval (-21837010987 / 1000000000000) (-21836976319 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 2) <| besselDerivativeNearFromState (864579281114749 / 4000000000000) 2 (IntervalRat.scale (283 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-8632789695 / 1000000000000) (-8632789694 / 1000000000000), orderedInterval (-53560077220 / 1000000000000) (-53560077218 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 2) <| besselDerivativeNearFromState (980340757083771 / 4000000000000) 2 (IntervalRat.scale (283 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (37466404890 / 1000000000000) (37466404891 / 1000000000000), orderedInterval (34475162817 / 1000000000000) (34475162818 / 1000000000000)))) (orderedInterval (5861675471 / 1000000000000) (5861678394 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 2) <| besselDerivativeNearFromState (817305917594699 / 4000000000000) 2 (IntervalRat.scale (283 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-43991383168 / 1000000000000) (-43991383167 / 1000000000000), orderedInterval (-34250097854 / 1000000000000) (-34250097853 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 2) <| besselDerivativeNearFromState (722114564596679 / 4000000000000) 2 (IntervalRat.scale (283 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-46480840895 / 1000000000000) (-46480746246 / 1000000000000), orderedInterval (37087478044 / 1000000000000) (37087572692 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 2) <| besselDerivativeNearFromState (209296946587221 / 800000000000) 2 (IntervalRat.scale (283 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-49158806918 / 1000000000000) (-49158806591 / 1000000000000), orderedInterval (4189326867 / 1000000000000) (4189327194 / 1000000000000)))) (orderedInterval (1054081777 / 1000000000000) (1054090701 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate267_chunkChecks2_2 :
    compactCertificate267.chunkChecks (2 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 2) <| besselDerivativeNearFromState (578926368955087 / 4000000000000) 2 (IntervalRat.scale (283 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (55910395902 / 1000000000000) (55910395903 / 1000000000000), orderedInterval (35480930507 / 1000000000000) (35480930508 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 2) <| besselDerivativeNearFromState (490762294397207 / 4000000000000) 2 (IntervalRat.scale (283 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-58711654667 / 1000000000000) (-58711654666 / 1000000000000), orderedInterval (-41495030603 / 1000000000000) (-41495030602 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 2) <| besselDerivativeNearFromState (307096257009821 / 4000000000000) 2 (IntervalRat.scale (283 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (75725550428 / 1000000000000) (75725579459 / 1000000000000), orderedInterval (-51066789489 / 1000000000000) (-51066760458 / 1000000000000)))) (orderedInterval (6161564229 / 1000000000000) (6161564543 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 2) <| besselDerivativeNearFromState (165157388375907 / 4000000000000) 2 (IntervalRat.scale (283 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-117067759711 / 1000000000000) (-117067759710 / 1000000000000), orderedInterval (-39968067610 / 1000000000000) (-39968067609 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 2) <| besselDerivativeNearFromState (448434437128721 / 4000000000000) 2 (IntervalRat.scale (283 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-15298932718 / 1000000000000) (-15298932589 / 1000000000000), orderedInterval (73855715940 / 1000000000000) (73855716068 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 2) <| besselDerivativeNearFromState (612298886060017 / 4000000000000) 2 (IntervalRat.scale (283 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (5072438382 / 1000000000000) (5072438396 / 1000000000000), orderedInterval (-64306339883 / 1000000000000) (-64306339868 / 1000000000000)))) (orderedInterval (23198784 / 1000000000000) (23198803 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 2) <| besselDerivativeNearFromState (258903742990179 / 4000000000000) 2 (IntervalRat.scale (283 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (44386661073 / 1000000000000) (44386665072 / 1000000000000), orderedInterval (-89031199050 / 1000000000000) (-89031195050 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 2) <| besselDerivativeNearFromState (1052429341349059 / 4000000000000) 2 (IntervalRat.scale (283 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-74988938 / 1000000000000) (-74988936 / 1000000000000), orderedInterval (49189762872 / 1000000000000) (49189762874 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 2) <| besselDerivativeNearFromState (702974026168781 / 4000000000000) 2 (IntervalRat.scale (283 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (33934439579 / 1000000000000) (33934439580 / 1000000000000), orderedInterval (49611564448 / 1000000000000) (49611564449 / 1000000000000)))) (orderedInterval (9880526846 / 1000000000000) (9880526933 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate267_chunkChecks2 :
    compactCertificate267.chunkChecks (2 : Fin 5) 0 9 = true :=
  compactCertificate267.chunkChecks_nine_of_three (2 : Fin 5) compactCertificate267_chunkChecks2_0
    compactCertificate267_chunkChecks2_1 compactCertificate267_chunkChecks2_2

theorem compactCertificate267_chunkChecks3_0 :
    compactCertificate267.chunkChecks (3 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 3) <| besselDerivativeNearFromState (283 / 2) 3 (IntervalRat.scale (283 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-53072860794 / 1000000000000) (-53072860793 / 1000000000000), orderedInterval (-40828853054 / 1000000000000) (-40828853053 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 3) <| besselDerivativeNearFromState (416913038255983 / 4000000000000) 3 (IntervalRat.scale (283 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-76078819822 / 1000000000000) (-76078819820 / 1000000000000), orderedInterval (-17520473070 / 1000000000000) (-17520473068 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 3) <| besselDerivativeNearFromState (134821110553039 / 800000000000) 3 (IntervalRat.scale (283 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-20204339112 / 1000000000000) (-20204338618 / 1000000000000), orderedInterval (58106175081 / 1000000000000) (58106175575 / 1000000000000)))) (orderedInterval (10323447760 / 1000000000000) (10323447825 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 3) <| besselDerivativeNearFromState (121654184767181 / 4000000000000) 3 (IntervalRat.scale (283 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-31725043373 / 1000000000000) (-31725043103 / 1000000000000), orderedInterval (141688649539 / 1000000000000) (141688649809 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 3) <| besselDerivativeNearFromState (326780252361257 / 4000000000000) 3 (IntervalRat.scale (283 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (63172084504 / 1000000000000) (63172084505 / 1000000000000), orderedInterval (61273082370 / 1000000000000) (61273082371 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 3) <| besselDerivativeNearFromState (887271952972869 / 4000000000000) 3 (IntervalRat.scale (283 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (23314473392 / 1000000000000) (23314474828 / 1000000000000), orderedInterval (-48285835669 / 1000000000000) (-48285834233 / 1000000000000)))) (orderedInterval (-13661406726 / 1000000000000) (-13661406290 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 3) <| besselDerivativeNearFromState (653560504722797 / 4000000000000) 3 (IntervalRat.scale (283 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (45293720030 / 1000000000000) (45293720031 / 1000000000000), orderedInterval (42812474861 / 1000000000000) (42812474862 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 3) <| besselDerivativeNearFromState (1119887064424481 / 4000000000000) 3 (IntervalRat.scale (283 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-43621532518 / 1000000000000) (-43621532517 / 1000000000000), orderedInterval (-19184256306 / 1000000000000) (-19184256305 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 3) <| besselDerivativeNearFromState (824903742990179 / 4000000000000) 3 (IntervalRat.scale (283 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-18234498009 / 1000000000000) (-18234497623 / 1000000000000), orderedInterval (52527651736 / 1000000000000) (52527652122 / 1000000000000)))) (orderedInterval (-8482477085 / 1000000000000) (-8482477011 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate267_chunkChecks3_1 :
    compactCertificate267.chunkChecks (3 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 3) <| besselDerivativeNearFromState (1265614475264717 / 4000000000000) 3 (IntervalRat.scale (283 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (5023882119 / 1000000000000) (5023882126 / 1000000000000), orderedInterval (-44581615676 / 1000000000000) (-44581615669 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 3) <| besselDerivativeNearFromState (730702857984293 / 4000000000000) 3 (IntervalRat.scale (283 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (55985602387 / 1000000000000) (55985602388 / 1000000000000), orderedInterval (18570385454 / 1000000000000) (18570385455 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 3) <| besselDerivativeNearFromState (1296645044103337 / 4000000000000) 3 (IntervalRat.scale (283 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-43355489809 / 1000000000000) (-43355489801 / 1000000000000), orderedInterval (-9109059402 / 1000000000000) (-9109059394 / 1000000000000)))) (orderedInterval (-76167764127 / 1000000000000) (-76167763552 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 3) <| besselDerivativeNearFromState (1211493996572653 / 4000000000000) 3 (IntervalRat.scale (283 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (40348236719 / 1000000000000) (40348271387 / 1000000000000), orderedInterval (-21837010987 / 1000000000000) (-21836976319 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 3) <| besselDerivativeNearFromState (864579281114749 / 4000000000000) 3 (IntervalRat.scale (283 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-8632789695 / 1000000000000) (-8632789694 / 1000000000000), orderedInterval (-53560077220 / 1000000000000) (-53560077218 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 3) <| besselDerivativeNearFromState (980340757083771 / 4000000000000) 3 (IntervalRat.scale (283 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (37466404890 / 1000000000000) (37466404891 / 1000000000000), orderedInterval (34475162817 / 1000000000000) (34475162818 / 1000000000000)))) (orderedInterval (15050851418 / 1000000000000) (15050857654 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 3) <| besselDerivativeNearFromState (817305917594699 / 4000000000000) 3 (IntervalRat.scale (283 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-43991383168 / 1000000000000) (-43991383167 / 1000000000000), orderedInterval (-34250097854 / 1000000000000) (-34250097853 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 3) <| besselDerivativeNearFromState (722114564596679 / 4000000000000) 3 (IntervalRat.scale (283 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-46480840895 / 1000000000000) (-46480746246 / 1000000000000), orderedInterval (37087478044 / 1000000000000) (37087572692 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 3) <| besselDerivativeNearFromState (209296946587221 / 800000000000) 3 (IntervalRat.scale (283 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-49158806918 / 1000000000000) (-49158806591 / 1000000000000), orderedInterval (4189326867 / 1000000000000) (4189327194 / 1000000000000)))) (orderedInterval (4912828031 / 1000000000000) (4912839440 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate267_chunkChecks3_2 :
    compactCertificate267.chunkChecks (3 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 3) <| besselDerivativeNearFromState (578926368955087 / 4000000000000) 3 (IntervalRat.scale (283 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (55910395902 / 1000000000000) (55910395903 / 1000000000000), orderedInterval (35480930507 / 1000000000000) (35480930508 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 3) <| besselDerivativeNearFromState (490762294397207 / 4000000000000) 3 (IntervalRat.scale (283 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-58711654667 / 1000000000000) (-58711654666 / 1000000000000), orderedInterval (-41495030603 / 1000000000000) (-41495030602 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 3) <| besselDerivativeNearFromState (307096257009821 / 4000000000000) 3 (IntervalRat.scale (283 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (75725550428 / 1000000000000) (75725579459 / 1000000000000), orderedInterval (-51066789489 / 1000000000000) (-51066760458 / 1000000000000)))) (orderedInterval (4761528170 / 1000000000000) (4761528354 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 3) <| besselDerivativeNearFromState (165157388375907 / 4000000000000) 3 (IntervalRat.scale (283 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-117067759711 / 1000000000000) (-117067759710 / 1000000000000), orderedInterval (-39968067610 / 1000000000000) (-39968067609 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 3) <| besselDerivativeNearFromState (448434437128721 / 4000000000000) 3 (IntervalRat.scale (283 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-15298932718 / 1000000000000) (-15298932589 / 1000000000000), orderedInterval (73855715940 / 1000000000000) (73855716068 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 3) <| besselDerivativeNearFromState (612298886060017 / 4000000000000) 3 (IntervalRat.scale (283 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (5072438382 / 1000000000000) (5072438396 / 1000000000000), orderedInterval (-64306339883 / 1000000000000) (-64306339868 / 1000000000000)))) (orderedInterval (-5424397174 / 1000000000000) (-5424397155 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 3) <| besselDerivativeNearFromState (258903742990179 / 4000000000000) 3 (IntervalRat.scale (283 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (44386661073 / 1000000000000) (44386665072 / 1000000000000), orderedInterval (-89031199050 / 1000000000000) (-89031195050 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 3) <| besselDerivativeNearFromState (1052429341349059 / 4000000000000) 3 (IntervalRat.scale (283 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-74988938 / 1000000000000) (-74988936 / 1000000000000), orderedInterval (49189762872 / 1000000000000) (49189762874 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 3) <| besselDerivativeNearFromState (702974026168781 / 4000000000000) 3 (IntervalRat.scale (283 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (33934439579 / 1000000000000) (33934439580 / 1000000000000), orderedInterval (49611564448 / 1000000000000) (49611564449 / 1000000000000)))) (orderedInterval (43556210905 / 1000000000000) (43556211035 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate267_chunkChecks3 :
    compactCertificate267.chunkChecks (3 : Fin 5) 0 9 = true :=
  compactCertificate267.chunkChecks_nine_of_three (3 : Fin 5) compactCertificate267_chunkChecks3_0
    compactCertificate267_chunkChecks3_1 compactCertificate267_chunkChecks3_2

theorem compactCertificate267_chunkChecks4_0 :
    compactCertificate267.chunkChecks (4 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 4) <| besselDerivativeNearFromState (283 / 2) 4 (IntervalRat.scale (283 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-53072860794 / 1000000000000) (-53072860793 / 1000000000000), orderedInterval (-40828853054 / 1000000000000) (-40828853053 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 4) <| besselDerivativeNearFromState (416913038255983 / 4000000000000) 4 (IntervalRat.scale (283 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-76078819822 / 1000000000000) (-76078819820 / 1000000000000), orderedInterval (-17520473070 / 1000000000000) (-17520473068 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 4) <| besselDerivativeNearFromState (134821110553039 / 800000000000) 4 (IntervalRat.scale (283 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-20204339112 / 1000000000000) (-20204338618 / 1000000000000), orderedInterval (58106175081 / 1000000000000) (58106175575 / 1000000000000)))) (orderedInterval (-23775220989 / 1000000000000) (-23775220911 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 4) <| besselDerivativeNearFromState (121654184767181 / 4000000000000) 4 (IntervalRat.scale (283 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-31725043373 / 1000000000000) (-31725043103 / 1000000000000), orderedInterval (141688649539 / 1000000000000) (141688649809 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 4) <| besselDerivativeNearFromState (326780252361257 / 4000000000000) 4 (IntervalRat.scale (283 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (63172084504 / 1000000000000) (63172084505 / 1000000000000), orderedInterval (61273082370 / 1000000000000) (61273082371 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 4) <| besselDerivativeNearFromState (887271952972869 / 4000000000000) 4 (IntervalRat.scale (283 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (23314473392 / 1000000000000) (23314474828 / 1000000000000), orderedInterval (-48285835669 / 1000000000000) (-48285834233 / 1000000000000)))) (orderedInterval (-9558790220 / 1000000000000) (-9558789535 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 4) <| besselDerivativeNearFromState (653560504722797 / 4000000000000) 4 (IntervalRat.scale (283 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (45293720030 / 1000000000000) (45293720031 / 1000000000000), orderedInterval (42812474861 / 1000000000000) (42812474862 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 4) <| besselDerivativeNearFromState (1119887064424481 / 4000000000000) 4 (IntervalRat.scale (283 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-43621532518 / 1000000000000) (-43621532517 / 1000000000000), orderedInterval (-19184256306 / 1000000000000) (-19184256305 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 4) <| besselDerivativeNearFromState (824903742990179 / 4000000000000) 4 (IntervalRat.scale (283 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-18234498009 / 1000000000000) (-18234497623 / 1000000000000), orderedInterval (52527651736 / 1000000000000) (52527652122 / 1000000000000)))) (orderedInterval (18752045106 / 1000000000000) (18752045232 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate267_chunkChecks4_1 :
    compactCertificate267.chunkChecks (4 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 4) <| besselDerivativeNearFromState (1265614475264717 / 4000000000000) 4 (IntervalRat.scale (283 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (5023882119 / 1000000000000) (5023882126 / 1000000000000), orderedInterval (-44581615676 / 1000000000000) (-44581615669 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 4) <| besselDerivativeNearFromState (730702857984293 / 4000000000000) 4 (IntervalRat.scale (283 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (55985602387 / 1000000000000) (55985602388 / 1000000000000), orderedInterval (18570385454 / 1000000000000) (18570385455 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 4) <| besselDerivativeNearFromState (1296645044103337 / 4000000000000) 4 (IntervalRat.scale (283 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-43355489809 / 1000000000000) (-43355489801 / 1000000000000), orderedInterval (-9109059402 / 1000000000000) (-9109059394 / 1000000000000)))) (orderedInterval (-179473585103 / 1000000000000) (-179473583827 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 4) <| besselDerivativeNearFromState (1211493996572653 / 4000000000000) 4 (IntervalRat.scale (283 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (40348236719 / 1000000000000) (40348271387 / 1000000000000), orderedInterval (-21837010987 / 1000000000000) (-21836976319 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 4) <| besselDerivativeNearFromState (864579281114749 / 4000000000000) 4 (IntervalRat.scale (283 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-8632789695 / 1000000000000) (-8632789694 / 1000000000000), orderedInterval (-53560077220 / 1000000000000) (-53560077218 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 4) <| besselDerivativeNearFromState (980340757083771 / 4000000000000) 4 (IntervalRat.scale (283 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (37466404890 / 1000000000000) (37466404891 / 1000000000000), orderedInterval (34475162817 / 1000000000000) (34475162818 / 1000000000000)))) (orderedInterval (-21652963055 / 1000000000000) (-21652949697 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 4) <| besselDerivativeNearFromState (817305917594699 / 4000000000000) 4 (IntervalRat.scale (283 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-43991383168 / 1000000000000) (-43991383167 / 1000000000000), orderedInterval (-34250097854 / 1000000000000) (-34250097853 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 4) <| besselDerivativeNearFromState (722114564596679 / 4000000000000) 4 (IntervalRat.scale (283 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-46480840895 / 1000000000000) (-46480746246 / 1000000000000), orderedInterval (37087478044 / 1000000000000) (37087572692 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 4) <| besselDerivativeNearFromState (209296946587221 / 800000000000) 4 (IntervalRat.scale (283 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-49158806918 / 1000000000000) (-49158806591 / 1000000000000), orderedInterval (4189326867 / 1000000000000) (4189327194 / 1000000000000)))) (orderedInterval (-9939349311 / 1000000000000) (-9939334633 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate267_chunkChecks4_2 :
    compactCertificate267.chunkChecks (4 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 4) <| besselDerivativeNearFromState (578926368955087 / 4000000000000) 4 (IntervalRat.scale (283 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (55910395902 / 1000000000000) (55910395903 / 1000000000000), orderedInterval (35480930507 / 1000000000000) (35480930508 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 4) <| besselDerivativeNearFromState (490762294397207 / 4000000000000) 4 (IntervalRat.scale (283 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-58711654667 / 1000000000000) (-58711654666 / 1000000000000), orderedInterval (-41495030603 / 1000000000000) (-41495030602 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 4) <| besselDerivativeNearFromState (307096257009821 / 4000000000000) 4 (IntervalRat.scale (283 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (75725550428 / 1000000000000) (75725579459 / 1000000000000), orderedInterval (-51066789489 / 1000000000000) (-51066760458 / 1000000000000)))) (orderedInterval (-7759781840 / 1000000000000) (-7759781725 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 4) <| besselDerivativeNearFromState (165157388375907 / 4000000000000) 4 (IntervalRat.scale (283 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-117067759711 / 1000000000000) (-117067759710 / 1000000000000), orderedInterval (-39968067610 / 1000000000000) (-39968067609 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 4) <| besselDerivativeNearFromState (448434437128721 / 4000000000000) 4 (IntervalRat.scale (283 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-15298932718 / 1000000000000) (-15298932589 / 1000000000000), orderedInterval (73855715940 / 1000000000000) (73855716068 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 4) <| besselDerivativeNearFromState (612298886060017 / 4000000000000) 4 (IntervalRat.scale (283 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (5072438382 / 1000000000000) (5072438396 / 1000000000000), orderedInterval (-64306339883 / 1000000000000) (-64306339868 / 1000000000000)))) (orderedInterval (-303316252 / 1000000000000) (-303316232 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 4) <| besselDerivativeNearFromState (258903742990179 / 4000000000000) 4 (IntervalRat.scale (283 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (44386661073 / 1000000000000) (44386665072 / 1000000000000), orderedInterval (-89031199050 / 1000000000000) (-89031195050 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 4) <| besselDerivativeNearFromState (1052429341349059 / 4000000000000) 4 (IntervalRat.scale (283 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-74988938 / 1000000000000) (-74988936 / 1000000000000), orderedInterval (49189762872 / 1000000000000) (49189762874 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 4) <| besselDerivativeNearFromState (702974026168781 / 4000000000000) 4 (IntervalRat.scale (283 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (33934439579 / 1000000000000) (33934439580 / 1000000000000), orderedInterval (49611564448 / 1000000000000) (49611564449 / 1000000000000)))) (orderedInterval (-15680928849 / 1000000000000) (-15680928644 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate267_chunkChecks4 :
    compactCertificate267.chunkChecks (4 : Fin 5) 0 9 = true :=
  compactCertificate267.chunkChecks_nine_of_three (4 : Fin 5) compactCertificate267_chunkChecks4_0
    compactCertificate267_chunkChecks4_1 compactCertificate267_chunkChecks4_2

theorem compactCertificate267_chunks :
    ∀ r : Fin 5, ∀ b, compactCertificate267.chunkCheck r b = true :=
  compactCertificate267.chunkChecks_all (by
    intro r
    fin_cases r
    · exact compactCertificate267_chunkChecks0
    · exact compactCertificate267_chunkChecks1
    · exact compactCertificate267_chunkChecks2
    · exact compactCertificate267_chunkChecks3
    · exact compactCertificate267_chunkChecks4)

theorem compactCertificate267_coefficient0 :
    compactCertificate267.coefficientCheck (0 : Fin 5) = true := by
  norm_num [CompactCertificate.coefficientCheck, intervalFinSumHull,
    compactCertificate267, rationalIntervalSubset, orderedInterval, Fin.sum_univ_succ]

theorem compactCertificate267_coefficient1 :
    compactCertificate267.coefficientCheck (1 : Fin 5) = true := by
  norm_num [CompactCertificate.coefficientCheck, intervalFinSumHull,
    compactCertificate267, rationalIntervalSubset, orderedInterval, Fin.sum_univ_succ]

theorem compactCertificate267_coefficient2 :
    compactCertificate267.coefficientCheck (2 : Fin 5) = true := by
  norm_num [CompactCertificate.coefficientCheck, intervalFinSumHull,
    compactCertificate267, rationalIntervalSubset, orderedInterval, Fin.sum_univ_succ]

theorem compactCertificate267_coefficient3 :
    compactCertificate267.coefficientCheck (3 : Fin 5) = true := by
  norm_num [CompactCertificate.coefficientCheck, intervalFinSumHull,
    compactCertificate267, rationalIntervalSubset, orderedInterval, Fin.sum_univ_succ]

theorem compactCertificate267_coefficient4 :
    compactCertificate267.coefficientCheck (4 : Fin 5) = true := by
  norm_num [CompactCertificate.coefficientCheck, intervalFinSumHull,
    compactCertificate267, rationalIntervalSubset, orderedInterval, Fin.sum_univ_succ]

theorem compactCertificate267_coefficients : ∀ r : Fin 5,
    compactCertificate267.coefficientCheck r = true := by
  intro r
  fin_cases r
  · exact compactCertificate267_coefficient0
  · exact compactCertificate267_coefficient1
  · exact compactCertificate267_coefficient2
  · exact compactCertificate267_coefficient3
  · exact compactCertificate267_coefficient4

theorem compactCertificate267_lower : (1 : ℚ) ≤ compactCertificate267.output.lo := by
  norm_num [CompactCertificate.output, CompactCertificate.interval,
    CompactCertificate.coefficientTargetNat, compactCertificate267, dualConstant,
    intervalTaylorSum, intervalPow, intervalSub, intervalMaxAbs, widenInterval,
    rationalErrorInterval, orderedInterval, IntervalRat.add, IntervalRat.mul, IntervalRat.scale,
    IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4]

theorem compactCertificate267_proves {t : ℝ} (ht : t ∈ compactCertificate267.interval) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t :=
  compactCertificate267.proves compactCertificate267_states compactCertificate267_chunks
    compactCertificate267_coefficients compactCertificate267_lower ht

end Erdos232
