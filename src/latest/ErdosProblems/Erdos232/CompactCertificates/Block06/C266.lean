/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, OpenAI Codex
-/
import ErdosProblems.Erdos232.CompactBase

open LeanCert.Core
namespace Erdos232

def compactCertificate266 : CompactCertificate where
  left := 140
  right := 141
  center := 281 / 2
  grid := fun i =>
    match i.val with
    | 0 => 45
    | 1 => 33
    | 2 => 53
    | 3 => 10
    | 4 => 26
    | 5 => 70
    | 6 => 52
    | 7 => 89
    | 8 => 65
    | 9 => 100
    | 10 => 58
    | 11 => 103
    | 12 => 96
    | 13 => 68
    | 14 => 78
    | 15 => 65
    | 16 => 57
    | 17 => 83
    | 18 => 46
    | 19 => 39
    | 20 => 24
    | 21 => 13
    | 22 => 35
    | 23 => 48
    | 24 => 20
    | 25 => 83
    | _ => 56
  point := fun i =>
    match i.val with
    | 0 => 281 / 2
    | 1 => 413966656360181 / 4000000000000
    | 2 => 133868311185173 / 800000000000
    | 3 => 120794437878367 / 4000000000000
    | 4 => 324470851284499 / 4000000000000
    | 5 => 881001479806983 / 4000000000000
    | 6 => 648941702569279 / 4000000000000
    | 7 => 1111972668209467 / 4000000000000
    | 8 => 819074034559153 / 4000000000000
    | 9 => 1256670203354719 / 4000000000000
    | 10 => 725538880189351 / 4000000000000
    | 11 => 1287481474887059 / 4000000000000
    | 12 => 1202932201543871 / 4000000000000
    | 13 => 858469180188143 / 4000000000000
    | 14 => 973412553853497 / 4000000000000
    | 15 => 811529904042793 / 4000000000000
    | 16 => 717011281454653 / 4000000000000
    | 17 => 207817816222647 / 800000000000
    | 18 => 574835016524309 / 4000000000000
    | 19 => 487294009631149 / 4000000000000
    | 20 => 304925965440847 / 4000000000000
    | 21 => 163990198352049 / 4000000000000
    | 22 => 445265289163147 / 4000000000000
    | 23 => 607971685451819 / 4000000000000
    | 24 => 257074034559153 / 4000000000000
    | 25 => 1044991678159313 / 4000000000000
    | _ => 698006011849567 / 4000000000000
  state := fun i =>
    match i.val with
    | 0 => (orderedInterval (5859657357 / 1000000000000) (5859657375 / 1000000000000), orderedInterval (-67078993460 / 1000000000000) (-67078993441 / 1000000000000))
    | 1 => (orderedInterval (-44498350304 / 1000000000000) (-44498350303 / 1000000000000), orderedInterval (-64370881283 / 1000000000000) (-64370881282 / 1000000000000))
    | 2 => (orderedInterval (-61618139099 / 1000000000000) (-61618138996 / 1000000000000), orderedInterval (2948516399 / 1000000000000) (2948516502 / 1000000000000))
    | 3 => (orderedInterval (-61320760912 / 1000000000000) (-61320757422 / 1000000000000), orderedInterval (132630799411 / 1000000000000) (132630802900 / 1000000000000))
    | 4 => (orderedInterval (19346599024 / 1000000000000) (19346599025 / 1000000000000), orderedInterval (86332718479 / 1000000000000) (86332718480 / 1000000000000))
    | 5 => (orderedInterval (48478522224 / 1000000000000) (48478522225 / 1000000000000), orderedInterval (23133548829 / 1000000000000) (23133548830 / 1000000000000))
    | 6 => (orderedInterval (-21053515557 / 1000000000000) (-21053514990 / 1000000000000), orderedInterval (59063299985 / 1000000000000) (59063300553 / 1000000000000))
    | 7 => (orderedInterval (35106881717 / 1000000000000) (35106928459 / 1000000000000), orderedInterval (-32583318789 / 1000000000000) (-32583272047 / 1000000000000))
    | 8 => (orderedInterval (-54401700929 / 1000000000000) (-54401700926 / 1000000000000), orderedInterval (-12090894609 / 1000000000000) (-12090894606 / 1000000000000))
    | 9 => (orderedInterval (32080622761 / 1000000000000) (32080622762 / 1000000000000), orderedInterval (31527477952 / 1000000000000) (31527477953 / 1000000000000))
    | 10 => (orderedInterval (-2543409390 / 1000000000000) (-2543409384 / 1000000000000), orderedInterval (59195865962 / 1000000000000) (59195865969 / 1000000000000))
    | 11 => (orderedInterval (35615098117 / 1000000000000) (35615193555 / 1000000000000), orderedInterval (-26690628117 / 1000000000000) (-26690532678 / 1000000000000))
    | 12 => (orderedInterval (-3441152928 / 1000000000000) (-3441152923 / 1000000000000), orderedInterval (45886595660 / 1000000000000) (45886595665 / 1000000000000))
    | 13 => (orderedInterval (53345193228 / 1000000000000) (53345194303 / 1000000000000), orderedInterval (-11105408381 / 1000000000000) (-11105407306 / 1000000000000))
    | 14 => (orderedInterval (-40261438024 / 1000000000000) (-40261327831 / 1000000000000), orderedInterval (31627114024 / 1000000000000) (31627224217 / 1000000000000))
    | 15 => (orderedInterval (28620493792 / 1000000000000) (28620497942 / 1000000000000), orderedInterval (-48223899422 / 1000000000000) (-48223895272 / 1000000000000))
    | 16 => (orderedInterval (-49048567690 / 1000000000000) (-49048567689 / 1000000000000), orderedInterval (-33712145264 / 1000000000000) (-33712145263 / 1000000000000))
    | 17 => (orderedInterval (9592429545 / 1000000000000) (9592429584 / 1000000000000), orderedInterval (-48584640566 / 1000000000000) (-48584640528 / 1000000000000))
    | 18 => (orderedInterval (-1329701743 / 1000000000000) (-1329701737 / 1000000000000), orderedInterval (66549265761 / 1000000000000) (66549265768 / 1000000000000))
    | 19 => (orderedInterval (-6191989970 / 1000000000000) (-6191989968 / 1000000000000), orderedInterval (-71998593679 / 1000000000000) (-71998593677 / 1000000000000))
    | 20 => (orderedInterval (91285948015 / 1000000000000) (91285948070 / 1000000000000), orderedInterval (-4821957465 / 1000000000000) (-4821957410 / 1000000000000))
    | 21 => (orderedInterval (-100568803755 / 1000000000000) (-100568803754 / 1000000000000), orderedInterval (-72352230422 / 1000000000000) (-72352230421 / 1000000000000))
    | 22 => (orderedInterval (-63501615689 / 1000000000000) (-63501586049 / 1000000000000), orderedInterval (41352695300 / 1000000000000) (41352724940 / 1000000000000))
    | 23 => (orderedInterval (59347971026 / 1000000000000) (59347978426 / 1000000000000), orderedInterval (-26007739967 / 1000000000000) (-26007732567 / 1000000000000))
    | 24 => (orderedInterval (79271994758 / 1000000000000) (79272042199 / 1000000000000), orderedInterval (-60795540978 / 1000000000000) (-60795493537 / 1000000000000))
    | 25 => (orderedInterval (-47300986170 / 1000000000000) (-47300986169 / 1000000000000), orderedInterval (-14032306675 / 1000000000000) (-14032306673 / 1000000000000))
    | _ => (orderedInterval (-36216192421 / 1000000000000) (-36216178204 / 1000000000000), orderedInterval (48442271964 / 1000000000000) (48442286181 / 1000000000000))
  chunkTarget := fun r b =>
    match r.val with
    | 0 =>
      match b.val with
      | 0 => orderedInterval (-1707897903 / 1000000000000) (-1707897879 / 1000000000000)
      | 1 => orderedInterval (-2074655899 / 1000000000000) (-2074655843 / 1000000000000)
      | 2 => orderedInterval (-2397619918 / 1000000000000) (-2397618467 / 1000000000000)
      | 3 => orderedInterval (-825889016 / 1000000000000) (-825875392 / 1000000000000)
      | 4 => orderedInterval (5310343289 / 1000000000000) (5310343966 / 1000000000000)
      | 5 => orderedInterval (3382990637 / 1000000000000) (3382990701 / 1000000000000)
      | 6 => orderedInterval (3534914376 / 1000000000000) (3534914415 / 1000000000000)
      | 7 => orderedInterval (-1250695565 / 1000000000000) (-1250694308 / 1000000000000)
      | _ => orderedInterval (11123377631 / 1000000000000) (11123380625 / 1000000000000)
    | 1 =>
      match b.val with
      | 0 => orderedInterval (-26823513961 / 1000000000000) (-26823513934 / 1000000000000)
      | 1 => orderedInterval (-1067419375 / 1000000000000) (-1067419347 / 1000000000000)
      | 2 => orderedInterval (1562609780 / 1000000000000) (1562612647 / 1000000000000)
      | 3 => orderedInterval (-15556535117 / 1000000000000) (-15556503919 / 1000000000000)
      | 4 => orderedInterval (-3654499220 / 1000000000000) (-3654498071 / 1000000000000)
      | 5 => orderedInterval (-642741959 / 1000000000000) (-642741867 / 1000000000000)
      | 6 => orderedInterval (-7435495057 / 1000000000000) (-7435495021 / 1000000000000)
      | 7 => orderedInterval (1802792018 / 1000000000000) (1802793180 / 1000000000000)
      | _ => orderedInterval (-9332361024 / 1000000000000) (-9332357525 / 1000000000000)
    | 2 =>
      match b.val with
      | 0 => orderedInterval (3222292039 / 1000000000000) (3222292069 / 1000000000000)
      | 1 => orderedInterval (8210485137 / 1000000000000) (8210485166 / 1000000000000)
      | 2 => orderedInterval (7020745775 / 1000000000000) (7020751465 / 1000000000000)
      | 3 => orderedInterval (2355395948 / 1000000000000) (2355467621 / 1000000000000)
      | 4 => orderedInterval (-12640287760 / 1000000000000) (-12640285796 / 1000000000000)
      | 5 => orderedInterval (-6092980248 / 1000000000000) (-6092980114 / 1000000000000)
      | 6 => orderedInterval (-1307860433 / 1000000000000) (-1307860399 / 1000000000000)
      | 7 => orderedInterval (4247636377 / 1000000000000) (4247637486 / 1000000000000)
      | _ => orderedInterval (-23827957125 / 1000000000000) (-23827952844 / 1000000000000)
    | 3 =>
      match b.val with
      | 0 => orderedInterval (26510885083 / 1000000000000) (26510885116 / 1000000000000)
      | 1 => orderedInterval (5684497835 / 1000000000000) (5684497876 / 1000000000000)
      | 2 => orderedInterval (-6929939011 / 1000000000000) (-6929927758 / 1000000000000)
      | 3 => orderedInterval (98796270657 / 1000000000000) (98796434826 / 1000000000000)
      | 4 => orderedInterval (12788097918 / 1000000000000) (12788101270 / 1000000000000)
      | 5 => orderedInterval (5576064200 / 1000000000000) (5576064397 / 1000000000000)
      | 6 => orderedInterval (8764082303 / 1000000000000) (8764082336 / 1000000000000)
      | 7 => orderedInterval (-2120193522 / 1000000000000) (-2120192445 / 1000000000000)
      | _ => orderedInterval (10274427013 / 1000000000000) (10274432307 / 1000000000000)
    | _ =>
      match b.val with
      | 0 => orderedInterval (-5452041948 / 1000000000000) (-5452041910 / 1000000000000)
      | 1 => orderedInterval (-20812747216 / 1000000000000) (-20812747153 / 1000000000000)
      | 2 => orderedInterval (-22428664730 / 1000000000000) (-22428642393 / 1000000000000)
      | 3 => orderedInterval (-4988435851 / 1000000000000) (-4988058645 / 1000000000000)
      | 4 => orderedInterval (30419385388 / 1000000000000) (30419391141 / 1000000000000)
      | 5 => orderedInterval (11664161369 / 1000000000000) (11664161663 / 1000000000000)
      | 6 => orderedInterval (563526912 / 1000000000000) (563526944 / 1000000000000)
      | 7 => orderedInterval (-5617837104 / 1000000000000) (-5617836030 / 1000000000000)
      | _ => orderedInterval (62069385065 / 1000000000000) (62069391699 / 1000000000000)
  coefficientTarget := fun i =>
    match i.val with
    | 0 => orderedInterval (15094867632 / 1000000000000) (15094887818 / 1000000000000)
    | 1 => orderedInterval (-61147163915 / 1000000000000) (-61147123857 / 1000000000000)
    | 2 => orderedInterval (-18812530290 / 1000000000000) (-18812445346 / 1000000000000)
    | 3 => orderedInterval (159344192476 / 1000000000000) (159344377925 / 1000000000000)
    | _ => orderedInterval (45416731885 / 1000000000000) (45417145316 / 1000000000000)

theorem compactCertificate266_stateChecks0 :
    compactCertificate266.stateChecks 0 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 45 12 (281 / 2)) (orderedInterval (5859657357 / 1000000000000) (5859657375 / 1000000000000), orderedInterval (-67078993460 / 1000000000000) (-67078993441 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 33 12 (413966656360181 / 4000000000000)) (orderedInterval (-44498350304 / 1000000000000) (-44498350303 / 1000000000000), orderedInterval (-64370881283 / 1000000000000) (-64370881282 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 53 12 (133868311185173 / 800000000000)) (orderedInterval (-61618139099 / 1000000000000) (-61618138996 / 1000000000000), orderedInterval (2948516399 / 1000000000000) (2948516502 / 1000000000000))) = true
  norm_num [besselStateAtRationalPoint, besselIntervalStepZero,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, besselZeroTransition,
    besselInitial, besselGridStateAt, besselGridStateBlock00, besselGridStateBlock01,
    besselGridStateBlock02, besselGridStateBlock03, besselGridStateBlock04,
    besselGridStateBlock05, besselGridStateBlock06, besselGridStateBlock07,
    besselGridStateBlock08, besselGridStateBlock09, besselGridStateBlock10,
    besselGridStateBlock11, besselGridStateBlock12, besselGridStateBlock13,
    besselGridStateBlock14, besselGridState010, besselGridState013, besselGridState020, besselGridState024, besselGridState026, besselGridState033, besselGridState035, besselGridState039, besselGridState045, besselGridState046, besselGridState048, besselGridState052, besselGridState053, besselGridState056, besselGridState057, besselGridState058, besselGridState065, besselGridState068, besselGridState070, besselGridState078, besselGridState083, besselGridState089, besselGridState096, besselGridState100, besselGridState103, besselStateSubset, linearInterval, widenInterval,
    rationalErrorInterval, rationalIntervalSubset, orderedInterval, Finset.sum_range_succ,
    IntervalRat.add, IntervalRat.mul, IntervalRat.scale, IntervalRat.singleton]

theorem compactCertificate266_stateChecks1 :
    compactCertificate266.stateChecks 3 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 10 12 (120794437878367 / 4000000000000)) (orderedInterval (-61320760912 / 1000000000000) (-61320757422 / 1000000000000), orderedInterval (132630799411 / 1000000000000) (132630802900 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 26 12 (324470851284499 / 4000000000000)) (orderedInterval (19346599024 / 1000000000000) (19346599025 / 1000000000000), orderedInterval (86332718479 / 1000000000000) (86332718480 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 70 12 (881001479806983 / 4000000000000)) (orderedInterval (48478522224 / 1000000000000) (48478522225 / 1000000000000), orderedInterval (23133548829 / 1000000000000) (23133548830 / 1000000000000))) = true
  norm_num [besselStateAtRationalPoint, besselIntervalStepZero,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, besselZeroTransition,
    besselInitial, besselGridStateAt, besselGridStateBlock00, besselGridStateBlock01,
    besselGridStateBlock02, besselGridStateBlock03, besselGridStateBlock04,
    besselGridStateBlock05, besselGridStateBlock06, besselGridStateBlock07,
    besselGridStateBlock08, besselGridStateBlock09, besselGridStateBlock10,
    besselGridStateBlock11, besselGridStateBlock12, besselGridStateBlock13,
    besselGridStateBlock14, besselGridState010, besselGridState013, besselGridState020, besselGridState024, besselGridState026, besselGridState033, besselGridState035, besselGridState039, besselGridState045, besselGridState046, besselGridState048, besselGridState052, besselGridState053, besselGridState056, besselGridState057, besselGridState058, besselGridState065, besselGridState068, besselGridState070, besselGridState078, besselGridState083, besselGridState089, besselGridState096, besselGridState100, besselGridState103, besselStateSubset, linearInterval, widenInterval,
    rationalErrorInterval, rationalIntervalSubset, orderedInterval, Finset.sum_range_succ,
    IntervalRat.add, IntervalRat.mul, IntervalRat.scale, IntervalRat.singleton]

theorem compactCertificate266_stateChecks2 :
    compactCertificate266.stateChecks 6 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 52 12 (648941702569279 / 4000000000000)) (orderedInterval (-21053515557 / 1000000000000) (-21053514990 / 1000000000000), orderedInterval (59063299985 / 1000000000000) (59063300553 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 89 12 (1111972668209467 / 4000000000000)) (orderedInterval (35106881717 / 1000000000000) (35106928459 / 1000000000000), orderedInterval (-32583318789 / 1000000000000) (-32583272047 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 65 12 (819074034559153 / 4000000000000)) (orderedInterval (-54401700929 / 1000000000000) (-54401700926 / 1000000000000), orderedInterval (-12090894609 / 1000000000000) (-12090894606 / 1000000000000))) = true
  norm_num [besselStateAtRationalPoint, besselIntervalStepZero,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, besselZeroTransition,
    besselInitial, besselGridStateAt, besselGridStateBlock00, besselGridStateBlock01,
    besselGridStateBlock02, besselGridStateBlock03, besselGridStateBlock04,
    besselGridStateBlock05, besselGridStateBlock06, besselGridStateBlock07,
    besselGridStateBlock08, besselGridStateBlock09, besselGridStateBlock10,
    besselGridStateBlock11, besselGridStateBlock12, besselGridStateBlock13,
    besselGridStateBlock14, besselGridState010, besselGridState013, besselGridState020, besselGridState024, besselGridState026, besselGridState033, besselGridState035, besselGridState039, besselGridState045, besselGridState046, besselGridState048, besselGridState052, besselGridState053, besselGridState056, besselGridState057, besselGridState058, besselGridState065, besselGridState068, besselGridState070, besselGridState078, besselGridState083, besselGridState089, besselGridState096, besselGridState100, besselGridState103, besselStateSubset, linearInterval, widenInterval,
    rationalErrorInterval, rationalIntervalSubset, orderedInterval, Finset.sum_range_succ,
    IntervalRat.add, IntervalRat.mul, IntervalRat.scale, IntervalRat.singleton]

theorem compactCertificate266_stateChecks3 :
    compactCertificate266.stateChecks 9 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 100 12 (1256670203354719 / 4000000000000)) (orderedInterval (32080622761 / 1000000000000) (32080622762 / 1000000000000), orderedInterval (31527477952 / 1000000000000) (31527477953 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 58 12 (725538880189351 / 4000000000000)) (orderedInterval (-2543409390 / 1000000000000) (-2543409384 / 1000000000000), orderedInterval (59195865962 / 1000000000000) (59195865969 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 103 12 (1287481474887059 / 4000000000000)) (orderedInterval (35615098117 / 1000000000000) (35615193555 / 1000000000000), orderedInterval (-26690628117 / 1000000000000) (-26690532678 / 1000000000000))) = true
  norm_num [besselStateAtRationalPoint, besselIntervalStepZero,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, besselZeroTransition,
    besselInitial, besselGridStateAt, besselGridStateBlock00, besselGridStateBlock01,
    besselGridStateBlock02, besselGridStateBlock03, besselGridStateBlock04,
    besselGridStateBlock05, besselGridStateBlock06, besselGridStateBlock07,
    besselGridStateBlock08, besselGridStateBlock09, besselGridStateBlock10,
    besselGridStateBlock11, besselGridStateBlock12, besselGridStateBlock13,
    besselGridStateBlock14, besselGridState010, besselGridState013, besselGridState020, besselGridState024, besselGridState026, besselGridState033, besselGridState035, besselGridState039, besselGridState045, besselGridState046, besselGridState048, besselGridState052, besselGridState053, besselGridState056, besselGridState057, besselGridState058, besselGridState065, besselGridState068, besselGridState070, besselGridState078, besselGridState083, besselGridState089, besselGridState096, besselGridState100, besselGridState103, besselStateSubset, linearInterval, widenInterval,
    rationalErrorInterval, rationalIntervalSubset, orderedInterval, Finset.sum_range_succ,
    IntervalRat.add, IntervalRat.mul, IntervalRat.scale, IntervalRat.singleton]

theorem compactCertificate266_stateChecks4 :
    compactCertificate266.stateChecks 12 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 96 12 (1202932201543871 / 4000000000000)) (orderedInterval (-3441152928 / 1000000000000) (-3441152923 / 1000000000000), orderedInterval (45886595660 / 1000000000000) (45886595665 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 68 12 (858469180188143 / 4000000000000)) (orderedInterval (53345193228 / 1000000000000) (53345194303 / 1000000000000), orderedInterval (-11105408381 / 1000000000000) (-11105407306 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 78 12 (973412553853497 / 4000000000000)) (orderedInterval (-40261438024 / 1000000000000) (-40261327831 / 1000000000000), orderedInterval (31627114024 / 1000000000000) (31627224217 / 1000000000000))) = true
  norm_num [besselStateAtRationalPoint, besselIntervalStepZero,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, besselZeroTransition,
    besselInitial, besselGridStateAt, besselGridStateBlock00, besselGridStateBlock01,
    besselGridStateBlock02, besselGridStateBlock03, besselGridStateBlock04,
    besselGridStateBlock05, besselGridStateBlock06, besselGridStateBlock07,
    besselGridStateBlock08, besselGridStateBlock09, besselGridStateBlock10,
    besselGridStateBlock11, besselGridStateBlock12, besselGridStateBlock13,
    besselGridStateBlock14, besselGridState010, besselGridState013, besselGridState020, besselGridState024, besselGridState026, besselGridState033, besselGridState035, besselGridState039, besselGridState045, besselGridState046, besselGridState048, besselGridState052, besselGridState053, besselGridState056, besselGridState057, besselGridState058, besselGridState065, besselGridState068, besselGridState070, besselGridState078, besselGridState083, besselGridState089, besselGridState096, besselGridState100, besselGridState103, besselStateSubset, linearInterval, widenInterval,
    rationalErrorInterval, rationalIntervalSubset, orderedInterval, Finset.sum_range_succ,
    IntervalRat.add, IntervalRat.mul, IntervalRat.scale, IntervalRat.singleton]

theorem compactCertificate266_stateChecks5 :
    compactCertificate266.stateChecks 15 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 65 12 (811529904042793 / 4000000000000)) (orderedInterval (28620493792 / 1000000000000) (28620497942 / 1000000000000), orderedInterval (-48223899422 / 1000000000000) (-48223895272 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 57 12 (717011281454653 / 4000000000000)) (orderedInterval (-49048567690 / 1000000000000) (-49048567689 / 1000000000000), orderedInterval (-33712145264 / 1000000000000) (-33712145263 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 83 12 (207817816222647 / 800000000000)) (orderedInterval (9592429545 / 1000000000000) (9592429584 / 1000000000000), orderedInterval (-48584640566 / 1000000000000) (-48584640528 / 1000000000000))) = true
  norm_num [besselStateAtRationalPoint, besselIntervalStepZero,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, besselZeroTransition,
    besselInitial, besselGridStateAt, besselGridStateBlock00, besselGridStateBlock01,
    besselGridStateBlock02, besselGridStateBlock03, besselGridStateBlock04,
    besselGridStateBlock05, besselGridStateBlock06, besselGridStateBlock07,
    besselGridStateBlock08, besselGridStateBlock09, besselGridStateBlock10,
    besselGridStateBlock11, besselGridStateBlock12, besselGridStateBlock13,
    besselGridStateBlock14, besselGridState010, besselGridState013, besselGridState020, besselGridState024, besselGridState026, besselGridState033, besselGridState035, besselGridState039, besselGridState045, besselGridState046, besselGridState048, besselGridState052, besselGridState053, besselGridState056, besselGridState057, besselGridState058, besselGridState065, besselGridState068, besselGridState070, besselGridState078, besselGridState083, besselGridState089, besselGridState096, besselGridState100, besselGridState103, besselStateSubset, linearInterval, widenInterval,
    rationalErrorInterval, rationalIntervalSubset, orderedInterval, Finset.sum_range_succ,
    IntervalRat.add, IntervalRat.mul, IntervalRat.scale, IntervalRat.singleton]

theorem compactCertificate266_stateChecks6 :
    compactCertificate266.stateChecks 18 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 46 12 (574835016524309 / 4000000000000)) (orderedInterval (-1329701743 / 1000000000000) (-1329701737 / 1000000000000), orderedInterval (66549265761 / 1000000000000) (66549265768 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 39 12 (487294009631149 / 4000000000000)) (orderedInterval (-6191989970 / 1000000000000) (-6191989968 / 1000000000000), orderedInterval (-71998593679 / 1000000000000) (-71998593677 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 24 12 (304925965440847 / 4000000000000)) (orderedInterval (91285948015 / 1000000000000) (91285948070 / 1000000000000), orderedInterval (-4821957465 / 1000000000000) (-4821957410 / 1000000000000))) = true
  norm_num [besselStateAtRationalPoint, besselIntervalStepZero,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, besselZeroTransition,
    besselInitial, besselGridStateAt, besselGridStateBlock00, besselGridStateBlock01,
    besselGridStateBlock02, besselGridStateBlock03, besselGridStateBlock04,
    besselGridStateBlock05, besselGridStateBlock06, besselGridStateBlock07,
    besselGridStateBlock08, besselGridStateBlock09, besselGridStateBlock10,
    besselGridStateBlock11, besselGridStateBlock12, besselGridStateBlock13,
    besselGridStateBlock14, besselGridState010, besselGridState013, besselGridState020, besselGridState024, besselGridState026, besselGridState033, besselGridState035, besselGridState039, besselGridState045, besselGridState046, besselGridState048, besselGridState052, besselGridState053, besselGridState056, besselGridState057, besselGridState058, besselGridState065, besselGridState068, besselGridState070, besselGridState078, besselGridState083, besselGridState089, besselGridState096, besselGridState100, besselGridState103, besselStateSubset, linearInterval, widenInterval,
    rationalErrorInterval, rationalIntervalSubset, orderedInterval, Finset.sum_range_succ,
    IntervalRat.add, IntervalRat.mul, IntervalRat.scale, IntervalRat.singleton]

theorem compactCertificate266_stateChecks7 :
    compactCertificate266.stateChecks 21 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 13 12 (163990198352049 / 4000000000000)) (orderedInterval (-100568803755 / 1000000000000) (-100568803754 / 1000000000000), orderedInterval (-72352230422 / 1000000000000) (-72352230421 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 35 12 (445265289163147 / 4000000000000)) (orderedInterval (-63501615689 / 1000000000000) (-63501586049 / 1000000000000), orderedInterval (41352695300 / 1000000000000) (41352724940 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 48 12 (607971685451819 / 4000000000000)) (orderedInterval (59347971026 / 1000000000000) (59347978426 / 1000000000000), orderedInterval (-26007739967 / 1000000000000) (-26007732567 / 1000000000000))) = true
  norm_num [besselStateAtRationalPoint, besselIntervalStepZero,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, besselZeroTransition,
    besselInitial, besselGridStateAt, besselGridStateBlock00, besselGridStateBlock01,
    besselGridStateBlock02, besselGridStateBlock03, besselGridStateBlock04,
    besselGridStateBlock05, besselGridStateBlock06, besselGridStateBlock07,
    besselGridStateBlock08, besselGridStateBlock09, besselGridStateBlock10,
    besselGridStateBlock11, besselGridStateBlock12, besselGridStateBlock13,
    besselGridStateBlock14, besselGridState010, besselGridState013, besselGridState020, besselGridState024, besselGridState026, besselGridState033, besselGridState035, besselGridState039, besselGridState045, besselGridState046, besselGridState048, besselGridState052, besselGridState053, besselGridState056, besselGridState057, besselGridState058, besselGridState065, besselGridState068, besselGridState070, besselGridState078, besselGridState083, besselGridState089, besselGridState096, besselGridState100, besselGridState103, besselStateSubset, linearInterval, widenInterval,
    rationalErrorInterval, rationalIntervalSubset, orderedInterval, Finset.sum_range_succ,
    IntervalRat.add, IntervalRat.mul, IntervalRat.scale, IntervalRat.singleton]

theorem compactCertificate266_stateChecks8 :
    compactCertificate266.stateChecks 24 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 20 12 (257074034559153 / 4000000000000)) (orderedInterval (79271994758 / 1000000000000) (79272042199 / 1000000000000), orderedInterval (-60795540978 / 1000000000000) (-60795493537 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 83 12 (1044991678159313 / 4000000000000)) (orderedInterval (-47300986170 / 1000000000000) (-47300986169 / 1000000000000), orderedInterval (-14032306675 / 1000000000000) (-14032306673 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 56 12 (698006011849567 / 4000000000000)) (orderedInterval (-36216192421 / 1000000000000) (-36216178204 / 1000000000000), orderedInterval (48442271964 / 1000000000000) (48442286181 / 1000000000000))) = true
  norm_num [besselStateAtRationalPoint, besselIntervalStepZero,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, besselZeroTransition,
    besselInitial, besselGridStateAt, besselGridStateBlock00, besselGridStateBlock01,
    besselGridStateBlock02, besselGridStateBlock03, besselGridStateBlock04,
    besselGridStateBlock05, besselGridStateBlock06, besselGridStateBlock07,
    besselGridStateBlock08, besselGridStateBlock09, besselGridStateBlock10,
    besselGridStateBlock11, besselGridStateBlock12, besselGridStateBlock13,
    besselGridStateBlock14, besselGridState010, besselGridState013, besselGridState020, besselGridState024, besselGridState026, besselGridState033, besselGridState035, besselGridState039, besselGridState045, besselGridState046, besselGridState048, besselGridState052, besselGridState053, besselGridState056, besselGridState057, besselGridState058, besselGridState065, besselGridState068, besselGridState070, besselGridState078, besselGridState083, besselGridState089, besselGridState096, besselGridState100, besselGridState103, besselStateSubset, linearInterval, widenInterval,
    rationalErrorInterval, rationalIntervalSubset, orderedInterval, Finset.sum_range_succ,
    IntervalRat.add, IntervalRat.mul, IntervalRat.scale, IntervalRat.singleton]

theorem compactCertificate266_states : ∀ j,
    BesselStateValid (compactCertificate266.point j) (compactCertificate266.state j) :=
  compactCertificate266.statesValid_of_checks3 compactCertificate266_stateChecks0
    compactCertificate266_stateChecks1 compactCertificate266_stateChecks2
    compactCertificate266_stateChecks3 compactCertificate266_stateChecks4
    compactCertificate266_stateChecks5 compactCertificate266_stateChecks6
    compactCertificate266_stateChecks7 compactCertificate266_stateChecks8

theorem compactCertificate266_chunkChecks0_0 :
    compactCertificate266.chunkChecks (0 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 0) <| besselDerivativeNearFromState (281 / 2) 0 (IntervalRat.scale (281 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (5859657357 / 1000000000000) (5859657375 / 1000000000000), orderedInterval (-67078993460 / 1000000000000) (-67078993441 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 0) <| besselDerivativeNearFromState (413966656360181 / 4000000000000) 0 (IntervalRat.scale (281 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-44498350304 / 1000000000000) (-44498350303 / 1000000000000), orderedInterval (-64370881283 / 1000000000000) (-64370881282 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 0) <| besselDerivativeNearFromState (133868311185173 / 800000000000) 0 (IntervalRat.scale (281 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-61618139099 / 1000000000000) (-61618138996 / 1000000000000), orderedInterval (2948516399 / 1000000000000) (2948516502 / 1000000000000)))) (orderedInterval (-1707897903 / 1000000000000) (-1707897879 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 0) <| besselDerivativeNearFromState (120794437878367 / 4000000000000) 0 (IntervalRat.scale (281 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-61320760912 / 1000000000000) (-61320757422 / 1000000000000), orderedInterval (132630799411 / 1000000000000) (132630802900 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 0) <| besselDerivativeNearFromState (324470851284499 / 4000000000000) 0 (IntervalRat.scale (281 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (19346599024 / 1000000000000) (19346599025 / 1000000000000), orderedInterval (86332718479 / 1000000000000) (86332718480 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 0) <| besselDerivativeNearFromState (881001479806983 / 4000000000000) 0 (IntervalRat.scale (281 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (48478522224 / 1000000000000) (48478522225 / 1000000000000), orderedInterval (23133548829 / 1000000000000) (23133548830 / 1000000000000)))) (orderedInterval (-2074655899 / 1000000000000) (-2074655843 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 0) <| besselDerivativeNearFromState (648941702569279 / 4000000000000) 0 (IntervalRat.scale (281 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-21053515557 / 1000000000000) (-21053514990 / 1000000000000), orderedInterval (59063299985 / 1000000000000) (59063300553 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 0) <| besselDerivativeNearFromState (1111972668209467 / 4000000000000) 0 (IntervalRat.scale (281 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (35106881717 / 1000000000000) (35106928459 / 1000000000000), orderedInterval (-32583318789 / 1000000000000) (-32583272047 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 0) <| besselDerivativeNearFromState (819074034559153 / 4000000000000) 0 (IntervalRat.scale (281 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-54401700929 / 1000000000000) (-54401700926 / 1000000000000), orderedInterval (-12090894609 / 1000000000000) (-12090894606 / 1000000000000)))) (orderedInterval (-2397619918 / 1000000000000) (-2397618467 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate266_chunkChecks0_1 :
    compactCertificate266.chunkChecks (0 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 0) <| besselDerivativeNearFromState (1256670203354719 / 4000000000000) 0 (IntervalRat.scale (281 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (32080622761 / 1000000000000) (32080622762 / 1000000000000), orderedInterval (31527477952 / 1000000000000) (31527477953 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 0) <| besselDerivativeNearFromState (725538880189351 / 4000000000000) 0 (IntervalRat.scale (281 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-2543409390 / 1000000000000) (-2543409384 / 1000000000000), orderedInterval (59195865962 / 1000000000000) (59195865969 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 0) <| besselDerivativeNearFromState (1287481474887059 / 4000000000000) 0 (IntervalRat.scale (281 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (35615098117 / 1000000000000) (35615193555 / 1000000000000), orderedInterval (-26690628117 / 1000000000000) (-26690532678 / 1000000000000)))) (orderedInterval (-825889016 / 1000000000000) (-825875392 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 0) <| besselDerivativeNearFromState (1202932201543871 / 4000000000000) 0 (IntervalRat.scale (281 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-3441152928 / 1000000000000) (-3441152923 / 1000000000000), orderedInterval (45886595660 / 1000000000000) (45886595665 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 0) <| besselDerivativeNearFromState (858469180188143 / 4000000000000) 0 (IntervalRat.scale (281 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (53345193228 / 1000000000000) (53345194303 / 1000000000000), orderedInterval (-11105408381 / 1000000000000) (-11105407306 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 0) <| besselDerivativeNearFromState (973412553853497 / 4000000000000) 0 (IntervalRat.scale (281 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-40261438024 / 1000000000000) (-40261327831 / 1000000000000), orderedInterval (31627114024 / 1000000000000) (31627224217 / 1000000000000)))) (orderedInterval (5310343289 / 1000000000000) (5310343966 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 0) <| besselDerivativeNearFromState (811529904042793 / 4000000000000) 0 (IntervalRat.scale (281 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (28620493792 / 1000000000000) (28620497942 / 1000000000000), orderedInterval (-48223899422 / 1000000000000) (-48223895272 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 0) <| besselDerivativeNearFromState (717011281454653 / 4000000000000) 0 (IntervalRat.scale (281 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-49048567690 / 1000000000000) (-49048567689 / 1000000000000), orderedInterval (-33712145264 / 1000000000000) (-33712145263 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 0) <| besselDerivativeNearFromState (207817816222647 / 800000000000) 0 (IntervalRat.scale (281 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (9592429545 / 1000000000000) (9592429584 / 1000000000000), orderedInterval (-48584640566 / 1000000000000) (-48584640528 / 1000000000000)))) (orderedInterval (3382990637 / 1000000000000) (3382990701 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate266_chunkChecks0_2 :
    compactCertificate266.chunkChecks (0 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 0) <| besselDerivativeNearFromState (574835016524309 / 4000000000000) 0 (IntervalRat.scale (281 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-1329701743 / 1000000000000) (-1329701737 / 1000000000000), orderedInterval (66549265761 / 1000000000000) (66549265768 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 0) <| besselDerivativeNearFromState (487294009631149 / 4000000000000) 0 (IntervalRat.scale (281 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-6191989970 / 1000000000000) (-6191989968 / 1000000000000), orderedInterval (-71998593679 / 1000000000000) (-71998593677 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 0) <| besselDerivativeNearFromState (304925965440847 / 4000000000000) 0 (IntervalRat.scale (281 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (91285948015 / 1000000000000) (91285948070 / 1000000000000), orderedInterval (-4821957465 / 1000000000000) (-4821957410 / 1000000000000)))) (orderedInterval (3534914376 / 1000000000000) (3534914415 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 0) <| besselDerivativeNearFromState (163990198352049 / 4000000000000) 0 (IntervalRat.scale (281 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-100568803755 / 1000000000000) (-100568803754 / 1000000000000), orderedInterval (-72352230422 / 1000000000000) (-72352230421 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 0) <| besselDerivativeNearFromState (445265289163147 / 4000000000000) 0 (IntervalRat.scale (281 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-63501615689 / 1000000000000) (-63501586049 / 1000000000000), orderedInterval (41352695300 / 1000000000000) (41352724940 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 0) <| besselDerivativeNearFromState (607971685451819 / 4000000000000) 0 (IntervalRat.scale (281 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (59347971026 / 1000000000000) (59347978426 / 1000000000000), orderedInterval (-26007739967 / 1000000000000) (-26007732567 / 1000000000000)))) (orderedInterval (-1250695565 / 1000000000000) (-1250694308 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 0) <| besselDerivativeNearFromState (257074034559153 / 4000000000000) 0 (IntervalRat.scale (281 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (79271994758 / 1000000000000) (79272042199 / 1000000000000), orderedInterval (-60795540978 / 1000000000000) (-60795493537 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 0) <| besselDerivativeNearFromState (1044991678159313 / 4000000000000) 0 (IntervalRat.scale (281 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-47300986170 / 1000000000000) (-47300986169 / 1000000000000), orderedInterval (-14032306675 / 1000000000000) (-14032306673 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 0) <| besselDerivativeNearFromState (698006011849567 / 4000000000000) 0 (IntervalRat.scale (281 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-36216192421 / 1000000000000) (-36216178204 / 1000000000000), orderedInterval (48442271964 / 1000000000000) (48442286181 / 1000000000000)))) (orderedInterval (11123377631 / 1000000000000) (11123380625 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate266_chunkChecks0 :
    compactCertificate266.chunkChecks (0 : Fin 5) 0 9 = true :=
  compactCertificate266.chunkChecks_nine_of_three (0 : Fin 5) compactCertificate266_chunkChecks0_0
    compactCertificate266_chunkChecks0_1 compactCertificate266_chunkChecks0_2

theorem compactCertificate266_chunkChecks1_0 :
    compactCertificate266.chunkChecks (1 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 1) <| besselDerivativeNearFromState (281 / 2) 1 (IntervalRat.scale (281 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (5859657357 / 1000000000000) (5859657375 / 1000000000000), orderedInterval (-67078993460 / 1000000000000) (-67078993441 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 1) <| besselDerivativeNearFromState (413966656360181 / 4000000000000) 1 (IntervalRat.scale (281 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-44498350304 / 1000000000000) (-44498350303 / 1000000000000), orderedInterval (-64370881283 / 1000000000000) (-64370881282 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 1) <| besselDerivativeNearFromState (133868311185173 / 800000000000) 1 (IntervalRat.scale (281 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-61618139099 / 1000000000000) (-61618138996 / 1000000000000), orderedInterval (2948516399 / 1000000000000) (2948516502 / 1000000000000)))) (orderedInterval (-26823513961 / 1000000000000) (-26823513934 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 1) <| besselDerivativeNearFromState (120794437878367 / 4000000000000) 1 (IntervalRat.scale (281 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-61320760912 / 1000000000000) (-61320757422 / 1000000000000), orderedInterval (132630799411 / 1000000000000) (132630802900 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 1) <| besselDerivativeNearFromState (324470851284499 / 4000000000000) 1 (IntervalRat.scale (281 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (19346599024 / 1000000000000) (19346599025 / 1000000000000), orderedInterval (86332718479 / 1000000000000) (86332718480 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 1) <| besselDerivativeNearFromState (881001479806983 / 4000000000000) 1 (IntervalRat.scale (281 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (48478522224 / 1000000000000) (48478522225 / 1000000000000), orderedInterval (23133548829 / 1000000000000) (23133548830 / 1000000000000)))) (orderedInterval (-1067419375 / 1000000000000) (-1067419347 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 1) <| besselDerivativeNearFromState (648941702569279 / 4000000000000) 1 (IntervalRat.scale (281 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-21053515557 / 1000000000000) (-21053514990 / 1000000000000), orderedInterval (59063299985 / 1000000000000) (59063300553 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 1) <| besselDerivativeNearFromState (1111972668209467 / 4000000000000) 1 (IntervalRat.scale (281 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (35106881717 / 1000000000000) (35106928459 / 1000000000000), orderedInterval (-32583318789 / 1000000000000) (-32583272047 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 1) <| besselDerivativeNearFromState (819074034559153 / 4000000000000) 1 (IntervalRat.scale (281 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-54401700929 / 1000000000000) (-54401700926 / 1000000000000), orderedInterval (-12090894609 / 1000000000000) (-12090894606 / 1000000000000)))) (orderedInterval (1562609780 / 1000000000000) (1562612647 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate266_chunkChecks1_1 :
    compactCertificate266.chunkChecks (1 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 1) <| besselDerivativeNearFromState (1256670203354719 / 4000000000000) 1 (IntervalRat.scale (281 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (32080622761 / 1000000000000) (32080622762 / 1000000000000), orderedInterval (31527477952 / 1000000000000) (31527477953 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 1) <| besselDerivativeNearFromState (725538880189351 / 4000000000000) 1 (IntervalRat.scale (281 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-2543409390 / 1000000000000) (-2543409384 / 1000000000000), orderedInterval (59195865962 / 1000000000000) (59195865969 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 1) <| besselDerivativeNearFromState (1287481474887059 / 4000000000000) 1 (IntervalRat.scale (281 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (35615098117 / 1000000000000) (35615193555 / 1000000000000), orderedInterval (-26690628117 / 1000000000000) (-26690532678 / 1000000000000)))) (orderedInterval (-15556535117 / 1000000000000) (-15556503919 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 1) <| besselDerivativeNearFromState (1202932201543871 / 4000000000000) 1 (IntervalRat.scale (281 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-3441152928 / 1000000000000) (-3441152923 / 1000000000000), orderedInterval (45886595660 / 1000000000000) (45886595665 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 1) <| besselDerivativeNearFromState (858469180188143 / 4000000000000) 1 (IntervalRat.scale (281 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (53345193228 / 1000000000000) (53345194303 / 1000000000000), orderedInterval (-11105408381 / 1000000000000) (-11105407306 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 1) <| besselDerivativeNearFromState (973412553853497 / 4000000000000) 1 (IntervalRat.scale (281 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-40261438024 / 1000000000000) (-40261327831 / 1000000000000), orderedInterval (31627114024 / 1000000000000) (31627224217 / 1000000000000)))) (orderedInterval (-3654499220 / 1000000000000) (-3654498071 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 1) <| besselDerivativeNearFromState (811529904042793 / 4000000000000) 1 (IntervalRat.scale (281 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (28620493792 / 1000000000000) (28620497942 / 1000000000000), orderedInterval (-48223899422 / 1000000000000) (-48223895272 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 1) <| besselDerivativeNearFromState (717011281454653 / 4000000000000) 1 (IntervalRat.scale (281 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-49048567690 / 1000000000000) (-49048567689 / 1000000000000), orderedInterval (-33712145264 / 1000000000000) (-33712145263 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 1) <| besselDerivativeNearFromState (207817816222647 / 800000000000) 1 (IntervalRat.scale (281 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (9592429545 / 1000000000000) (9592429584 / 1000000000000), orderedInterval (-48584640566 / 1000000000000) (-48584640528 / 1000000000000)))) (orderedInterval (-642741959 / 1000000000000) (-642741867 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate266_chunkChecks1_2 :
    compactCertificate266.chunkChecks (1 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 1) <| besselDerivativeNearFromState (574835016524309 / 4000000000000) 1 (IntervalRat.scale (281 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-1329701743 / 1000000000000) (-1329701737 / 1000000000000), orderedInterval (66549265761 / 1000000000000) (66549265768 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 1) <| besselDerivativeNearFromState (487294009631149 / 4000000000000) 1 (IntervalRat.scale (281 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-6191989970 / 1000000000000) (-6191989968 / 1000000000000), orderedInterval (-71998593679 / 1000000000000) (-71998593677 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 1) <| besselDerivativeNearFromState (304925965440847 / 4000000000000) 1 (IntervalRat.scale (281 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (91285948015 / 1000000000000) (91285948070 / 1000000000000), orderedInterval (-4821957465 / 1000000000000) (-4821957410 / 1000000000000)))) (orderedInterval (-7435495057 / 1000000000000) (-7435495021 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 1) <| besselDerivativeNearFromState (163990198352049 / 4000000000000) 1 (IntervalRat.scale (281 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-100568803755 / 1000000000000) (-100568803754 / 1000000000000), orderedInterval (-72352230422 / 1000000000000) (-72352230421 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 1) <| besselDerivativeNearFromState (445265289163147 / 4000000000000) 1 (IntervalRat.scale (281 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-63501615689 / 1000000000000) (-63501586049 / 1000000000000), orderedInterval (41352695300 / 1000000000000) (41352724940 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 1) <| besselDerivativeNearFromState (607971685451819 / 4000000000000) 1 (IntervalRat.scale (281 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (59347971026 / 1000000000000) (59347978426 / 1000000000000), orderedInterval (-26007739967 / 1000000000000) (-26007732567 / 1000000000000)))) (orderedInterval (1802792018 / 1000000000000) (1802793180 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 1) <| besselDerivativeNearFromState (257074034559153 / 4000000000000) 1 (IntervalRat.scale (281 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (79271994758 / 1000000000000) (79272042199 / 1000000000000), orderedInterval (-60795540978 / 1000000000000) (-60795493537 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 1) <| besselDerivativeNearFromState (1044991678159313 / 4000000000000) 1 (IntervalRat.scale (281 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-47300986170 / 1000000000000) (-47300986169 / 1000000000000), orderedInterval (-14032306675 / 1000000000000) (-14032306673 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 1) <| besselDerivativeNearFromState (698006011849567 / 4000000000000) 1 (IntervalRat.scale (281 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-36216192421 / 1000000000000) (-36216178204 / 1000000000000), orderedInterval (48442271964 / 1000000000000) (48442286181 / 1000000000000)))) (orderedInterval (-9332361024 / 1000000000000) (-9332357525 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate266_chunkChecks1 :
    compactCertificate266.chunkChecks (1 : Fin 5) 0 9 = true :=
  compactCertificate266.chunkChecks_nine_of_three (1 : Fin 5) compactCertificate266_chunkChecks1_0
    compactCertificate266_chunkChecks1_1 compactCertificate266_chunkChecks1_2

theorem compactCertificate266_chunkChecks2_0 :
    compactCertificate266.chunkChecks (2 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 2) <| besselDerivativeNearFromState (281 / 2) 2 (IntervalRat.scale (281 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (5859657357 / 1000000000000) (5859657375 / 1000000000000), orderedInterval (-67078993460 / 1000000000000) (-67078993441 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 2) <| besselDerivativeNearFromState (413966656360181 / 4000000000000) 2 (IntervalRat.scale (281 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-44498350304 / 1000000000000) (-44498350303 / 1000000000000), orderedInterval (-64370881283 / 1000000000000) (-64370881282 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 2) <| besselDerivativeNearFromState (133868311185173 / 800000000000) 2 (IntervalRat.scale (281 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-61618139099 / 1000000000000) (-61618138996 / 1000000000000), orderedInterval (2948516399 / 1000000000000) (2948516502 / 1000000000000)))) (orderedInterval (3222292039 / 1000000000000) (3222292069 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 2) <| besselDerivativeNearFromState (120794437878367 / 4000000000000) 2 (IntervalRat.scale (281 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-61320760912 / 1000000000000) (-61320757422 / 1000000000000), orderedInterval (132630799411 / 1000000000000) (132630802900 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 2) <| besselDerivativeNearFromState (324470851284499 / 4000000000000) 2 (IntervalRat.scale (281 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (19346599024 / 1000000000000) (19346599025 / 1000000000000), orderedInterval (86332718479 / 1000000000000) (86332718480 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 2) <| besselDerivativeNearFromState (881001479806983 / 4000000000000) 2 (IntervalRat.scale (281 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (48478522224 / 1000000000000) (48478522225 / 1000000000000), orderedInterval (23133548829 / 1000000000000) (23133548830 / 1000000000000)))) (orderedInterval (8210485137 / 1000000000000) (8210485166 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 2) <| besselDerivativeNearFromState (648941702569279 / 4000000000000) 2 (IntervalRat.scale (281 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-21053515557 / 1000000000000) (-21053514990 / 1000000000000), orderedInterval (59063299985 / 1000000000000) (59063300553 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 2) <| besselDerivativeNearFromState (1111972668209467 / 4000000000000) 2 (IntervalRat.scale (281 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (35106881717 / 1000000000000) (35106928459 / 1000000000000), orderedInterval (-32583318789 / 1000000000000) (-32583272047 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 2) <| besselDerivativeNearFromState (819074034559153 / 4000000000000) 2 (IntervalRat.scale (281 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-54401700929 / 1000000000000) (-54401700926 / 1000000000000), orderedInterval (-12090894609 / 1000000000000) (-12090894606 / 1000000000000)))) (orderedInterval (7020745775 / 1000000000000) (7020751465 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate266_chunkChecks2_1 :
    compactCertificate266.chunkChecks (2 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 2) <| besselDerivativeNearFromState (1256670203354719 / 4000000000000) 2 (IntervalRat.scale (281 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (32080622761 / 1000000000000) (32080622762 / 1000000000000), orderedInterval (31527477952 / 1000000000000) (31527477953 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 2) <| besselDerivativeNearFromState (725538880189351 / 4000000000000) 2 (IntervalRat.scale (281 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-2543409390 / 1000000000000) (-2543409384 / 1000000000000), orderedInterval (59195865962 / 1000000000000) (59195865969 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 2) <| besselDerivativeNearFromState (1287481474887059 / 4000000000000) 2 (IntervalRat.scale (281 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (35615098117 / 1000000000000) (35615193555 / 1000000000000), orderedInterval (-26690628117 / 1000000000000) (-26690532678 / 1000000000000)))) (orderedInterval (2355395948 / 1000000000000) (2355467621 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 2) <| besselDerivativeNearFromState (1202932201543871 / 4000000000000) 2 (IntervalRat.scale (281 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-3441152928 / 1000000000000) (-3441152923 / 1000000000000), orderedInterval (45886595660 / 1000000000000) (45886595665 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 2) <| besselDerivativeNearFromState (858469180188143 / 4000000000000) 2 (IntervalRat.scale (281 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (53345193228 / 1000000000000) (53345194303 / 1000000000000), orderedInterval (-11105408381 / 1000000000000) (-11105407306 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 2) <| besselDerivativeNearFromState (973412553853497 / 4000000000000) 2 (IntervalRat.scale (281 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-40261438024 / 1000000000000) (-40261327831 / 1000000000000), orderedInterval (31627114024 / 1000000000000) (31627224217 / 1000000000000)))) (orderedInterval (-12640287760 / 1000000000000) (-12640285796 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 2) <| besselDerivativeNearFromState (811529904042793 / 4000000000000) 2 (IntervalRat.scale (281 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (28620493792 / 1000000000000) (28620497942 / 1000000000000), orderedInterval (-48223899422 / 1000000000000) (-48223895272 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 2) <| besselDerivativeNearFromState (717011281454653 / 4000000000000) 2 (IntervalRat.scale (281 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-49048567690 / 1000000000000) (-49048567689 / 1000000000000), orderedInterval (-33712145264 / 1000000000000) (-33712145263 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 2) <| besselDerivativeNearFromState (207817816222647 / 800000000000) 2 (IntervalRat.scale (281 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (9592429545 / 1000000000000) (9592429584 / 1000000000000), orderedInterval (-48584640566 / 1000000000000) (-48584640528 / 1000000000000)))) (orderedInterval (-6092980248 / 1000000000000) (-6092980114 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate266_chunkChecks2_2 :
    compactCertificate266.chunkChecks (2 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 2) <| besselDerivativeNearFromState (574835016524309 / 4000000000000) 2 (IntervalRat.scale (281 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-1329701743 / 1000000000000) (-1329701737 / 1000000000000), orderedInterval (66549265761 / 1000000000000) (66549265768 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 2) <| besselDerivativeNearFromState (487294009631149 / 4000000000000) 2 (IntervalRat.scale (281 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-6191989970 / 1000000000000) (-6191989968 / 1000000000000), orderedInterval (-71998593679 / 1000000000000) (-71998593677 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 2) <| besselDerivativeNearFromState (304925965440847 / 4000000000000) 2 (IntervalRat.scale (281 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (91285948015 / 1000000000000) (91285948070 / 1000000000000), orderedInterval (-4821957465 / 1000000000000) (-4821957410 / 1000000000000)))) (orderedInterval (-1307860433 / 1000000000000) (-1307860399 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 2) <| besselDerivativeNearFromState (163990198352049 / 4000000000000) 2 (IntervalRat.scale (281 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-100568803755 / 1000000000000) (-100568803754 / 1000000000000), orderedInterval (-72352230422 / 1000000000000) (-72352230421 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 2) <| besselDerivativeNearFromState (445265289163147 / 4000000000000) 2 (IntervalRat.scale (281 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-63501615689 / 1000000000000) (-63501586049 / 1000000000000), orderedInterval (41352695300 / 1000000000000) (41352724940 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 2) <| besselDerivativeNearFromState (607971685451819 / 4000000000000) 2 (IntervalRat.scale (281 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (59347971026 / 1000000000000) (59347978426 / 1000000000000), orderedInterval (-26007739967 / 1000000000000) (-26007732567 / 1000000000000)))) (orderedInterval (4247636377 / 1000000000000) (4247637486 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 2) <| besselDerivativeNearFromState (257074034559153 / 4000000000000) 2 (IntervalRat.scale (281 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (79271994758 / 1000000000000) (79272042199 / 1000000000000), orderedInterval (-60795540978 / 1000000000000) (-60795493537 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 2) <| besselDerivativeNearFromState (1044991678159313 / 4000000000000) 2 (IntervalRat.scale (281 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-47300986170 / 1000000000000) (-47300986169 / 1000000000000), orderedInterval (-14032306675 / 1000000000000) (-14032306673 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 2) <| besselDerivativeNearFromState (698006011849567 / 4000000000000) 2 (IntervalRat.scale (281 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-36216192421 / 1000000000000) (-36216178204 / 1000000000000), orderedInterval (48442271964 / 1000000000000) (48442286181 / 1000000000000)))) (orderedInterval (-23827957125 / 1000000000000) (-23827952844 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate266_chunkChecks2 :
    compactCertificate266.chunkChecks (2 : Fin 5) 0 9 = true :=
  compactCertificate266.chunkChecks_nine_of_three (2 : Fin 5) compactCertificate266_chunkChecks2_0
    compactCertificate266_chunkChecks2_1 compactCertificate266_chunkChecks2_2

theorem compactCertificate266_chunkChecks3_0 :
    compactCertificate266.chunkChecks (3 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 3) <| besselDerivativeNearFromState (281 / 2) 3 (IntervalRat.scale (281 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (5859657357 / 1000000000000) (5859657375 / 1000000000000), orderedInterval (-67078993460 / 1000000000000) (-67078993441 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 3) <| besselDerivativeNearFromState (413966656360181 / 4000000000000) 3 (IntervalRat.scale (281 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-44498350304 / 1000000000000) (-44498350303 / 1000000000000), orderedInterval (-64370881283 / 1000000000000) (-64370881282 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 3) <| besselDerivativeNearFromState (133868311185173 / 800000000000) 3 (IntervalRat.scale (281 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-61618139099 / 1000000000000) (-61618138996 / 1000000000000), orderedInterval (2948516399 / 1000000000000) (2948516502 / 1000000000000)))) (orderedInterval (26510885083 / 1000000000000) (26510885116 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 3) <| besselDerivativeNearFromState (120794437878367 / 4000000000000) 3 (IntervalRat.scale (281 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-61320760912 / 1000000000000) (-61320757422 / 1000000000000), orderedInterval (132630799411 / 1000000000000) (132630802900 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 3) <| besselDerivativeNearFromState (324470851284499 / 4000000000000) 3 (IntervalRat.scale (281 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (19346599024 / 1000000000000) (19346599025 / 1000000000000), orderedInterval (86332718479 / 1000000000000) (86332718480 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 3) <| besselDerivativeNearFromState (881001479806983 / 4000000000000) 3 (IntervalRat.scale (281 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (48478522224 / 1000000000000) (48478522225 / 1000000000000), orderedInterval (23133548829 / 1000000000000) (23133548830 / 1000000000000)))) (orderedInterval (5684497835 / 1000000000000) (5684497876 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 3) <| besselDerivativeNearFromState (648941702569279 / 4000000000000) 3 (IntervalRat.scale (281 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-21053515557 / 1000000000000) (-21053514990 / 1000000000000), orderedInterval (59063299985 / 1000000000000) (59063300553 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 3) <| besselDerivativeNearFromState (1111972668209467 / 4000000000000) 3 (IntervalRat.scale (281 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (35106881717 / 1000000000000) (35106928459 / 1000000000000), orderedInterval (-32583318789 / 1000000000000) (-32583272047 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 3) <| besselDerivativeNearFromState (819074034559153 / 4000000000000) 3 (IntervalRat.scale (281 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-54401700929 / 1000000000000) (-54401700926 / 1000000000000), orderedInterval (-12090894609 / 1000000000000) (-12090894606 / 1000000000000)))) (orderedInterval (-6929939011 / 1000000000000) (-6929927758 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate266_chunkChecks3_1 :
    compactCertificate266.chunkChecks (3 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 3) <| besselDerivativeNearFromState (1256670203354719 / 4000000000000) 3 (IntervalRat.scale (281 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (32080622761 / 1000000000000) (32080622762 / 1000000000000), orderedInterval (31527477952 / 1000000000000) (31527477953 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 3) <| besselDerivativeNearFromState (725538880189351 / 4000000000000) 3 (IntervalRat.scale (281 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-2543409390 / 1000000000000) (-2543409384 / 1000000000000), orderedInterval (59195865962 / 1000000000000) (59195865969 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 3) <| besselDerivativeNearFromState (1287481474887059 / 4000000000000) 3 (IntervalRat.scale (281 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (35615098117 / 1000000000000) (35615193555 / 1000000000000), orderedInterval (-26690628117 / 1000000000000) (-26690532678 / 1000000000000)))) (orderedInterval (98796270657 / 1000000000000) (98796434826 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 3) <| besselDerivativeNearFromState (1202932201543871 / 4000000000000) 3 (IntervalRat.scale (281 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-3441152928 / 1000000000000) (-3441152923 / 1000000000000), orderedInterval (45886595660 / 1000000000000) (45886595665 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 3) <| besselDerivativeNearFromState (858469180188143 / 4000000000000) 3 (IntervalRat.scale (281 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (53345193228 / 1000000000000) (53345194303 / 1000000000000), orderedInterval (-11105408381 / 1000000000000) (-11105407306 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 3) <| besselDerivativeNearFromState (973412553853497 / 4000000000000) 3 (IntervalRat.scale (281 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-40261438024 / 1000000000000) (-40261327831 / 1000000000000), orderedInterval (31627114024 / 1000000000000) (31627224217 / 1000000000000)))) (orderedInterval (12788097918 / 1000000000000) (12788101270 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 3) <| besselDerivativeNearFromState (811529904042793 / 4000000000000) 3 (IntervalRat.scale (281 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (28620493792 / 1000000000000) (28620497942 / 1000000000000), orderedInterval (-48223899422 / 1000000000000) (-48223895272 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 3) <| besselDerivativeNearFromState (717011281454653 / 4000000000000) 3 (IntervalRat.scale (281 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-49048567690 / 1000000000000) (-49048567689 / 1000000000000), orderedInterval (-33712145264 / 1000000000000) (-33712145263 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 3) <| besselDerivativeNearFromState (207817816222647 / 800000000000) 3 (IntervalRat.scale (281 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (9592429545 / 1000000000000) (9592429584 / 1000000000000), orderedInterval (-48584640566 / 1000000000000) (-48584640528 / 1000000000000)))) (orderedInterval (5576064200 / 1000000000000) (5576064397 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate266_chunkChecks3_2 :
    compactCertificate266.chunkChecks (3 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 3) <| besselDerivativeNearFromState (574835016524309 / 4000000000000) 3 (IntervalRat.scale (281 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-1329701743 / 1000000000000) (-1329701737 / 1000000000000), orderedInterval (66549265761 / 1000000000000) (66549265768 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 3) <| besselDerivativeNearFromState (487294009631149 / 4000000000000) 3 (IntervalRat.scale (281 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-6191989970 / 1000000000000) (-6191989968 / 1000000000000), orderedInterval (-71998593679 / 1000000000000) (-71998593677 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 3) <| besselDerivativeNearFromState (304925965440847 / 4000000000000) 3 (IntervalRat.scale (281 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (91285948015 / 1000000000000) (91285948070 / 1000000000000), orderedInterval (-4821957465 / 1000000000000) (-4821957410 / 1000000000000)))) (orderedInterval (8764082303 / 1000000000000) (8764082336 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 3) <| besselDerivativeNearFromState (163990198352049 / 4000000000000) 3 (IntervalRat.scale (281 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-100568803755 / 1000000000000) (-100568803754 / 1000000000000), orderedInterval (-72352230422 / 1000000000000) (-72352230421 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 3) <| besselDerivativeNearFromState (445265289163147 / 4000000000000) 3 (IntervalRat.scale (281 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-63501615689 / 1000000000000) (-63501586049 / 1000000000000), orderedInterval (41352695300 / 1000000000000) (41352724940 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 3) <| besselDerivativeNearFromState (607971685451819 / 4000000000000) 3 (IntervalRat.scale (281 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (59347971026 / 1000000000000) (59347978426 / 1000000000000), orderedInterval (-26007739967 / 1000000000000) (-26007732567 / 1000000000000)))) (orderedInterval (-2120193522 / 1000000000000) (-2120192445 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 3) <| besselDerivativeNearFromState (257074034559153 / 4000000000000) 3 (IntervalRat.scale (281 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (79271994758 / 1000000000000) (79272042199 / 1000000000000), orderedInterval (-60795540978 / 1000000000000) (-60795493537 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 3) <| besselDerivativeNearFromState (1044991678159313 / 4000000000000) 3 (IntervalRat.scale (281 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-47300986170 / 1000000000000) (-47300986169 / 1000000000000), orderedInterval (-14032306675 / 1000000000000) (-14032306673 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 3) <| besselDerivativeNearFromState (698006011849567 / 4000000000000) 3 (IntervalRat.scale (281 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-36216192421 / 1000000000000) (-36216178204 / 1000000000000), orderedInterval (48442271964 / 1000000000000) (48442286181 / 1000000000000)))) (orderedInterval (10274427013 / 1000000000000) (10274432307 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate266_chunkChecks3 :
    compactCertificate266.chunkChecks (3 : Fin 5) 0 9 = true :=
  compactCertificate266.chunkChecks_nine_of_three (3 : Fin 5) compactCertificate266_chunkChecks3_0
    compactCertificate266_chunkChecks3_1 compactCertificate266_chunkChecks3_2

theorem compactCertificate266_chunkChecks4_0 :
    compactCertificate266.chunkChecks (4 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 4) <| besselDerivativeNearFromState (281 / 2) 4 (IntervalRat.scale (281 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (5859657357 / 1000000000000) (5859657375 / 1000000000000), orderedInterval (-67078993460 / 1000000000000) (-67078993441 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 4) <| besselDerivativeNearFromState (413966656360181 / 4000000000000) 4 (IntervalRat.scale (281 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-44498350304 / 1000000000000) (-44498350303 / 1000000000000), orderedInterval (-64370881283 / 1000000000000) (-64370881282 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 4) <| besselDerivativeNearFromState (133868311185173 / 800000000000) 4 (IntervalRat.scale (281 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-61618139099 / 1000000000000) (-61618138996 / 1000000000000), orderedInterval (2948516399 / 1000000000000) (2948516502 / 1000000000000)))) (orderedInterval (-5452041948 / 1000000000000) (-5452041910 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 4) <| besselDerivativeNearFromState (120794437878367 / 4000000000000) 4 (IntervalRat.scale (281 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-61320760912 / 1000000000000) (-61320757422 / 1000000000000), orderedInterval (132630799411 / 1000000000000) (132630802900 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 4) <| besselDerivativeNearFromState (324470851284499 / 4000000000000) 4 (IntervalRat.scale (281 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (19346599024 / 1000000000000) (19346599025 / 1000000000000), orderedInterval (86332718479 / 1000000000000) (86332718480 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 4) <| besselDerivativeNearFromState (881001479806983 / 4000000000000) 4 (IntervalRat.scale (281 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (48478522224 / 1000000000000) (48478522225 / 1000000000000), orderedInterval (23133548829 / 1000000000000) (23133548830 / 1000000000000)))) (orderedInterval (-20812747216 / 1000000000000) (-20812747153 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 4) <| besselDerivativeNearFromState (648941702569279 / 4000000000000) 4 (IntervalRat.scale (281 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-21053515557 / 1000000000000) (-21053514990 / 1000000000000), orderedInterval (59063299985 / 1000000000000) (59063300553 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 4) <| besselDerivativeNearFromState (1111972668209467 / 4000000000000) 4 (IntervalRat.scale (281 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (35106881717 / 1000000000000) (35106928459 / 1000000000000), orderedInterval (-32583318789 / 1000000000000) (-32583272047 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 4) <| besselDerivativeNearFromState (819074034559153 / 4000000000000) 4 (IntervalRat.scale (281 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-54401700929 / 1000000000000) (-54401700926 / 1000000000000), orderedInterval (-12090894609 / 1000000000000) (-12090894606 / 1000000000000)))) (orderedInterval (-22428664730 / 1000000000000) (-22428642393 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate266_chunkChecks4_1 :
    compactCertificate266.chunkChecks (4 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 4) <| besselDerivativeNearFromState (1256670203354719 / 4000000000000) 4 (IntervalRat.scale (281 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (32080622761 / 1000000000000) (32080622762 / 1000000000000), orderedInterval (31527477952 / 1000000000000) (31527477953 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 4) <| besselDerivativeNearFromState (725538880189351 / 4000000000000) 4 (IntervalRat.scale (281 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-2543409390 / 1000000000000) (-2543409384 / 1000000000000), orderedInterval (59195865962 / 1000000000000) (59195865969 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 4) <| besselDerivativeNearFromState (1287481474887059 / 4000000000000) 4 (IntervalRat.scale (281 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (35615098117 / 1000000000000) (35615193555 / 1000000000000), orderedInterval (-26690628117 / 1000000000000) (-26690532678 / 1000000000000)))) (orderedInterval (-4988435851 / 1000000000000) (-4988058645 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 4) <| besselDerivativeNearFromState (1202932201543871 / 4000000000000) 4 (IntervalRat.scale (281 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-3441152928 / 1000000000000) (-3441152923 / 1000000000000), orderedInterval (45886595660 / 1000000000000) (45886595665 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 4) <| besselDerivativeNearFromState (858469180188143 / 4000000000000) 4 (IntervalRat.scale (281 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (53345193228 / 1000000000000) (53345194303 / 1000000000000), orderedInterval (-11105408381 / 1000000000000) (-11105407306 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 4) <| besselDerivativeNearFromState (973412553853497 / 4000000000000) 4 (IntervalRat.scale (281 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-40261438024 / 1000000000000) (-40261327831 / 1000000000000), orderedInterval (31627114024 / 1000000000000) (31627224217 / 1000000000000)))) (orderedInterval (30419385388 / 1000000000000) (30419391141 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 4) <| besselDerivativeNearFromState (811529904042793 / 4000000000000) 4 (IntervalRat.scale (281 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (28620493792 / 1000000000000) (28620497942 / 1000000000000), orderedInterval (-48223899422 / 1000000000000) (-48223895272 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 4) <| besselDerivativeNearFromState (717011281454653 / 4000000000000) 4 (IntervalRat.scale (281 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-49048567690 / 1000000000000) (-49048567689 / 1000000000000), orderedInterval (-33712145264 / 1000000000000) (-33712145263 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 4) <| besselDerivativeNearFromState (207817816222647 / 800000000000) 4 (IntervalRat.scale (281 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (9592429545 / 1000000000000) (9592429584 / 1000000000000), orderedInterval (-48584640566 / 1000000000000) (-48584640528 / 1000000000000)))) (orderedInterval (11664161369 / 1000000000000) (11664161663 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate266_chunkChecks4_2 :
    compactCertificate266.chunkChecks (4 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 4) <| besselDerivativeNearFromState (574835016524309 / 4000000000000) 4 (IntervalRat.scale (281 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-1329701743 / 1000000000000) (-1329701737 / 1000000000000), orderedInterval (66549265761 / 1000000000000) (66549265768 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 4) <| besselDerivativeNearFromState (487294009631149 / 4000000000000) 4 (IntervalRat.scale (281 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-6191989970 / 1000000000000) (-6191989968 / 1000000000000), orderedInterval (-71998593679 / 1000000000000) (-71998593677 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 4) <| besselDerivativeNearFromState (304925965440847 / 4000000000000) 4 (IntervalRat.scale (281 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (91285948015 / 1000000000000) (91285948070 / 1000000000000), orderedInterval (-4821957465 / 1000000000000) (-4821957410 / 1000000000000)))) (orderedInterval (563526912 / 1000000000000) (563526944 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 4) <| besselDerivativeNearFromState (163990198352049 / 4000000000000) 4 (IntervalRat.scale (281 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-100568803755 / 1000000000000) (-100568803754 / 1000000000000), orderedInterval (-72352230422 / 1000000000000) (-72352230421 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 4) <| besselDerivativeNearFromState (445265289163147 / 4000000000000) 4 (IntervalRat.scale (281 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-63501615689 / 1000000000000) (-63501586049 / 1000000000000), orderedInterval (41352695300 / 1000000000000) (41352724940 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 4) <| besselDerivativeNearFromState (607971685451819 / 4000000000000) 4 (IntervalRat.scale (281 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (59347971026 / 1000000000000) (59347978426 / 1000000000000), orderedInterval (-26007739967 / 1000000000000) (-26007732567 / 1000000000000)))) (orderedInterval (-5617837104 / 1000000000000) (-5617836030 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 4) <| besselDerivativeNearFromState (257074034559153 / 4000000000000) 4 (IntervalRat.scale (281 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (79271994758 / 1000000000000) (79272042199 / 1000000000000), orderedInterval (-60795540978 / 1000000000000) (-60795493537 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 4) <| besselDerivativeNearFromState (1044991678159313 / 4000000000000) 4 (IntervalRat.scale (281 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-47300986170 / 1000000000000) (-47300986169 / 1000000000000), orderedInterval (-14032306675 / 1000000000000) (-14032306673 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 4) <| besselDerivativeNearFromState (698006011849567 / 4000000000000) 4 (IntervalRat.scale (281 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-36216192421 / 1000000000000) (-36216178204 / 1000000000000), orderedInterval (48442271964 / 1000000000000) (48442286181 / 1000000000000)))) (orderedInterval (62069385065 / 1000000000000) (62069391699 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate266_chunkChecks4 :
    compactCertificate266.chunkChecks (4 : Fin 5) 0 9 = true :=
  compactCertificate266.chunkChecks_nine_of_three (4 : Fin 5) compactCertificate266_chunkChecks4_0
    compactCertificate266_chunkChecks4_1 compactCertificate266_chunkChecks4_2

theorem compactCertificate266_chunks :
    ∀ r : Fin 5, ∀ b, compactCertificate266.chunkCheck r b = true :=
  compactCertificate266.chunkChecks_all (by
    intro r
    fin_cases r
    · exact compactCertificate266_chunkChecks0
    · exact compactCertificate266_chunkChecks1
    · exact compactCertificate266_chunkChecks2
    · exact compactCertificate266_chunkChecks3
    · exact compactCertificate266_chunkChecks4)

theorem compactCertificate266_coefficient0 :
    compactCertificate266.coefficientCheck (0 : Fin 5) = true := by
  norm_num [CompactCertificate.coefficientCheck, intervalFinSumHull,
    compactCertificate266, rationalIntervalSubset, orderedInterval, Fin.sum_univ_succ]

theorem compactCertificate266_coefficient1 :
    compactCertificate266.coefficientCheck (1 : Fin 5) = true := by
  norm_num [CompactCertificate.coefficientCheck, intervalFinSumHull,
    compactCertificate266, rationalIntervalSubset, orderedInterval, Fin.sum_univ_succ]

theorem compactCertificate266_coefficient2 :
    compactCertificate266.coefficientCheck (2 : Fin 5) = true := by
  norm_num [CompactCertificate.coefficientCheck, intervalFinSumHull,
    compactCertificate266, rationalIntervalSubset, orderedInterval, Fin.sum_univ_succ]

theorem compactCertificate266_coefficient3 :
    compactCertificate266.coefficientCheck (3 : Fin 5) = true := by
  norm_num [CompactCertificate.coefficientCheck, intervalFinSumHull,
    compactCertificate266, rationalIntervalSubset, orderedInterval, Fin.sum_univ_succ]

theorem compactCertificate266_coefficient4 :
    compactCertificate266.coefficientCheck (4 : Fin 5) = true := by
  norm_num [CompactCertificate.coefficientCheck, intervalFinSumHull,
    compactCertificate266, rationalIntervalSubset, orderedInterval, Fin.sum_univ_succ]

theorem compactCertificate266_coefficients : ∀ r : Fin 5,
    compactCertificate266.coefficientCheck r = true := by
  intro r
  fin_cases r
  · exact compactCertificate266_coefficient0
  · exact compactCertificate266_coefficient1
  · exact compactCertificate266_coefficient2
  · exact compactCertificate266_coefficient3
  · exact compactCertificate266_coefficient4

theorem compactCertificate266_lower : (1 : ℚ) ≤ compactCertificate266.output.lo := by
  norm_num [CompactCertificate.output, CompactCertificate.interval,
    CompactCertificate.coefficientTargetNat, compactCertificate266, dualConstant,
    intervalTaylorSum, intervalPow, intervalSub, intervalMaxAbs, widenInterval,
    rationalErrorInterval, orderedInterval, IntervalRat.add, IntervalRat.mul, IntervalRat.scale,
    IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4]

theorem compactCertificate266_proves {t : ℝ} (ht : t ∈ compactCertificate266.interval) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t :=
  compactCertificate266.proves compactCertificate266_states compactCertificate266_chunks
    compactCertificate266_coefficients compactCertificate266_lower ht

end Erdos232
