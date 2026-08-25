/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, OpenAI Codex
-/
import ErdosProblems.Erdos232.CompactBase

open LeanCert.Core
namespace Erdos232

def compactCertificate257 : CompactCertificate where
  left := 132
  right := 133
  center := 265 / 2
  grid := fun i =>
    match i.val with
    | 0 => 42
    | 1 => 31
    | 2 => 50
    | 3 => 9
    | 4 => 24
    | 5 => 66
    | 6 => 49
    | 7 => 83
    | 8 => 61
    | 9 => 94
    | 10 => 54
    | 11 => 97
    | 12 => 90
    | 13 => 64
    | 14 => 73
    | 15 => 61
    | 16 => 54
    | 17 => 78
    | 18 => 43
    | 19 => 37
    | 20 => 23
    | 21 => 12
    | 22 => 33
    | 23 => 46
    | 24 => 19
    | 25 => 78
    | _ => 52
  point := fun i =>
    match i.val with
    | 0 => 265 / 2
    | 1 => 78079120238753 / 800000000000
    | 2 => 25249183248449 / 160000000000
    | 3 => 22783292553571 / 800000000000
    | 4 => 61199128534087 / 800000000000
    | 5 => 166167538895979 / 800000000000
    | 6 => 122398257068227 / 800000000000
    | 7 => 209731499697871 / 800000000000
    | 8 => 154487273422189 / 800000000000
    | 9 => 237023205614947 / 800000000000
    | 10 => 136845411565963 / 800000000000
    | 11 => 242834584231367 / 800000000000
    | 12 => 226887568262723 / 800000000000
    | 13 => 161917674555059 / 800000000000
    | 14 => 183597385602261 / 800000000000
    | 15 => 153064359125509 / 800000000000
    | 16 => 135237003263689 / 800000000000
    | 17 => 39196954661211 / 160000000000
    | 18 => 108420839415617 / 800000000000
    | 19 => 91909546300537 / 800000000000
    | 20 => 57512726577811 / 800000000000
    | 21 => 30930535632237 / 800000000000
    | 22 => 83982421087711 / 800000000000
    | 23 => 114670816117247 / 800000000000
    | 24 => 48487273422189 / 800000000000
    | 25 => 197098074528269 / 800000000000
    | _ => 131652379459171 / 800000000000
  state := fun i =>
    match i.val with
    | 0 => (orderedInterval (67438765133 / 1000000000000) (67438765134 / 1000000000000), orderedInterval (15766127353 / 1000000000000) (15766127355 / 1000000000000))
    | 1 => (orderedInterval (-67681423620 / 1000000000000) (-67681423619 / 1000000000000), orderedInterval (-43721488933 / 1000000000000) (-43721488932 / 1000000000000))
    | 2 => (orderedInterval (63406470495 / 1000000000000) (63406470515 / 1000000000000), orderedInterval (3508033469 / 1000000000000) (3508033490 / 1000000000000))
    | 3 => (orderedInterval (-124640368500 / 1000000000000) (-124640368499 / 1000000000000), orderedInterval (-80379663479 / 1000000000000) (-80379663478 / 1000000000000))
    | 4 => (orderedInterval (86773121940 / 1000000000000) (86773123684 / 1000000000000), orderedInterval (-28713654256 / 1000000000000) (-28713652513 / 1000000000000))
    | 5 => (orderedInterval (50512122466 / 1000000000000) (50512122467 / 1000000000000), orderedInterval (22538356889 / 1000000000000) (22538356890 / 1000000000000))
    | 6 => (orderedInterval (9998982851 / 1000000000000) (9998982899 / 1000000000000), orderedInterval (-63758764519 / 1000000000000) (-63758764472 / 1000000000000))
    | 7 => (orderedInterval (-39924874377 / 1000000000000) (-39924783063 / 1000000000000), orderedInterval (28960859753 / 1000000000000) (28960951068 / 1000000000000))
    | 8 => (orderedInterval (-44432104337 / 1000000000000) (-44431992088 / 1000000000000), orderedInterval (36480838569 / 1000000000000) (36480950818 / 1000000000000))
    | 9 => (orderedInterval (45576175014 / 1000000000000) (45576176400 / 1000000000000), orderedInterval (-8534246585 / 1000000000000) (-8534245199 / 1000000000000))
    | 10 => (orderedInterval (49486303600 / 1000000000000) (49486364379 / 1000000000000), orderedInterval (-35820786458 / 1000000000000) (-35820725679 / 1000000000000))
    | 11 => (orderedInterval (18098036579 / 1000000000000) (18098037093 / 1000000000000), orderedInterval (-42098306333 / 1000000000000) (-42098305819 / 1000000000000))
    | 12 => (orderedInterval (47225686673 / 1000000000000) (47225687037 / 1000000000000), orderedInterval (-3882831576 / 1000000000000) (-3882831212 / 1000000000000))
    | 13 => (orderedInterval (47837747452 / 1000000000000) (47837783267 / 1000000000000), orderedInterval (-29391792653 / 1000000000000) (-29391756838 / 1000000000000))
    | 14 => (orderedInterval (-42697616589 / 1000000000000) (-42697616588 / 1000000000000), orderedInterval (-30743534348 / 1000000000000) (-30743534347 / 1000000000000))
    | 15 => (orderedInterval (-26536536952 / 1000000000000) (-26536536951 / 1000000000000), orderedInterval (-51147349183 / 1000000000000) (-51147349182 / 1000000000000))
    | 16 => (orderedInterval (11282826630 / 1000000000000) (11282826631 / 1000000000000), orderedInterval (60287962566 / 1000000000000) (60287962567 / 1000000000000))
    | 17 => (orderedInterval (33675719573 / 1000000000000) (33675719574 / 1000000000000), orderedInterval (38201316440 / 1000000000000) (38201316441 / 1000000000000))
    | 18 => (orderedInterval (-64411301630 / 1000000000000) (-64411301629 / 1000000000000), orderedInterval (-23183674780 / 1000000000000) (-23183674779 / 1000000000000))
    | 19 => (orderedInterval (40024682902 / 1000000000000) (40024691978 / 1000000000000), orderedInterval (-62938185147 / 1000000000000) (-62938176072 / 1000000000000))
    | 20 => (orderedInterval (-38193623380 / 1000000000000) (-38193623379 / 1000000000000), orderedInterval (-85738733154 / 1000000000000) (-85738733153 / 1000000000000))
    | 21 => (orderedInterval (126344389909 / 1000000000000) (126344390168 / 1000000000000), orderedInterval (-24030005328 / 1000000000000) (-24030005070 / 1000000000000))
    | 22 => (orderedInterval (-67623219300 / 1000000000000) (-67623202138 / 1000000000000), orderedInterval (38940467531 / 1000000000000) (38940484694 / 1000000000000))
    | 23 => (orderedInterval (-25350357919 / 1000000000000) (-25350356789 / 1000000000000), orderedInterval (61722436349 / 1000000000000) (61722437478 / 1000000000000))
    | 24 => (orderedInterval (-101602724173 / 1000000000000) (-101602724010 / 1000000000000), orderedInterval (14263560931 / 1000000000000) (14263561094 / 1000000000000))
    | 25 => (orderedInterval (43535209644 / 1000000000000) (43535250819 / 1000000000000), orderedInterval (-26330565670 / 1000000000000) (-26330524495 / 1000000000000))
    | _ => (orderedInterval (56879874397 / 1000000000000) (56879882803 / 1000000000000), orderedInterval (-25335425095 / 1000000000000) (-25335416688 / 1000000000000))
  chunkTarget := fun r b =>
    match r.val with
    | 0 =>
      match b.val with
      | 0 => orderedInterval (29820470071 / 1000000000000) (29820470082 / 1000000000000)
      | 1 => orderedInterval (929609155 / 1000000000000) (929609236 / 1000000000000)
      | 2 => orderedInterval (157603747 / 1000000000000) (157609285 / 1000000000000)
      | 3 => orderedInterval (-1859065879 / 1000000000000) (-1859061003 / 1000000000000)
      | 4 => orderedInterval (3887179638 / 1000000000000) (3887183048 / 1000000000000)
      | 5 => orderedInterval (-89882414 / 1000000000000) (-89882400 / 1000000000000)
      | 6 => orderedInterval (6790080728 / 1000000000000) (6790081276 / 1000000000000)
      | 7 => orderedInterval (1144016998 / 1000000000000) (1144017496 / 1000000000000)
      | _ => orderedInterval (-14828516211 / 1000000000000) (-14828511244 / 1000000000000)
    | 1 =>
      match b.val with
      | 0 => orderedInterval (6194225979 / 1000000000000) (6194225992 / 1000000000000)
      | 1 => orderedInterval (-2929554054 / 1000000000000) (-2929553998 / 1000000000000)
      | 2 => orderedInterval (-482456757 / 1000000000000) (-482447216 / 1000000000000)
      | 3 => orderedInterval (-13745382534 / 1000000000000) (-13745375893 / 1000000000000)
      | 4 => orderedInterval (-3826049430 / 1000000000000) (-3826044216 / 1000000000000)
      | 5 => orderedInterval (-3446128854 / 1000000000000) (-3446128835 / 1000000000000)
      | 6 => orderedInterval (5365863447 / 1000000000000) (5365863924 / 1000000000000)
      | 7 => orderedInterval (-5687740716 / 1000000000000) (-5687740297 / 1000000000000)
      | _ => orderedInterval (9928697196 / 1000000000000) (9928705440 / 1000000000000)
    | 2 =>
      match b.val with
      | 0 => orderedInterval (-31712761765 / 1000000000000) (-31712761751 / 1000000000000)
      | 1 => orderedInterval (7727906114 / 1000000000000) (7727906161 / 1000000000000)
      | 2 => orderedInterval (-2536354961 / 1000000000000) (-2536338077 / 1000000000000)
      | 3 => orderedInterval (20982295627 / 1000000000000) (20982305031 / 1000000000000)
      | 4 => orderedInterval (-7268531793 / 1000000000000) (-7268523778 / 1000000000000)
      | 5 => orderedInterval (-1231566422 / 1000000000000) (-1231566394 / 1000000000000)
      | 6 => orderedInterval (-8745970738 / 1000000000000) (-8745970319 / 1000000000000)
      | 7 => orderedInterval (-2995120780 / 1000000000000) (-2995120416 / 1000000000000)
      | _ => orderedInterval (28768409972 / 1000000000000) (28768424132 / 1000000000000)
    | 3 =>
      match b.val with
      | 0 => orderedInterval (-6194400274 / 1000000000000) (-6194400257 / 1000000000000)
      | 1 => orderedInterval (6306947679 / 1000000000000) (6306947730 / 1000000000000)
      | 2 => orderedInterval (4208905027 / 1000000000000) (4208935410 / 1000000000000)
      | 3 => orderedInterval (60549277041 / 1000000000000) (60549290942 / 1000000000000)
      | 4 => orderedInterval (8465110712 / 1000000000000) (8465122980 / 1000000000000)
      | 5 => orderedInterval (2770089876 / 1000000000000) (2770089919 / 1000000000000)
      | 6 => orderedInterval (-5776740855 / 1000000000000) (-5776740487 / 1000000000000)
      | 7 => orderedInterval (6439328880 / 1000000000000) (6439329201 / 1000000000000)
      | _ => orderedInterval (-23111300483 / 1000000000000) (-23111275691 / 1000000000000)
    | _ =>
      match b.val with
      | 0 => orderedInterval (34122886059 / 1000000000000) (34122886079 / 1000000000000)
      | 1 => orderedInterval (-21425035103 / 1000000000000) (-21425035037 / 1000000000000)
      | 2 => orderedInterval (13964570572 / 1000000000000) (13964626509 / 1000000000000)
      | 3 => orderedInterval (-122324094567 / 1000000000000) (-122324072553 / 1000000000000)
      | 4 => orderedInterval (8549661546 / 1000000000000) (8549680431 / 1000000000000)
      | 5 => orderedInterval (6991120800 / 1000000000000) (6991120868 / 1000000000000)
      | 6 => orderedInterval (9970919034 / 1000000000000) (9970919359 / 1000000000000)
      | 7 => orderedInterval (3151082079 / 1000000000000) (3151082371 / 1000000000000)
      | _ => orderedInterval (-67433547752 / 1000000000000) (-67433503376 / 1000000000000)
  coefficientTarget := fun i =>
    match i.val with
    | 0 => orderedInterval (25951495833 / 1000000000000) (25951515776 / 1000000000000)
    | 1 => orderedInterval (-8628525723 / 1000000000000) (-8628495099 / 1000000000000)
    | 2 => orderedInterval (2988305254 / 1000000000000) (2988354589 / 1000000000000)
    | 3 => orderedInterval (53657217603 / 1000000000000) (53657299747 / 1000000000000)
    | _ => orderedInterval (-134432437332 / 1000000000000) (-134432295349 / 1000000000000)

theorem compactCertificate257_stateChecks0 :
    compactCertificate257.stateChecks 0 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 42 12 (265 / 2)) (orderedInterval (67438765133 / 1000000000000) (67438765134 / 1000000000000), orderedInterval (15766127353 / 1000000000000) (15766127355 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 31 12 (78079120238753 / 800000000000)) (orderedInterval (-67681423620 / 1000000000000) (-67681423619 / 1000000000000), orderedInterval (-43721488933 / 1000000000000) (-43721488932 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 50 12 (25249183248449 / 160000000000)) (orderedInterval (63406470495 / 1000000000000) (63406470515 / 1000000000000), orderedInterval (3508033469 / 1000000000000) (3508033490 / 1000000000000))) = true
  norm_num [besselStateAtRationalPoint, besselIntervalStepZero,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, besselZeroTransition,
    besselInitial, besselGridStateAt, besselGridStateBlock00, besselGridStateBlock01,
    besselGridStateBlock02, besselGridStateBlock03, besselGridStateBlock04,
    besselGridStateBlock05, besselGridStateBlock06, besselGridStateBlock07,
    besselGridStateBlock08, besselGridStateBlock09, besselGridStateBlock10,
    besselGridStateBlock11, besselGridStateBlock12, besselGridStateBlock13,
    besselGridStateBlock14, besselGridState009, besselGridState012, besselGridState019, besselGridState023, besselGridState024, besselGridState031, besselGridState033, besselGridState037, besselGridState042, besselGridState043, besselGridState046, besselGridState049, besselGridState050, besselGridState052, besselGridState054, besselGridState061, besselGridState064, besselGridState066, besselGridState073, besselGridState078, besselGridState083, besselGridState090, besselGridState094, besselGridState097, besselStateSubset, linearInterval, widenInterval,
    rationalErrorInterval, rationalIntervalSubset, orderedInterval, Finset.sum_range_succ,
    IntervalRat.add, IntervalRat.mul, IntervalRat.scale, IntervalRat.singleton]

theorem compactCertificate257_stateChecks1 :
    compactCertificate257.stateChecks 3 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 9 12 (22783292553571 / 800000000000)) (orderedInterval (-124640368500 / 1000000000000) (-124640368499 / 1000000000000), orderedInterval (-80379663479 / 1000000000000) (-80379663478 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 24 12 (61199128534087 / 800000000000)) (orderedInterval (86773121940 / 1000000000000) (86773123684 / 1000000000000), orderedInterval (-28713654256 / 1000000000000) (-28713652513 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 66 12 (166167538895979 / 800000000000)) (orderedInterval (50512122466 / 1000000000000) (50512122467 / 1000000000000), orderedInterval (22538356889 / 1000000000000) (22538356890 / 1000000000000))) = true
  norm_num [besselStateAtRationalPoint, besselIntervalStepZero,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, besselZeroTransition,
    besselInitial, besselGridStateAt, besselGridStateBlock00, besselGridStateBlock01,
    besselGridStateBlock02, besselGridStateBlock03, besselGridStateBlock04,
    besselGridStateBlock05, besselGridStateBlock06, besselGridStateBlock07,
    besselGridStateBlock08, besselGridStateBlock09, besselGridStateBlock10,
    besselGridStateBlock11, besselGridStateBlock12, besselGridStateBlock13,
    besselGridStateBlock14, besselGridState009, besselGridState012, besselGridState019, besselGridState023, besselGridState024, besselGridState031, besselGridState033, besselGridState037, besselGridState042, besselGridState043, besselGridState046, besselGridState049, besselGridState050, besselGridState052, besselGridState054, besselGridState061, besselGridState064, besselGridState066, besselGridState073, besselGridState078, besselGridState083, besselGridState090, besselGridState094, besselGridState097, besselStateSubset, linearInterval, widenInterval,
    rationalErrorInterval, rationalIntervalSubset, orderedInterval, Finset.sum_range_succ,
    IntervalRat.add, IntervalRat.mul, IntervalRat.scale, IntervalRat.singleton]

theorem compactCertificate257_stateChecks2 :
    compactCertificate257.stateChecks 6 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 49 12 (122398257068227 / 800000000000)) (orderedInterval (9998982851 / 1000000000000) (9998982899 / 1000000000000), orderedInterval (-63758764519 / 1000000000000) (-63758764472 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 83 12 (209731499697871 / 800000000000)) (orderedInterval (-39924874377 / 1000000000000) (-39924783063 / 1000000000000), orderedInterval (28960859753 / 1000000000000) (28960951068 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 61 12 (154487273422189 / 800000000000)) (orderedInterval (-44432104337 / 1000000000000) (-44431992088 / 1000000000000), orderedInterval (36480838569 / 1000000000000) (36480950818 / 1000000000000))) = true
  norm_num [besselStateAtRationalPoint, besselIntervalStepZero,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, besselZeroTransition,
    besselInitial, besselGridStateAt, besselGridStateBlock00, besselGridStateBlock01,
    besselGridStateBlock02, besselGridStateBlock03, besselGridStateBlock04,
    besselGridStateBlock05, besselGridStateBlock06, besselGridStateBlock07,
    besselGridStateBlock08, besselGridStateBlock09, besselGridStateBlock10,
    besselGridStateBlock11, besselGridStateBlock12, besselGridStateBlock13,
    besselGridStateBlock14, besselGridState009, besselGridState012, besselGridState019, besselGridState023, besselGridState024, besselGridState031, besselGridState033, besselGridState037, besselGridState042, besselGridState043, besselGridState046, besselGridState049, besselGridState050, besselGridState052, besselGridState054, besselGridState061, besselGridState064, besselGridState066, besselGridState073, besselGridState078, besselGridState083, besselGridState090, besselGridState094, besselGridState097, besselStateSubset, linearInterval, widenInterval,
    rationalErrorInterval, rationalIntervalSubset, orderedInterval, Finset.sum_range_succ,
    IntervalRat.add, IntervalRat.mul, IntervalRat.scale, IntervalRat.singleton]

theorem compactCertificate257_stateChecks3 :
    compactCertificate257.stateChecks 9 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 94 12 (237023205614947 / 800000000000)) (orderedInterval (45576175014 / 1000000000000) (45576176400 / 1000000000000), orderedInterval (-8534246585 / 1000000000000) (-8534245199 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 54 12 (136845411565963 / 800000000000)) (orderedInterval (49486303600 / 1000000000000) (49486364379 / 1000000000000), orderedInterval (-35820786458 / 1000000000000) (-35820725679 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 97 12 (242834584231367 / 800000000000)) (orderedInterval (18098036579 / 1000000000000) (18098037093 / 1000000000000), orderedInterval (-42098306333 / 1000000000000) (-42098305819 / 1000000000000))) = true
  norm_num [besselStateAtRationalPoint, besselIntervalStepZero,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, besselZeroTransition,
    besselInitial, besselGridStateAt, besselGridStateBlock00, besselGridStateBlock01,
    besselGridStateBlock02, besselGridStateBlock03, besselGridStateBlock04,
    besselGridStateBlock05, besselGridStateBlock06, besselGridStateBlock07,
    besselGridStateBlock08, besselGridStateBlock09, besselGridStateBlock10,
    besselGridStateBlock11, besselGridStateBlock12, besselGridStateBlock13,
    besselGridStateBlock14, besselGridState009, besselGridState012, besselGridState019, besselGridState023, besselGridState024, besselGridState031, besselGridState033, besselGridState037, besselGridState042, besselGridState043, besselGridState046, besselGridState049, besselGridState050, besselGridState052, besselGridState054, besselGridState061, besselGridState064, besselGridState066, besselGridState073, besselGridState078, besselGridState083, besselGridState090, besselGridState094, besselGridState097, besselStateSubset, linearInterval, widenInterval,
    rationalErrorInterval, rationalIntervalSubset, orderedInterval, Finset.sum_range_succ,
    IntervalRat.add, IntervalRat.mul, IntervalRat.scale, IntervalRat.singleton]

theorem compactCertificate257_stateChecks4 :
    compactCertificate257.stateChecks 12 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 90 12 (226887568262723 / 800000000000)) (orderedInterval (47225686673 / 1000000000000) (47225687037 / 1000000000000), orderedInterval (-3882831576 / 1000000000000) (-3882831212 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 64 12 (161917674555059 / 800000000000)) (orderedInterval (47837747452 / 1000000000000) (47837783267 / 1000000000000), orderedInterval (-29391792653 / 1000000000000) (-29391756838 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 73 12 (183597385602261 / 800000000000)) (orderedInterval (-42697616589 / 1000000000000) (-42697616588 / 1000000000000), orderedInterval (-30743534348 / 1000000000000) (-30743534347 / 1000000000000))) = true
  norm_num [besselStateAtRationalPoint, besselIntervalStepZero,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, besselZeroTransition,
    besselInitial, besselGridStateAt, besselGridStateBlock00, besselGridStateBlock01,
    besselGridStateBlock02, besselGridStateBlock03, besselGridStateBlock04,
    besselGridStateBlock05, besselGridStateBlock06, besselGridStateBlock07,
    besselGridStateBlock08, besselGridStateBlock09, besselGridStateBlock10,
    besselGridStateBlock11, besselGridStateBlock12, besselGridStateBlock13,
    besselGridStateBlock14, besselGridState009, besselGridState012, besselGridState019, besselGridState023, besselGridState024, besselGridState031, besselGridState033, besselGridState037, besselGridState042, besselGridState043, besselGridState046, besselGridState049, besselGridState050, besselGridState052, besselGridState054, besselGridState061, besselGridState064, besselGridState066, besselGridState073, besselGridState078, besselGridState083, besselGridState090, besselGridState094, besselGridState097, besselStateSubset, linearInterval, widenInterval,
    rationalErrorInterval, rationalIntervalSubset, orderedInterval, Finset.sum_range_succ,
    IntervalRat.add, IntervalRat.mul, IntervalRat.scale, IntervalRat.singleton]

theorem compactCertificate257_stateChecks5 :
    compactCertificate257.stateChecks 15 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 61 12 (153064359125509 / 800000000000)) (orderedInterval (-26536536952 / 1000000000000) (-26536536951 / 1000000000000), orderedInterval (-51147349183 / 1000000000000) (-51147349182 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 54 12 (135237003263689 / 800000000000)) (orderedInterval (11282826630 / 1000000000000) (11282826631 / 1000000000000), orderedInterval (60287962566 / 1000000000000) (60287962567 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 78 12 (39196954661211 / 160000000000)) (orderedInterval (33675719573 / 1000000000000) (33675719574 / 1000000000000), orderedInterval (38201316440 / 1000000000000) (38201316441 / 1000000000000))) = true
  norm_num [besselStateAtRationalPoint, besselIntervalStepZero,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, besselZeroTransition,
    besselInitial, besselGridStateAt, besselGridStateBlock00, besselGridStateBlock01,
    besselGridStateBlock02, besselGridStateBlock03, besselGridStateBlock04,
    besselGridStateBlock05, besselGridStateBlock06, besselGridStateBlock07,
    besselGridStateBlock08, besselGridStateBlock09, besselGridStateBlock10,
    besselGridStateBlock11, besselGridStateBlock12, besselGridStateBlock13,
    besselGridStateBlock14, besselGridState009, besselGridState012, besselGridState019, besselGridState023, besselGridState024, besselGridState031, besselGridState033, besselGridState037, besselGridState042, besselGridState043, besselGridState046, besselGridState049, besselGridState050, besselGridState052, besselGridState054, besselGridState061, besselGridState064, besselGridState066, besselGridState073, besselGridState078, besselGridState083, besselGridState090, besselGridState094, besselGridState097, besselStateSubset, linearInterval, widenInterval,
    rationalErrorInterval, rationalIntervalSubset, orderedInterval, Finset.sum_range_succ,
    IntervalRat.add, IntervalRat.mul, IntervalRat.scale, IntervalRat.singleton]

theorem compactCertificate257_stateChecks6 :
    compactCertificate257.stateChecks 18 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 43 12 (108420839415617 / 800000000000)) (orderedInterval (-64411301630 / 1000000000000) (-64411301629 / 1000000000000), orderedInterval (-23183674780 / 1000000000000) (-23183674779 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 37 12 (91909546300537 / 800000000000)) (orderedInterval (40024682902 / 1000000000000) (40024691978 / 1000000000000), orderedInterval (-62938185147 / 1000000000000) (-62938176072 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 23 12 (57512726577811 / 800000000000)) (orderedInterval (-38193623380 / 1000000000000) (-38193623379 / 1000000000000), orderedInterval (-85738733154 / 1000000000000) (-85738733153 / 1000000000000))) = true
  norm_num [besselStateAtRationalPoint, besselIntervalStepZero,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, besselZeroTransition,
    besselInitial, besselGridStateAt, besselGridStateBlock00, besselGridStateBlock01,
    besselGridStateBlock02, besselGridStateBlock03, besselGridStateBlock04,
    besselGridStateBlock05, besselGridStateBlock06, besselGridStateBlock07,
    besselGridStateBlock08, besselGridStateBlock09, besselGridStateBlock10,
    besselGridStateBlock11, besselGridStateBlock12, besselGridStateBlock13,
    besselGridStateBlock14, besselGridState009, besselGridState012, besselGridState019, besselGridState023, besselGridState024, besselGridState031, besselGridState033, besselGridState037, besselGridState042, besselGridState043, besselGridState046, besselGridState049, besselGridState050, besselGridState052, besselGridState054, besselGridState061, besselGridState064, besselGridState066, besselGridState073, besselGridState078, besselGridState083, besselGridState090, besselGridState094, besselGridState097, besselStateSubset, linearInterval, widenInterval,
    rationalErrorInterval, rationalIntervalSubset, orderedInterval, Finset.sum_range_succ,
    IntervalRat.add, IntervalRat.mul, IntervalRat.scale, IntervalRat.singleton]

theorem compactCertificate257_stateChecks7 :
    compactCertificate257.stateChecks 21 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 12 12 (30930535632237 / 800000000000)) (orderedInterval (126344389909 / 1000000000000) (126344390168 / 1000000000000), orderedInterval (-24030005328 / 1000000000000) (-24030005070 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 33 12 (83982421087711 / 800000000000)) (orderedInterval (-67623219300 / 1000000000000) (-67623202138 / 1000000000000), orderedInterval (38940467531 / 1000000000000) (38940484694 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 46 12 (114670816117247 / 800000000000)) (orderedInterval (-25350357919 / 1000000000000) (-25350356789 / 1000000000000), orderedInterval (61722436349 / 1000000000000) (61722437478 / 1000000000000))) = true
  norm_num [besselStateAtRationalPoint, besselIntervalStepZero,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, besselZeroTransition,
    besselInitial, besselGridStateAt, besselGridStateBlock00, besselGridStateBlock01,
    besselGridStateBlock02, besselGridStateBlock03, besselGridStateBlock04,
    besselGridStateBlock05, besselGridStateBlock06, besselGridStateBlock07,
    besselGridStateBlock08, besselGridStateBlock09, besselGridStateBlock10,
    besselGridStateBlock11, besselGridStateBlock12, besselGridStateBlock13,
    besselGridStateBlock14, besselGridState009, besselGridState012, besselGridState019, besselGridState023, besselGridState024, besselGridState031, besselGridState033, besselGridState037, besselGridState042, besselGridState043, besselGridState046, besselGridState049, besselGridState050, besselGridState052, besselGridState054, besselGridState061, besselGridState064, besselGridState066, besselGridState073, besselGridState078, besselGridState083, besselGridState090, besselGridState094, besselGridState097, besselStateSubset, linearInterval, widenInterval,
    rationalErrorInterval, rationalIntervalSubset, orderedInterval, Finset.sum_range_succ,
    IntervalRat.add, IntervalRat.mul, IntervalRat.scale, IntervalRat.singleton]

theorem compactCertificate257_stateChecks8 :
    compactCertificate257.stateChecks 24 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 19 12 (48487273422189 / 800000000000)) (orderedInterval (-101602724173 / 1000000000000) (-101602724010 / 1000000000000), orderedInterval (14263560931 / 1000000000000) (14263561094 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 78 12 (197098074528269 / 800000000000)) (orderedInterval (43535209644 / 1000000000000) (43535250819 / 1000000000000), orderedInterval (-26330565670 / 1000000000000) (-26330524495 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 52 12 (131652379459171 / 800000000000)) (orderedInterval (56879874397 / 1000000000000) (56879882803 / 1000000000000), orderedInterval (-25335425095 / 1000000000000) (-25335416688 / 1000000000000))) = true
  norm_num [besselStateAtRationalPoint, besselIntervalStepZero,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, besselZeroTransition,
    besselInitial, besselGridStateAt, besselGridStateBlock00, besselGridStateBlock01,
    besselGridStateBlock02, besselGridStateBlock03, besselGridStateBlock04,
    besselGridStateBlock05, besselGridStateBlock06, besselGridStateBlock07,
    besselGridStateBlock08, besselGridStateBlock09, besselGridStateBlock10,
    besselGridStateBlock11, besselGridStateBlock12, besselGridStateBlock13,
    besselGridStateBlock14, besselGridState009, besselGridState012, besselGridState019, besselGridState023, besselGridState024, besselGridState031, besselGridState033, besselGridState037, besselGridState042, besselGridState043, besselGridState046, besselGridState049, besselGridState050, besselGridState052, besselGridState054, besselGridState061, besselGridState064, besselGridState066, besselGridState073, besselGridState078, besselGridState083, besselGridState090, besselGridState094, besselGridState097, besselStateSubset, linearInterval, widenInterval,
    rationalErrorInterval, rationalIntervalSubset, orderedInterval, Finset.sum_range_succ,
    IntervalRat.add, IntervalRat.mul, IntervalRat.scale, IntervalRat.singleton]

theorem compactCertificate257_states : ∀ j,
    BesselStateValid (compactCertificate257.point j) (compactCertificate257.state j) :=
  compactCertificate257.statesValid_of_checks3 compactCertificate257_stateChecks0
    compactCertificate257_stateChecks1 compactCertificate257_stateChecks2
    compactCertificate257_stateChecks3 compactCertificate257_stateChecks4
    compactCertificate257_stateChecks5 compactCertificate257_stateChecks6
    compactCertificate257_stateChecks7 compactCertificate257_stateChecks8

theorem compactCertificate257_chunkChecks0_0 :
    compactCertificate257.chunkChecks (0 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 0) <| besselDerivativeNearFromState (265 / 2) 0 (IntervalRat.scale (265 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (67438765133 / 1000000000000) (67438765134 / 1000000000000), orderedInterval (15766127353 / 1000000000000) (15766127355 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 0) <| besselDerivativeNearFromState (78079120238753 / 800000000000) 0 (IntervalRat.scale (265 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-67681423620 / 1000000000000) (-67681423619 / 1000000000000), orderedInterval (-43721488933 / 1000000000000) (-43721488932 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 0) <| besselDerivativeNearFromState (25249183248449 / 160000000000) 0 (IntervalRat.scale (265 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (63406470495 / 1000000000000) (63406470515 / 1000000000000), orderedInterval (3508033469 / 1000000000000) (3508033490 / 1000000000000)))) (orderedInterval (29820470071 / 1000000000000) (29820470082 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 0) <| besselDerivativeNearFromState (22783292553571 / 800000000000) 0 (IntervalRat.scale (265 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-124640368500 / 1000000000000) (-124640368499 / 1000000000000), orderedInterval (-80379663479 / 1000000000000) (-80379663478 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 0) <| besselDerivativeNearFromState (61199128534087 / 800000000000) 0 (IntervalRat.scale (265 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (86773121940 / 1000000000000) (86773123684 / 1000000000000), orderedInterval (-28713654256 / 1000000000000) (-28713652513 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 0) <| besselDerivativeNearFromState (166167538895979 / 800000000000) 0 (IntervalRat.scale (265 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (50512122466 / 1000000000000) (50512122467 / 1000000000000), orderedInterval (22538356889 / 1000000000000) (22538356890 / 1000000000000)))) (orderedInterval (929609155 / 1000000000000) (929609236 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 0) <| besselDerivativeNearFromState (122398257068227 / 800000000000) 0 (IntervalRat.scale (265 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (9998982851 / 1000000000000) (9998982899 / 1000000000000), orderedInterval (-63758764519 / 1000000000000) (-63758764472 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 0) <| besselDerivativeNearFromState (209731499697871 / 800000000000) 0 (IntervalRat.scale (265 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-39924874377 / 1000000000000) (-39924783063 / 1000000000000), orderedInterval (28960859753 / 1000000000000) (28960951068 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 0) <| besselDerivativeNearFromState (154487273422189 / 800000000000) 0 (IntervalRat.scale (265 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-44432104337 / 1000000000000) (-44431992088 / 1000000000000), orderedInterval (36480838569 / 1000000000000) (36480950818 / 1000000000000)))) (orderedInterval (157603747 / 1000000000000) (157609285 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate257_chunkChecks0_1 :
    compactCertificate257.chunkChecks (0 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 0) <| besselDerivativeNearFromState (237023205614947 / 800000000000) 0 (IntervalRat.scale (265 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (45576175014 / 1000000000000) (45576176400 / 1000000000000), orderedInterval (-8534246585 / 1000000000000) (-8534245199 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 0) <| besselDerivativeNearFromState (136845411565963 / 800000000000) 0 (IntervalRat.scale (265 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (49486303600 / 1000000000000) (49486364379 / 1000000000000), orderedInterval (-35820786458 / 1000000000000) (-35820725679 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 0) <| besselDerivativeNearFromState (242834584231367 / 800000000000) 0 (IntervalRat.scale (265 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (18098036579 / 1000000000000) (18098037093 / 1000000000000), orderedInterval (-42098306333 / 1000000000000) (-42098305819 / 1000000000000)))) (orderedInterval (-1859065879 / 1000000000000) (-1859061003 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 0) <| besselDerivativeNearFromState (226887568262723 / 800000000000) 0 (IntervalRat.scale (265 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (47225686673 / 1000000000000) (47225687037 / 1000000000000), orderedInterval (-3882831576 / 1000000000000) (-3882831212 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 0) <| besselDerivativeNearFromState (161917674555059 / 800000000000) 0 (IntervalRat.scale (265 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (47837747452 / 1000000000000) (47837783267 / 1000000000000), orderedInterval (-29391792653 / 1000000000000) (-29391756838 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 0) <| besselDerivativeNearFromState (183597385602261 / 800000000000) 0 (IntervalRat.scale (265 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-42697616589 / 1000000000000) (-42697616588 / 1000000000000), orderedInterval (-30743534348 / 1000000000000) (-30743534347 / 1000000000000)))) (orderedInterval (3887179638 / 1000000000000) (3887183048 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 0) <| besselDerivativeNearFromState (153064359125509 / 800000000000) 0 (IntervalRat.scale (265 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-26536536952 / 1000000000000) (-26536536951 / 1000000000000), orderedInterval (-51147349183 / 1000000000000) (-51147349182 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 0) <| besselDerivativeNearFromState (135237003263689 / 800000000000) 0 (IntervalRat.scale (265 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (11282826630 / 1000000000000) (11282826631 / 1000000000000), orderedInterval (60287962566 / 1000000000000) (60287962567 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 0) <| besselDerivativeNearFromState (39196954661211 / 160000000000) 0 (IntervalRat.scale (265 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (33675719573 / 1000000000000) (33675719574 / 1000000000000), orderedInterval (38201316440 / 1000000000000) (38201316441 / 1000000000000)))) (orderedInterval (-89882414 / 1000000000000) (-89882400 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate257_chunkChecks0_2 :
    compactCertificate257.chunkChecks (0 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 0) <| besselDerivativeNearFromState (108420839415617 / 800000000000) 0 (IntervalRat.scale (265 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-64411301630 / 1000000000000) (-64411301629 / 1000000000000), orderedInterval (-23183674780 / 1000000000000) (-23183674779 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 0) <| besselDerivativeNearFromState (91909546300537 / 800000000000) 0 (IntervalRat.scale (265 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (40024682902 / 1000000000000) (40024691978 / 1000000000000), orderedInterval (-62938185147 / 1000000000000) (-62938176072 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 0) <| besselDerivativeNearFromState (57512726577811 / 800000000000) 0 (IntervalRat.scale (265 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-38193623380 / 1000000000000) (-38193623379 / 1000000000000), orderedInterval (-85738733154 / 1000000000000) (-85738733153 / 1000000000000)))) (orderedInterval (6790080728 / 1000000000000) (6790081276 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 0) <| besselDerivativeNearFromState (30930535632237 / 800000000000) 0 (IntervalRat.scale (265 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (126344389909 / 1000000000000) (126344390168 / 1000000000000), orderedInterval (-24030005328 / 1000000000000) (-24030005070 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 0) <| besselDerivativeNearFromState (83982421087711 / 800000000000) 0 (IntervalRat.scale (265 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-67623219300 / 1000000000000) (-67623202138 / 1000000000000), orderedInterval (38940467531 / 1000000000000) (38940484694 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 0) <| besselDerivativeNearFromState (114670816117247 / 800000000000) 0 (IntervalRat.scale (265 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-25350357919 / 1000000000000) (-25350356789 / 1000000000000), orderedInterval (61722436349 / 1000000000000) (61722437478 / 1000000000000)))) (orderedInterval (1144016998 / 1000000000000) (1144017496 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 0) <| besselDerivativeNearFromState (48487273422189 / 800000000000) 0 (IntervalRat.scale (265 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-101602724173 / 1000000000000) (-101602724010 / 1000000000000), orderedInterval (14263560931 / 1000000000000) (14263561094 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 0) <| besselDerivativeNearFromState (197098074528269 / 800000000000) 0 (IntervalRat.scale (265 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (43535209644 / 1000000000000) (43535250819 / 1000000000000), orderedInterval (-26330565670 / 1000000000000) (-26330524495 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 0) <| besselDerivativeNearFromState (131652379459171 / 800000000000) 0 (IntervalRat.scale (265 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (56879874397 / 1000000000000) (56879882803 / 1000000000000), orderedInterval (-25335425095 / 1000000000000) (-25335416688 / 1000000000000)))) (orderedInterval (-14828516211 / 1000000000000) (-14828511244 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate257_chunkChecks0 :
    compactCertificate257.chunkChecks (0 : Fin 5) 0 9 = true :=
  compactCertificate257.chunkChecks_nine_of_three (0 : Fin 5) compactCertificate257_chunkChecks0_0
    compactCertificate257_chunkChecks0_1 compactCertificate257_chunkChecks0_2

theorem compactCertificate257_chunkChecks1_0 :
    compactCertificate257.chunkChecks (1 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 1) <| besselDerivativeNearFromState (265 / 2) 1 (IntervalRat.scale (265 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (67438765133 / 1000000000000) (67438765134 / 1000000000000), orderedInterval (15766127353 / 1000000000000) (15766127355 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 1) <| besselDerivativeNearFromState (78079120238753 / 800000000000) 1 (IntervalRat.scale (265 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-67681423620 / 1000000000000) (-67681423619 / 1000000000000), orderedInterval (-43721488933 / 1000000000000) (-43721488932 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 1) <| besselDerivativeNearFromState (25249183248449 / 160000000000) 1 (IntervalRat.scale (265 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (63406470495 / 1000000000000) (63406470515 / 1000000000000), orderedInterval (3508033469 / 1000000000000) (3508033490 / 1000000000000)))) (orderedInterval (6194225979 / 1000000000000) (6194225992 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 1) <| besselDerivativeNearFromState (22783292553571 / 800000000000) 1 (IntervalRat.scale (265 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-124640368500 / 1000000000000) (-124640368499 / 1000000000000), orderedInterval (-80379663479 / 1000000000000) (-80379663478 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 1) <| besselDerivativeNearFromState (61199128534087 / 800000000000) 1 (IntervalRat.scale (265 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (86773121940 / 1000000000000) (86773123684 / 1000000000000), orderedInterval (-28713654256 / 1000000000000) (-28713652513 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 1) <| besselDerivativeNearFromState (166167538895979 / 800000000000) 1 (IntervalRat.scale (265 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (50512122466 / 1000000000000) (50512122467 / 1000000000000), orderedInterval (22538356889 / 1000000000000) (22538356890 / 1000000000000)))) (orderedInterval (-2929554054 / 1000000000000) (-2929553998 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 1) <| besselDerivativeNearFromState (122398257068227 / 800000000000) 1 (IntervalRat.scale (265 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (9998982851 / 1000000000000) (9998982899 / 1000000000000), orderedInterval (-63758764519 / 1000000000000) (-63758764472 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 1) <| besselDerivativeNearFromState (209731499697871 / 800000000000) 1 (IntervalRat.scale (265 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-39924874377 / 1000000000000) (-39924783063 / 1000000000000), orderedInterval (28960859753 / 1000000000000) (28960951068 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 1) <| besselDerivativeNearFromState (154487273422189 / 800000000000) 1 (IntervalRat.scale (265 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-44432104337 / 1000000000000) (-44431992088 / 1000000000000), orderedInterval (36480838569 / 1000000000000) (36480950818 / 1000000000000)))) (orderedInterval (-482456757 / 1000000000000) (-482447216 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate257_chunkChecks1_1 :
    compactCertificate257.chunkChecks (1 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 1) <| besselDerivativeNearFromState (237023205614947 / 800000000000) 1 (IntervalRat.scale (265 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (45576175014 / 1000000000000) (45576176400 / 1000000000000), orderedInterval (-8534246585 / 1000000000000) (-8534245199 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 1) <| besselDerivativeNearFromState (136845411565963 / 800000000000) 1 (IntervalRat.scale (265 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (49486303600 / 1000000000000) (49486364379 / 1000000000000), orderedInterval (-35820786458 / 1000000000000) (-35820725679 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 1) <| besselDerivativeNearFromState (242834584231367 / 800000000000) 1 (IntervalRat.scale (265 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (18098036579 / 1000000000000) (18098037093 / 1000000000000), orderedInterval (-42098306333 / 1000000000000) (-42098305819 / 1000000000000)))) (orderedInterval (-13745382534 / 1000000000000) (-13745375893 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 1) <| besselDerivativeNearFromState (226887568262723 / 800000000000) 1 (IntervalRat.scale (265 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (47225686673 / 1000000000000) (47225687037 / 1000000000000), orderedInterval (-3882831576 / 1000000000000) (-3882831212 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 1) <| besselDerivativeNearFromState (161917674555059 / 800000000000) 1 (IntervalRat.scale (265 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (47837747452 / 1000000000000) (47837783267 / 1000000000000), orderedInterval (-29391792653 / 1000000000000) (-29391756838 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 1) <| besselDerivativeNearFromState (183597385602261 / 800000000000) 1 (IntervalRat.scale (265 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-42697616589 / 1000000000000) (-42697616588 / 1000000000000), orderedInterval (-30743534348 / 1000000000000) (-30743534347 / 1000000000000)))) (orderedInterval (-3826049430 / 1000000000000) (-3826044216 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 1) <| besselDerivativeNearFromState (153064359125509 / 800000000000) 1 (IntervalRat.scale (265 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-26536536952 / 1000000000000) (-26536536951 / 1000000000000), orderedInterval (-51147349183 / 1000000000000) (-51147349182 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 1) <| besselDerivativeNearFromState (135237003263689 / 800000000000) 1 (IntervalRat.scale (265 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (11282826630 / 1000000000000) (11282826631 / 1000000000000), orderedInterval (60287962566 / 1000000000000) (60287962567 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 1) <| besselDerivativeNearFromState (39196954661211 / 160000000000) 1 (IntervalRat.scale (265 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (33675719573 / 1000000000000) (33675719574 / 1000000000000), orderedInterval (38201316440 / 1000000000000) (38201316441 / 1000000000000)))) (orderedInterval (-3446128854 / 1000000000000) (-3446128835 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate257_chunkChecks1_2 :
    compactCertificate257.chunkChecks (1 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 1) <| besselDerivativeNearFromState (108420839415617 / 800000000000) 1 (IntervalRat.scale (265 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-64411301630 / 1000000000000) (-64411301629 / 1000000000000), orderedInterval (-23183674780 / 1000000000000) (-23183674779 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 1) <| besselDerivativeNearFromState (91909546300537 / 800000000000) 1 (IntervalRat.scale (265 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (40024682902 / 1000000000000) (40024691978 / 1000000000000), orderedInterval (-62938185147 / 1000000000000) (-62938176072 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 1) <| besselDerivativeNearFromState (57512726577811 / 800000000000) 1 (IntervalRat.scale (265 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-38193623380 / 1000000000000) (-38193623379 / 1000000000000), orderedInterval (-85738733154 / 1000000000000) (-85738733153 / 1000000000000)))) (orderedInterval (5365863447 / 1000000000000) (5365863924 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 1) <| besselDerivativeNearFromState (30930535632237 / 800000000000) 1 (IntervalRat.scale (265 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (126344389909 / 1000000000000) (126344390168 / 1000000000000), orderedInterval (-24030005328 / 1000000000000) (-24030005070 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 1) <| besselDerivativeNearFromState (83982421087711 / 800000000000) 1 (IntervalRat.scale (265 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-67623219300 / 1000000000000) (-67623202138 / 1000000000000), orderedInterval (38940467531 / 1000000000000) (38940484694 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 1) <| besselDerivativeNearFromState (114670816117247 / 800000000000) 1 (IntervalRat.scale (265 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-25350357919 / 1000000000000) (-25350356789 / 1000000000000), orderedInterval (61722436349 / 1000000000000) (61722437478 / 1000000000000)))) (orderedInterval (-5687740716 / 1000000000000) (-5687740297 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 1) <| besselDerivativeNearFromState (48487273422189 / 800000000000) 1 (IntervalRat.scale (265 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-101602724173 / 1000000000000) (-101602724010 / 1000000000000), orderedInterval (14263560931 / 1000000000000) (14263561094 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 1) <| besselDerivativeNearFromState (197098074528269 / 800000000000) 1 (IntervalRat.scale (265 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (43535209644 / 1000000000000) (43535250819 / 1000000000000), orderedInterval (-26330565670 / 1000000000000) (-26330524495 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 1) <| besselDerivativeNearFromState (131652379459171 / 800000000000) 1 (IntervalRat.scale (265 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (56879874397 / 1000000000000) (56879882803 / 1000000000000), orderedInterval (-25335425095 / 1000000000000) (-25335416688 / 1000000000000)))) (orderedInterval (9928697196 / 1000000000000) (9928705440 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate257_chunkChecks1 :
    compactCertificate257.chunkChecks (1 : Fin 5) 0 9 = true :=
  compactCertificate257.chunkChecks_nine_of_three (1 : Fin 5) compactCertificate257_chunkChecks1_0
    compactCertificate257_chunkChecks1_1 compactCertificate257_chunkChecks1_2

theorem compactCertificate257_chunkChecks2_0 :
    compactCertificate257.chunkChecks (2 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 2) <| besselDerivativeNearFromState (265 / 2) 2 (IntervalRat.scale (265 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (67438765133 / 1000000000000) (67438765134 / 1000000000000), orderedInterval (15766127353 / 1000000000000) (15766127355 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 2) <| besselDerivativeNearFromState (78079120238753 / 800000000000) 2 (IntervalRat.scale (265 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-67681423620 / 1000000000000) (-67681423619 / 1000000000000), orderedInterval (-43721488933 / 1000000000000) (-43721488932 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 2) <| besselDerivativeNearFromState (25249183248449 / 160000000000) 2 (IntervalRat.scale (265 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (63406470495 / 1000000000000) (63406470515 / 1000000000000), orderedInterval (3508033469 / 1000000000000) (3508033490 / 1000000000000)))) (orderedInterval (-31712761765 / 1000000000000) (-31712761751 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 2) <| besselDerivativeNearFromState (22783292553571 / 800000000000) 2 (IntervalRat.scale (265 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-124640368500 / 1000000000000) (-124640368499 / 1000000000000), orderedInterval (-80379663479 / 1000000000000) (-80379663478 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 2) <| besselDerivativeNearFromState (61199128534087 / 800000000000) 2 (IntervalRat.scale (265 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (86773121940 / 1000000000000) (86773123684 / 1000000000000), orderedInterval (-28713654256 / 1000000000000) (-28713652513 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 2) <| besselDerivativeNearFromState (166167538895979 / 800000000000) 2 (IntervalRat.scale (265 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (50512122466 / 1000000000000) (50512122467 / 1000000000000), orderedInterval (22538356889 / 1000000000000) (22538356890 / 1000000000000)))) (orderedInterval (7727906114 / 1000000000000) (7727906161 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 2) <| besselDerivativeNearFromState (122398257068227 / 800000000000) 2 (IntervalRat.scale (265 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (9998982851 / 1000000000000) (9998982899 / 1000000000000), orderedInterval (-63758764519 / 1000000000000) (-63758764472 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 2) <| besselDerivativeNearFromState (209731499697871 / 800000000000) 2 (IntervalRat.scale (265 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-39924874377 / 1000000000000) (-39924783063 / 1000000000000), orderedInterval (28960859753 / 1000000000000) (28960951068 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 2) <| besselDerivativeNearFromState (154487273422189 / 800000000000) 2 (IntervalRat.scale (265 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-44432104337 / 1000000000000) (-44431992088 / 1000000000000), orderedInterval (36480838569 / 1000000000000) (36480950818 / 1000000000000)))) (orderedInterval (-2536354961 / 1000000000000) (-2536338077 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate257_chunkChecks2_1 :
    compactCertificate257.chunkChecks (2 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 2) <| besselDerivativeNearFromState (237023205614947 / 800000000000) 2 (IntervalRat.scale (265 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (45576175014 / 1000000000000) (45576176400 / 1000000000000), orderedInterval (-8534246585 / 1000000000000) (-8534245199 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 2) <| besselDerivativeNearFromState (136845411565963 / 800000000000) 2 (IntervalRat.scale (265 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (49486303600 / 1000000000000) (49486364379 / 1000000000000), orderedInterval (-35820786458 / 1000000000000) (-35820725679 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 2) <| besselDerivativeNearFromState (242834584231367 / 800000000000) 2 (IntervalRat.scale (265 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (18098036579 / 1000000000000) (18098037093 / 1000000000000), orderedInterval (-42098306333 / 1000000000000) (-42098305819 / 1000000000000)))) (orderedInterval (20982295627 / 1000000000000) (20982305031 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 2) <| besselDerivativeNearFromState (226887568262723 / 800000000000) 2 (IntervalRat.scale (265 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (47225686673 / 1000000000000) (47225687037 / 1000000000000), orderedInterval (-3882831576 / 1000000000000) (-3882831212 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 2) <| besselDerivativeNearFromState (161917674555059 / 800000000000) 2 (IntervalRat.scale (265 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (47837747452 / 1000000000000) (47837783267 / 1000000000000), orderedInterval (-29391792653 / 1000000000000) (-29391756838 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 2) <| besselDerivativeNearFromState (183597385602261 / 800000000000) 2 (IntervalRat.scale (265 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-42697616589 / 1000000000000) (-42697616588 / 1000000000000), orderedInterval (-30743534348 / 1000000000000) (-30743534347 / 1000000000000)))) (orderedInterval (-7268531793 / 1000000000000) (-7268523778 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 2) <| besselDerivativeNearFromState (153064359125509 / 800000000000) 2 (IntervalRat.scale (265 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-26536536952 / 1000000000000) (-26536536951 / 1000000000000), orderedInterval (-51147349183 / 1000000000000) (-51147349182 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 2) <| besselDerivativeNearFromState (135237003263689 / 800000000000) 2 (IntervalRat.scale (265 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (11282826630 / 1000000000000) (11282826631 / 1000000000000), orderedInterval (60287962566 / 1000000000000) (60287962567 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 2) <| besselDerivativeNearFromState (39196954661211 / 160000000000) 2 (IntervalRat.scale (265 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (33675719573 / 1000000000000) (33675719574 / 1000000000000), orderedInterval (38201316440 / 1000000000000) (38201316441 / 1000000000000)))) (orderedInterval (-1231566422 / 1000000000000) (-1231566394 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate257_chunkChecks2_2 :
    compactCertificate257.chunkChecks (2 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 2) <| besselDerivativeNearFromState (108420839415617 / 800000000000) 2 (IntervalRat.scale (265 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-64411301630 / 1000000000000) (-64411301629 / 1000000000000), orderedInterval (-23183674780 / 1000000000000) (-23183674779 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 2) <| besselDerivativeNearFromState (91909546300537 / 800000000000) 2 (IntervalRat.scale (265 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (40024682902 / 1000000000000) (40024691978 / 1000000000000), orderedInterval (-62938185147 / 1000000000000) (-62938176072 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 2) <| besselDerivativeNearFromState (57512726577811 / 800000000000) 2 (IntervalRat.scale (265 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-38193623380 / 1000000000000) (-38193623379 / 1000000000000), orderedInterval (-85738733154 / 1000000000000) (-85738733153 / 1000000000000)))) (orderedInterval (-8745970738 / 1000000000000) (-8745970319 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 2) <| besselDerivativeNearFromState (30930535632237 / 800000000000) 2 (IntervalRat.scale (265 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (126344389909 / 1000000000000) (126344390168 / 1000000000000), orderedInterval (-24030005328 / 1000000000000) (-24030005070 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 2) <| besselDerivativeNearFromState (83982421087711 / 800000000000) 2 (IntervalRat.scale (265 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-67623219300 / 1000000000000) (-67623202138 / 1000000000000), orderedInterval (38940467531 / 1000000000000) (38940484694 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 2) <| besselDerivativeNearFromState (114670816117247 / 800000000000) 2 (IntervalRat.scale (265 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-25350357919 / 1000000000000) (-25350356789 / 1000000000000), orderedInterval (61722436349 / 1000000000000) (61722437478 / 1000000000000)))) (orderedInterval (-2995120780 / 1000000000000) (-2995120416 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 2) <| besselDerivativeNearFromState (48487273422189 / 800000000000) 2 (IntervalRat.scale (265 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-101602724173 / 1000000000000) (-101602724010 / 1000000000000), orderedInterval (14263560931 / 1000000000000) (14263561094 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 2) <| besselDerivativeNearFromState (197098074528269 / 800000000000) 2 (IntervalRat.scale (265 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (43535209644 / 1000000000000) (43535250819 / 1000000000000), orderedInterval (-26330565670 / 1000000000000) (-26330524495 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 2) <| besselDerivativeNearFromState (131652379459171 / 800000000000) 2 (IntervalRat.scale (265 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (56879874397 / 1000000000000) (56879882803 / 1000000000000), orderedInterval (-25335425095 / 1000000000000) (-25335416688 / 1000000000000)))) (orderedInterval (28768409972 / 1000000000000) (28768424132 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate257_chunkChecks2 :
    compactCertificate257.chunkChecks (2 : Fin 5) 0 9 = true :=
  compactCertificate257.chunkChecks_nine_of_three (2 : Fin 5) compactCertificate257_chunkChecks2_0
    compactCertificate257_chunkChecks2_1 compactCertificate257_chunkChecks2_2

theorem compactCertificate257_chunkChecks3_0 :
    compactCertificate257.chunkChecks (3 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 3) <| besselDerivativeNearFromState (265 / 2) 3 (IntervalRat.scale (265 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (67438765133 / 1000000000000) (67438765134 / 1000000000000), orderedInterval (15766127353 / 1000000000000) (15766127355 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 3) <| besselDerivativeNearFromState (78079120238753 / 800000000000) 3 (IntervalRat.scale (265 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-67681423620 / 1000000000000) (-67681423619 / 1000000000000), orderedInterval (-43721488933 / 1000000000000) (-43721488932 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 3) <| besselDerivativeNearFromState (25249183248449 / 160000000000) 3 (IntervalRat.scale (265 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (63406470495 / 1000000000000) (63406470515 / 1000000000000), orderedInterval (3508033469 / 1000000000000) (3508033490 / 1000000000000)))) (orderedInterval (-6194400274 / 1000000000000) (-6194400257 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 3) <| besselDerivativeNearFromState (22783292553571 / 800000000000) 3 (IntervalRat.scale (265 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-124640368500 / 1000000000000) (-124640368499 / 1000000000000), orderedInterval (-80379663479 / 1000000000000) (-80379663478 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 3) <| besselDerivativeNearFromState (61199128534087 / 800000000000) 3 (IntervalRat.scale (265 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (86773121940 / 1000000000000) (86773123684 / 1000000000000), orderedInterval (-28713654256 / 1000000000000) (-28713652513 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 3) <| besselDerivativeNearFromState (166167538895979 / 800000000000) 3 (IntervalRat.scale (265 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (50512122466 / 1000000000000) (50512122467 / 1000000000000), orderedInterval (22538356889 / 1000000000000) (22538356890 / 1000000000000)))) (orderedInterval (6306947679 / 1000000000000) (6306947730 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 3) <| besselDerivativeNearFromState (122398257068227 / 800000000000) 3 (IntervalRat.scale (265 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (9998982851 / 1000000000000) (9998982899 / 1000000000000), orderedInterval (-63758764519 / 1000000000000) (-63758764472 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 3) <| besselDerivativeNearFromState (209731499697871 / 800000000000) 3 (IntervalRat.scale (265 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-39924874377 / 1000000000000) (-39924783063 / 1000000000000), orderedInterval (28960859753 / 1000000000000) (28960951068 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 3) <| besselDerivativeNearFromState (154487273422189 / 800000000000) 3 (IntervalRat.scale (265 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-44432104337 / 1000000000000) (-44431992088 / 1000000000000), orderedInterval (36480838569 / 1000000000000) (36480950818 / 1000000000000)))) (orderedInterval (4208905027 / 1000000000000) (4208935410 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate257_chunkChecks3_1 :
    compactCertificate257.chunkChecks (3 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 3) <| besselDerivativeNearFromState (237023205614947 / 800000000000) 3 (IntervalRat.scale (265 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (45576175014 / 1000000000000) (45576176400 / 1000000000000), orderedInterval (-8534246585 / 1000000000000) (-8534245199 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 3) <| besselDerivativeNearFromState (136845411565963 / 800000000000) 3 (IntervalRat.scale (265 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (49486303600 / 1000000000000) (49486364379 / 1000000000000), orderedInterval (-35820786458 / 1000000000000) (-35820725679 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 3) <| besselDerivativeNearFromState (242834584231367 / 800000000000) 3 (IntervalRat.scale (265 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (18098036579 / 1000000000000) (18098037093 / 1000000000000), orderedInterval (-42098306333 / 1000000000000) (-42098305819 / 1000000000000)))) (orderedInterval (60549277041 / 1000000000000) (60549290942 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 3) <| besselDerivativeNearFromState (226887568262723 / 800000000000) 3 (IntervalRat.scale (265 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (47225686673 / 1000000000000) (47225687037 / 1000000000000), orderedInterval (-3882831576 / 1000000000000) (-3882831212 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 3) <| besselDerivativeNearFromState (161917674555059 / 800000000000) 3 (IntervalRat.scale (265 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (47837747452 / 1000000000000) (47837783267 / 1000000000000), orderedInterval (-29391792653 / 1000000000000) (-29391756838 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 3) <| besselDerivativeNearFromState (183597385602261 / 800000000000) 3 (IntervalRat.scale (265 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-42697616589 / 1000000000000) (-42697616588 / 1000000000000), orderedInterval (-30743534348 / 1000000000000) (-30743534347 / 1000000000000)))) (orderedInterval (8465110712 / 1000000000000) (8465122980 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 3) <| besselDerivativeNearFromState (153064359125509 / 800000000000) 3 (IntervalRat.scale (265 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-26536536952 / 1000000000000) (-26536536951 / 1000000000000), orderedInterval (-51147349183 / 1000000000000) (-51147349182 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 3) <| besselDerivativeNearFromState (135237003263689 / 800000000000) 3 (IntervalRat.scale (265 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (11282826630 / 1000000000000) (11282826631 / 1000000000000), orderedInterval (60287962566 / 1000000000000) (60287962567 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 3) <| besselDerivativeNearFromState (39196954661211 / 160000000000) 3 (IntervalRat.scale (265 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (33675719573 / 1000000000000) (33675719574 / 1000000000000), orderedInterval (38201316440 / 1000000000000) (38201316441 / 1000000000000)))) (orderedInterval (2770089876 / 1000000000000) (2770089919 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate257_chunkChecks3_2 :
    compactCertificate257.chunkChecks (3 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 3) <| besselDerivativeNearFromState (108420839415617 / 800000000000) 3 (IntervalRat.scale (265 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-64411301630 / 1000000000000) (-64411301629 / 1000000000000), orderedInterval (-23183674780 / 1000000000000) (-23183674779 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 3) <| besselDerivativeNearFromState (91909546300537 / 800000000000) 3 (IntervalRat.scale (265 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (40024682902 / 1000000000000) (40024691978 / 1000000000000), orderedInterval (-62938185147 / 1000000000000) (-62938176072 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 3) <| besselDerivativeNearFromState (57512726577811 / 800000000000) 3 (IntervalRat.scale (265 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-38193623380 / 1000000000000) (-38193623379 / 1000000000000), orderedInterval (-85738733154 / 1000000000000) (-85738733153 / 1000000000000)))) (orderedInterval (-5776740855 / 1000000000000) (-5776740487 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 3) <| besselDerivativeNearFromState (30930535632237 / 800000000000) 3 (IntervalRat.scale (265 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (126344389909 / 1000000000000) (126344390168 / 1000000000000), orderedInterval (-24030005328 / 1000000000000) (-24030005070 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 3) <| besselDerivativeNearFromState (83982421087711 / 800000000000) 3 (IntervalRat.scale (265 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-67623219300 / 1000000000000) (-67623202138 / 1000000000000), orderedInterval (38940467531 / 1000000000000) (38940484694 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 3) <| besselDerivativeNearFromState (114670816117247 / 800000000000) 3 (IntervalRat.scale (265 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-25350357919 / 1000000000000) (-25350356789 / 1000000000000), orderedInterval (61722436349 / 1000000000000) (61722437478 / 1000000000000)))) (orderedInterval (6439328880 / 1000000000000) (6439329201 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 3) <| besselDerivativeNearFromState (48487273422189 / 800000000000) 3 (IntervalRat.scale (265 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-101602724173 / 1000000000000) (-101602724010 / 1000000000000), orderedInterval (14263560931 / 1000000000000) (14263561094 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 3) <| besselDerivativeNearFromState (197098074528269 / 800000000000) 3 (IntervalRat.scale (265 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (43535209644 / 1000000000000) (43535250819 / 1000000000000), orderedInterval (-26330565670 / 1000000000000) (-26330524495 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 3) <| besselDerivativeNearFromState (131652379459171 / 800000000000) 3 (IntervalRat.scale (265 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (56879874397 / 1000000000000) (56879882803 / 1000000000000), orderedInterval (-25335425095 / 1000000000000) (-25335416688 / 1000000000000)))) (orderedInterval (-23111300483 / 1000000000000) (-23111275691 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate257_chunkChecks3 :
    compactCertificate257.chunkChecks (3 : Fin 5) 0 9 = true :=
  compactCertificate257.chunkChecks_nine_of_three (3 : Fin 5) compactCertificate257_chunkChecks3_0
    compactCertificate257_chunkChecks3_1 compactCertificate257_chunkChecks3_2

theorem compactCertificate257_chunkChecks4_0 :
    compactCertificate257.chunkChecks (4 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 4) <| besselDerivativeNearFromState (265 / 2) 4 (IntervalRat.scale (265 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (67438765133 / 1000000000000) (67438765134 / 1000000000000), orderedInterval (15766127353 / 1000000000000) (15766127355 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 4) <| besselDerivativeNearFromState (78079120238753 / 800000000000) 4 (IntervalRat.scale (265 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-67681423620 / 1000000000000) (-67681423619 / 1000000000000), orderedInterval (-43721488933 / 1000000000000) (-43721488932 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 4) <| besselDerivativeNearFromState (25249183248449 / 160000000000) 4 (IntervalRat.scale (265 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (63406470495 / 1000000000000) (63406470515 / 1000000000000), orderedInterval (3508033469 / 1000000000000) (3508033490 / 1000000000000)))) (orderedInterval (34122886059 / 1000000000000) (34122886079 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 4) <| besselDerivativeNearFromState (22783292553571 / 800000000000) 4 (IntervalRat.scale (265 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-124640368500 / 1000000000000) (-124640368499 / 1000000000000), orderedInterval (-80379663479 / 1000000000000) (-80379663478 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 4) <| besselDerivativeNearFromState (61199128534087 / 800000000000) 4 (IntervalRat.scale (265 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (86773121940 / 1000000000000) (86773123684 / 1000000000000), orderedInterval (-28713654256 / 1000000000000) (-28713652513 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 4) <| besselDerivativeNearFromState (166167538895979 / 800000000000) 4 (IntervalRat.scale (265 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (50512122466 / 1000000000000) (50512122467 / 1000000000000), orderedInterval (22538356889 / 1000000000000) (22538356890 / 1000000000000)))) (orderedInterval (-21425035103 / 1000000000000) (-21425035037 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 4) <| besselDerivativeNearFromState (122398257068227 / 800000000000) 4 (IntervalRat.scale (265 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (9998982851 / 1000000000000) (9998982899 / 1000000000000), orderedInterval (-63758764519 / 1000000000000) (-63758764472 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 4) <| besselDerivativeNearFromState (209731499697871 / 800000000000) 4 (IntervalRat.scale (265 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-39924874377 / 1000000000000) (-39924783063 / 1000000000000), orderedInterval (28960859753 / 1000000000000) (28960951068 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 4) <| besselDerivativeNearFromState (154487273422189 / 800000000000) 4 (IntervalRat.scale (265 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-44432104337 / 1000000000000) (-44431992088 / 1000000000000), orderedInterval (36480838569 / 1000000000000) (36480950818 / 1000000000000)))) (orderedInterval (13964570572 / 1000000000000) (13964626509 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate257_chunkChecks4_1 :
    compactCertificate257.chunkChecks (4 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 4) <| besselDerivativeNearFromState (237023205614947 / 800000000000) 4 (IntervalRat.scale (265 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (45576175014 / 1000000000000) (45576176400 / 1000000000000), orderedInterval (-8534246585 / 1000000000000) (-8534245199 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 4) <| besselDerivativeNearFromState (136845411565963 / 800000000000) 4 (IntervalRat.scale (265 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (49486303600 / 1000000000000) (49486364379 / 1000000000000), orderedInterval (-35820786458 / 1000000000000) (-35820725679 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 4) <| besselDerivativeNearFromState (242834584231367 / 800000000000) 4 (IntervalRat.scale (265 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (18098036579 / 1000000000000) (18098037093 / 1000000000000), orderedInterval (-42098306333 / 1000000000000) (-42098305819 / 1000000000000)))) (orderedInterval (-122324094567 / 1000000000000) (-122324072553 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 4) <| besselDerivativeNearFromState (226887568262723 / 800000000000) 4 (IntervalRat.scale (265 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (47225686673 / 1000000000000) (47225687037 / 1000000000000), orderedInterval (-3882831576 / 1000000000000) (-3882831212 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 4) <| besselDerivativeNearFromState (161917674555059 / 800000000000) 4 (IntervalRat.scale (265 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (47837747452 / 1000000000000) (47837783267 / 1000000000000), orderedInterval (-29391792653 / 1000000000000) (-29391756838 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 4) <| besselDerivativeNearFromState (183597385602261 / 800000000000) 4 (IntervalRat.scale (265 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-42697616589 / 1000000000000) (-42697616588 / 1000000000000), orderedInterval (-30743534348 / 1000000000000) (-30743534347 / 1000000000000)))) (orderedInterval (8549661546 / 1000000000000) (8549680431 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 4) <| besselDerivativeNearFromState (153064359125509 / 800000000000) 4 (IntervalRat.scale (265 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-26536536952 / 1000000000000) (-26536536951 / 1000000000000), orderedInterval (-51147349183 / 1000000000000) (-51147349182 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 4) <| besselDerivativeNearFromState (135237003263689 / 800000000000) 4 (IntervalRat.scale (265 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (11282826630 / 1000000000000) (11282826631 / 1000000000000), orderedInterval (60287962566 / 1000000000000) (60287962567 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 4) <| besselDerivativeNearFromState (39196954661211 / 160000000000) 4 (IntervalRat.scale (265 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (33675719573 / 1000000000000) (33675719574 / 1000000000000), orderedInterval (38201316440 / 1000000000000) (38201316441 / 1000000000000)))) (orderedInterval (6991120800 / 1000000000000) (6991120868 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate257_chunkChecks4_2 :
    compactCertificate257.chunkChecks (4 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 4) <| besselDerivativeNearFromState (108420839415617 / 800000000000) 4 (IntervalRat.scale (265 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-64411301630 / 1000000000000) (-64411301629 / 1000000000000), orderedInterval (-23183674780 / 1000000000000) (-23183674779 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 4) <| besselDerivativeNearFromState (91909546300537 / 800000000000) 4 (IntervalRat.scale (265 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (40024682902 / 1000000000000) (40024691978 / 1000000000000), orderedInterval (-62938185147 / 1000000000000) (-62938176072 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 4) <| besselDerivativeNearFromState (57512726577811 / 800000000000) 4 (IntervalRat.scale (265 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-38193623380 / 1000000000000) (-38193623379 / 1000000000000), orderedInterval (-85738733154 / 1000000000000) (-85738733153 / 1000000000000)))) (orderedInterval (9970919034 / 1000000000000) (9970919359 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 4) <| besselDerivativeNearFromState (30930535632237 / 800000000000) 4 (IntervalRat.scale (265 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (126344389909 / 1000000000000) (126344390168 / 1000000000000), orderedInterval (-24030005328 / 1000000000000) (-24030005070 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 4) <| besselDerivativeNearFromState (83982421087711 / 800000000000) 4 (IntervalRat.scale (265 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-67623219300 / 1000000000000) (-67623202138 / 1000000000000), orderedInterval (38940467531 / 1000000000000) (38940484694 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 4) <| besselDerivativeNearFromState (114670816117247 / 800000000000) 4 (IntervalRat.scale (265 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-25350357919 / 1000000000000) (-25350356789 / 1000000000000), orderedInterval (61722436349 / 1000000000000) (61722437478 / 1000000000000)))) (orderedInterval (3151082079 / 1000000000000) (3151082371 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 4) <| besselDerivativeNearFromState (48487273422189 / 800000000000) 4 (IntervalRat.scale (265 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-101602724173 / 1000000000000) (-101602724010 / 1000000000000), orderedInterval (14263560931 / 1000000000000) (14263561094 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 4) <| besselDerivativeNearFromState (197098074528269 / 800000000000) 4 (IntervalRat.scale (265 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (43535209644 / 1000000000000) (43535250819 / 1000000000000), orderedInterval (-26330565670 / 1000000000000) (-26330524495 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 4) <| besselDerivativeNearFromState (131652379459171 / 800000000000) 4 (IntervalRat.scale (265 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (56879874397 / 1000000000000) (56879882803 / 1000000000000), orderedInterval (-25335425095 / 1000000000000) (-25335416688 / 1000000000000)))) (orderedInterval (-67433547752 / 1000000000000) (-67433503376 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate257_chunkChecks4 :
    compactCertificate257.chunkChecks (4 : Fin 5) 0 9 = true :=
  compactCertificate257.chunkChecks_nine_of_three (4 : Fin 5) compactCertificate257_chunkChecks4_0
    compactCertificate257_chunkChecks4_1 compactCertificate257_chunkChecks4_2

theorem compactCertificate257_chunks :
    ∀ r : Fin 5, ∀ b, compactCertificate257.chunkCheck r b = true :=
  compactCertificate257.chunkChecks_all (by
    intro r
    fin_cases r
    · exact compactCertificate257_chunkChecks0
    · exact compactCertificate257_chunkChecks1
    · exact compactCertificate257_chunkChecks2
    · exact compactCertificate257_chunkChecks3
    · exact compactCertificate257_chunkChecks4)

theorem compactCertificate257_coefficient0 :
    compactCertificate257.coefficientCheck (0 : Fin 5) = true := by
  norm_num [CompactCertificate.coefficientCheck, intervalFinSumHull,
    compactCertificate257, rationalIntervalSubset, orderedInterval, Fin.sum_univ_succ]

theorem compactCertificate257_coefficient1 :
    compactCertificate257.coefficientCheck (1 : Fin 5) = true := by
  norm_num [CompactCertificate.coefficientCheck, intervalFinSumHull,
    compactCertificate257, rationalIntervalSubset, orderedInterval, Fin.sum_univ_succ]

theorem compactCertificate257_coefficient2 :
    compactCertificate257.coefficientCheck (2 : Fin 5) = true := by
  norm_num [CompactCertificate.coefficientCheck, intervalFinSumHull,
    compactCertificate257, rationalIntervalSubset, orderedInterval, Fin.sum_univ_succ]

theorem compactCertificate257_coefficient3 :
    compactCertificate257.coefficientCheck (3 : Fin 5) = true := by
  norm_num [CompactCertificate.coefficientCheck, intervalFinSumHull,
    compactCertificate257, rationalIntervalSubset, orderedInterval, Fin.sum_univ_succ]

theorem compactCertificate257_coefficient4 :
    compactCertificate257.coefficientCheck (4 : Fin 5) = true := by
  norm_num [CompactCertificate.coefficientCheck, intervalFinSumHull,
    compactCertificate257, rationalIntervalSubset, orderedInterval, Fin.sum_univ_succ]

theorem compactCertificate257_coefficients : ∀ r : Fin 5,
    compactCertificate257.coefficientCheck r = true := by
  intro r
  fin_cases r
  · exact compactCertificate257_coefficient0
  · exact compactCertificate257_coefficient1
  · exact compactCertificate257_coefficient2
  · exact compactCertificate257_coefficient3
  · exact compactCertificate257_coefficient4

theorem compactCertificate257_lower : (1 : ℚ) ≤ compactCertificate257.output.lo := by
  norm_num [CompactCertificate.output, CompactCertificate.interval,
    CompactCertificate.coefficientTargetNat, compactCertificate257, dualConstant,
    intervalTaylorSum, intervalPow, intervalSub, intervalMaxAbs, widenInterval,
    rationalErrorInterval, orderedInterval, IntervalRat.add, IntervalRat.mul, IntervalRat.scale,
    IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4]

theorem compactCertificate257_proves {t : ℝ} (ht : t ∈ compactCertificate257.interval) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t :=
  compactCertificate257.proves compactCertificate257_states compactCertificate257_chunks
    compactCertificate257_coefficients compactCertificate257_lower ht

end Erdos232
