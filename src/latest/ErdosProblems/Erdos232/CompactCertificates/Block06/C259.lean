/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, OpenAI Codex
-/
import ErdosProblems.Erdos232.CompactBase

open LeanCert.Core
namespace Erdos232

def compactCertificate259 : CompactCertificate where
  left := 134
  right := 135
  center := 269 / 2
  grid := fun i =>
    match i.val with
    | 0 => 43
    | 1 => 32
    | 2 => 51
    | 3 => 9
    | 4 => 25
    | 5 => 67
    | 6 => 49
    | 7 => 85
    | 8 => 62
    | 9 => 96
    | 10 => 55
    | 11 => 98
    | 12 => 92
    | 13 => 65
    | 14 => 74
    | 15 => 62
    | 16 => 55
    | 17 => 79
    | 18 => 44
    | 19 => 37
    | 20 => 23
    | 21 => 12
    | 22 => 34
    | 23 => 46
    | 24 => 20
    | 25 => 80
    | _ => 53
  point := fun i =>
    match i.val with
    | 0 => 269 / 2
    | 1 => 396288364985369 / 4000000000000
    | 2 => 128151514977977 / 800000000000
    | 3 => 115635956545483 / 4000000000000
    | 4 => 310614444823951 / 4000000000000
    | 5 => 843378640811667 / 4000000000000
    | 6 => 621228889648171 / 4000000000000
    | 7 => 1064486290919383 / 4000000000000
    | 8 => 784095783972997 / 4000000000000
    | 9 => 1203004571894731 / 4000000000000
    | 10 => 694555013419699 / 4000000000000
    | 11 => 1232500059589391 / 4000000000000
    | 12 => 1151561431371179 / 4000000000000
    | 13 => 821808574628507 / 4000000000000
    | 14 => 931843334471853 / 4000000000000
    | 15 => 776873822731357 / 4000000000000
    | 16 => 686391582602497 / 4000000000000
    | 17 => 198943034035203 / 800000000000
    | 18 => 550286901939641 / 4000000000000
    | 19 => 466484301034801 / 4000000000000
    | 20 => 291904216027003 / 4000000000000
    | 21 => 156987058208901 / 4000000000000
    | 22 => 426250401369703 / 4000000000000
    | 23 => 582008481802631 / 4000000000000
    | 24 => 246095783972997 / 4000000000000
    | 25 => 1000365699020837 / 4000000000000
    | _ => 668197925934283 / 4000000000000
  state := fun i =>
    match i.val with
    | 0 => (orderedInterval (-13397255791 / 1000000000000) (-13397255790 / 1000000000000), orderedInterval (-67431870337 / 1000000000000) (-67431870336 / 1000000000000))
    | 1 => (orderedInterval (-50075782570 / 1000000000000) (-50075755140 / 1000000000000), orderedInterval (62848699361 / 1000000000000) (62848726791 / 1000000000000))
    | 2 => (orderedInterval (-43099445297 / 1000000000000) (-43099445296 / 1000000000000), orderedInterval (-45872087214 / 1000000000000) (-45872087213 / 1000000000000))
    | 3 => (orderedInterval (-146605023640 / 1000000000000) (-146605023638 / 1000000000000), orderedInterval (-20385703638 / 1000000000000) (-20385703636 / 1000000000000))
    | 4 => (orderedInterval (9256895334 / 1000000000000) (9256895372 / 1000000000000), orderedInterval (-90129992813 / 1000000000000) (-90129992776 / 1000000000000))
    | 5 => (orderedInterval (-49991402574 / 1000000000000) (-49991402573 / 1000000000000), orderedInterval (-22690052084 / 1000000000000) (-22690052083 / 1000000000000))
    | 6 => (orderedInterval (-53448966919 / 1000000000000) (-53448927680 / 1000000000000), orderedInterval (35418345575 / 1000000000000) (35418384814 / 1000000000000))
    | 7 => (orderedInterval (6285840408 / 1000000000000) (6285840422 / 1000000000000), orderedInterval (-48516514670 / 1000000000000) (-48516514656 / 1000000000000))
    | 8 => (orderedInterval (51085485102 / 1000000000000) (51085500090 / 1000000000000), orderedInterval (-25387572617 / 1000000000000) (-25387557630 / 1000000000000))
    | 9 => (orderedInterval (-2610452744 / 1000000000000) (-2610452741 / 1000000000000), orderedInterval (45938579514 / 1000000000000) (45938579518 / 1000000000000))
    | 10 => (orderedInterval (-60422212650 / 1000000000000) (-60422212507 / 1000000000000), orderedInterval (4109376376 / 1000000000000) (4109376519 / 1000000000000))
    | 11 => (orderedInterval (39059646088 / 1000000000000) (39059646089 / 1000000000000), orderedInterval (23184228978 / 1000000000000) (23184228979 / 1000000000000))
    | 12 => (orderedInterval (-16177770933 / 1000000000000) (-16177770652 / 1000000000000), orderedInterval (44182478932 / 1000000000000) (44182479214 / 1000000000000))
    | 13 => (orderedInterval (-49814200698 / 1000000000000) (-49814184477 / 1000000000000), orderedInterval (24964101784 / 1000000000000) (24964118005 / 1000000000000))
    | 14 => (orderedInterval (49894775485 / 1000000000000) (49894775487 / 1000000000000), orderedInterval (15489042077 / 1000000000000) (15489042079 / 1000000000000))
    | 15 => (orderedInterval (12743567127 / 1000000000000) (12743567128 / 1000000000000), orderedInterval (55783547503 / 1000000000000) (55783547504 / 1000000000000))
    | 16 => (orderedInterval (24001092779 / 1000000000000) (24001093917 / 1000000000000), orderedInterval (-56051264021 / 1000000000000) (-56051262883 / 1000000000000))
    | 17 => (orderedInterval (-48441191586 / 1000000000000) (-48441191585 / 1000000000000), orderedInterval (-14512700612 / 1000000000000) (-14512700610 / 1000000000000))
    | 18 => (orderedInterval (8557929899 / 1000000000000) (8557929900 / 1000000000000), orderedInterval (67454743529 / 1000000000000) (67454743530 / 1000000000000))
    | 19 => (orderedInterval (-67926524014 / 1000000000000) (-67926524013 / 1000000000000), orderedInterval (-28774683004 / 1000000000000) (-28774683003 / 1000000000000))
    | 20 => (orderedInterval (-93185668256 / 1000000000000) (-93185668246 / 1000000000000), orderedInterval (-5678904788 / 1000000000000) (-5678904779 / 1000000000000))
    | 21 => (orderedInterval (92393894394 / 1000000000000) (92394004497 / 1000000000000), orderedInterval (-88836730919 / 1000000000000) (-88836620816 / 1000000000000))
    | 22 => (orderedInterval (39252020014 / 1000000000000) (39252020015 / 1000000000000), orderedInterval (66399985010 / 1000000000000) (66399985011 / 1000000000000))
    | 23 => (orderedInterval (64793161368 / 1000000000000) (64793162072 / 1000000000000), orderedInterval (-13532509118 / 1000000000000) (-13532508414 / 1000000000000))
    | 24 => (orderedInterval (-50943449690 / 1000000000000) (-50943442050 / 1000000000000), orderedInterval (88461966238 / 1000000000000) (88461973879 / 1000000000000))
    | 25 => (orderedInterval (-21994949147 / 1000000000000) (-21994947920 / 1000000000000), orderedInterval (45450729956 / 1000000000000) (45450731184 / 1000000000000))
    | _ => (orderedInterval (-59947670574 / 1000000000000) (-59947670572 / 1000000000000), orderedInterval (-14559191406 / 1000000000000) (-14559191404 / 1000000000000))
  chunkTarget := fun r b =>
    match r.val with
    | 0 =>
      match b.val with
      | 0 => orderedInterval (-8305936933 / 1000000000000) (-8305936667 / 1000000000000)
      | 1 => orderedInterval (5482416828 / 1000000000000) (5482416847 / 1000000000000)
      | 2 => orderedInterval (1040754911 / 1000000000000) (1040755282 / 1000000000000)
      | 3 => orderedInterval (1539615994 / 1000000000000) (1539616060 / 1000000000000)
      | 4 => orderedInterval (-4671011212 / 1000000000000) (-4671009657 / 1000000000000)
      | 5 => orderedInterval (-2466630196 / 1000000000000) (-2466630117 / 1000000000000)
      | 6 => orderedInterval (-557394740 / 1000000000000) (-557394705 / 1000000000000)
      | 7 => orderedInterval (-7562245998 / 1000000000000) (-7562243894 / 1000000000000)
      | _ => orderedInterval (12731097234 / 1000000000000) (12731097418 / 1000000000000)
    | 1 =>
      match b.val with
      | 0 => orderedInterval (-29502225003 / 1000000000000) (-29502224803 / 1000000000000)
      | 1 => orderedInterval (676203066 / 1000000000000) (676203086 / 1000000000000)
      | 2 => orderedInterval (2066631575 / 1000000000000) (2066632118 / 1000000000000)
      | 3 => orderedInterval (-10309085921 / 1000000000000) (-10309085795 / 1000000000000)
      | 4 => orderedInterval (1762943176 / 1000000000000) (1762945557 / 1000000000000)
      | 5 => orderedInterval (4335517882 / 1000000000000) (4335517984 / 1000000000000)
      | 6 => orderedInterval (-9719982276 / 1000000000000) (-9719982244 / 1000000000000)
      | 7 => orderedInterval (407103883 / 1000000000000) (407104550 / 1000000000000)
      | _ => orderedInterval (-3242706239 / 1000000000000) (-3242705978 / 1000000000000)
    | 2 =>
      match b.val with
      | 0 => orderedInterval (9370230331 / 1000000000000) (9370230484 / 1000000000000)
      | 1 => orderedInterval (-8924548334 / 1000000000000) (-8924548307 / 1000000000000)
      | 2 => orderedInterval (-1878833640 / 1000000000000) (-1878832841 / 1000000000000)
      | 3 => orderedInterval (-23922137877 / 1000000000000) (-23922137619 / 1000000000000)
      | 4 => orderedInterval (10397643287 / 1000000000000) (10397646950 / 1000000000000)
      | 5 => orderedInterval (6136486112 / 1000000000000) (6136486248 / 1000000000000)
      | 6 => orderedInterval (-493544120 / 1000000000000) (-493544089 / 1000000000000)
      | 7 => orderedInterval (6512511280 / 1000000000000) (6512511536 / 1000000000000)
      | _ => orderedInterval (-23452416640 / 1000000000000) (-23452416205 / 1000000000000)
    | 3 =>
      match b.val with
      | 0 => orderedInterval (30969876255 / 1000000000000) (30969876374 / 1000000000000)
      | 1 => orderedInterval (-5516368683 / 1000000000000) (-5516368643 / 1000000000000)
      | 2 => orderedInterval (-9677830897 / 1000000000000) (-9677829724 / 1000000000000)
      | 3 => orderedInterval (51159071615 / 1000000000000) (51159072168 / 1000000000000)
      | 4 => orderedInterval (-261938780 / 1000000000000) (-261933163 / 1000000000000)
      | 5 => orderedInterval (-6297584864 / 1000000000000) (-6297584684 / 1000000000000)
      | 6 => orderedInterval (10512458697 / 1000000000000) (10512458727 / 1000000000000)
      | 7 => orderedInterval (-652978400 / 1000000000000) (-652978264 / 1000000000000)
      | _ => orderedInterval (18674615499 / 1000000000000) (18674616269 / 1000000000000)
    | _ =>
      match b.val with
      | 0 => orderedInterval (-10996363210 / 1000000000000) (-10996363116 / 1000000000000)
      | 1 => orderedInterval (21584124010 / 1000000000000) (21584124070 / 1000000000000)
      | 2 => orderedInterval (2742771519 / 1000000000000) (2742773256 / 1000000000000)
      | 3 => orderedInterval (151335327368 / 1000000000000) (151335328568 / 1000000000000)
      | 4 => orderedInterval (-21784044799 / 1000000000000) (-21784036132 / 1000000000000)
      | 5 => orderedInterval (-17399229347 / 1000000000000) (-17399229104 / 1000000000000)
      | 6 => orderedInterval (256126160 / 1000000000000) (256126189 / 1000000000000)
      | 7 => orderedInterval (-7154086002 / 1000000000000) (-7154085895 / 1000000000000)
      | _ => orderedInterval (47874416846 / 1000000000000) (47874418245 / 1000000000000)
  coefficientTarget := fun i =>
    match i.val with
    | 0 => orderedInterval (-2769334112 / 1000000000000) (-2769329433 / 1000000000000)
    | 1 => orderedInterval (-43525599857 / 1000000000000) (-43525595525 / 1000000000000)
    | 2 => orderedInterval (-26254609601 / 1000000000000) (-26254603843 / 1000000000000)
    | 3 => orderedInterval (88909320442 / 1000000000000) (88909329060 / 1000000000000)
    | _ => orderedInterval (166459042545 / 1000000000000) (166459056081 / 1000000000000)

theorem compactCertificate259_stateChecks0 :
    compactCertificate259.stateChecks 0 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 43 12 (269 / 2)) (orderedInterval (-13397255791 / 1000000000000) (-13397255790 / 1000000000000), orderedInterval (-67431870337 / 1000000000000) (-67431870336 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 32 12 (396288364985369 / 4000000000000)) (orderedInterval (-50075782570 / 1000000000000) (-50075755140 / 1000000000000), orderedInterval (62848699361 / 1000000000000) (62848726791 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 51 12 (128151514977977 / 800000000000)) (orderedInterval (-43099445297 / 1000000000000) (-43099445296 / 1000000000000), orderedInterval (-45872087214 / 1000000000000) (-45872087213 / 1000000000000))) = true
  norm_num [besselStateAtRationalPoint, besselIntervalStepZero,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, besselZeroTransition,
    besselInitial, besselGridStateAt, besselGridStateBlock00, besselGridStateBlock01,
    besselGridStateBlock02, besselGridStateBlock03, besselGridStateBlock04,
    besselGridStateBlock05, besselGridStateBlock06, besselGridStateBlock07,
    besselGridStateBlock08, besselGridStateBlock09, besselGridStateBlock10,
    besselGridStateBlock11, besselGridStateBlock12, besselGridStateBlock13,
    besselGridStateBlock14, besselGridState009, besselGridState012, besselGridState020, besselGridState023, besselGridState025, besselGridState032, besselGridState034, besselGridState037, besselGridState043, besselGridState044, besselGridState046, besselGridState049, besselGridState051, besselGridState053, besselGridState055, besselGridState062, besselGridState065, besselGridState067, besselGridState074, besselGridState079, besselGridState080, besselGridState085, besselGridState092, besselGridState096, besselGridState098, besselStateSubset, linearInterval, widenInterval,
    rationalErrorInterval, rationalIntervalSubset, orderedInterval, Finset.sum_range_succ,
    IntervalRat.add, IntervalRat.mul, IntervalRat.scale, IntervalRat.singleton]

theorem compactCertificate259_stateChecks1 :
    compactCertificate259.stateChecks 3 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 9 12 (115635956545483 / 4000000000000)) (orderedInterval (-146605023640 / 1000000000000) (-146605023638 / 1000000000000), orderedInterval (-20385703638 / 1000000000000) (-20385703636 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 25 12 (310614444823951 / 4000000000000)) (orderedInterval (9256895334 / 1000000000000) (9256895372 / 1000000000000), orderedInterval (-90129992813 / 1000000000000) (-90129992776 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 67 12 (843378640811667 / 4000000000000)) (orderedInterval (-49991402574 / 1000000000000) (-49991402573 / 1000000000000), orderedInterval (-22690052084 / 1000000000000) (-22690052083 / 1000000000000))) = true
  norm_num [besselStateAtRationalPoint, besselIntervalStepZero,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, besselZeroTransition,
    besselInitial, besselGridStateAt, besselGridStateBlock00, besselGridStateBlock01,
    besselGridStateBlock02, besselGridStateBlock03, besselGridStateBlock04,
    besselGridStateBlock05, besselGridStateBlock06, besselGridStateBlock07,
    besselGridStateBlock08, besselGridStateBlock09, besselGridStateBlock10,
    besselGridStateBlock11, besselGridStateBlock12, besselGridStateBlock13,
    besselGridStateBlock14, besselGridState009, besselGridState012, besselGridState020, besselGridState023, besselGridState025, besselGridState032, besselGridState034, besselGridState037, besselGridState043, besselGridState044, besselGridState046, besselGridState049, besselGridState051, besselGridState053, besselGridState055, besselGridState062, besselGridState065, besselGridState067, besselGridState074, besselGridState079, besselGridState080, besselGridState085, besselGridState092, besselGridState096, besselGridState098, besselStateSubset, linearInterval, widenInterval,
    rationalErrorInterval, rationalIntervalSubset, orderedInterval, Finset.sum_range_succ,
    IntervalRat.add, IntervalRat.mul, IntervalRat.scale, IntervalRat.singleton]

theorem compactCertificate259_stateChecks2 :
    compactCertificate259.stateChecks 6 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 49 12 (621228889648171 / 4000000000000)) (orderedInterval (-53448966919 / 1000000000000) (-53448927680 / 1000000000000), orderedInterval (35418345575 / 1000000000000) (35418384814 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 85 12 (1064486290919383 / 4000000000000)) (orderedInterval (6285840408 / 1000000000000) (6285840422 / 1000000000000), orderedInterval (-48516514670 / 1000000000000) (-48516514656 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 62 12 (784095783972997 / 4000000000000)) (orderedInterval (51085485102 / 1000000000000) (51085500090 / 1000000000000), orderedInterval (-25387572617 / 1000000000000) (-25387557630 / 1000000000000))) = true
  norm_num [besselStateAtRationalPoint, besselIntervalStepZero,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, besselZeroTransition,
    besselInitial, besselGridStateAt, besselGridStateBlock00, besselGridStateBlock01,
    besselGridStateBlock02, besselGridStateBlock03, besselGridStateBlock04,
    besselGridStateBlock05, besselGridStateBlock06, besselGridStateBlock07,
    besselGridStateBlock08, besselGridStateBlock09, besselGridStateBlock10,
    besselGridStateBlock11, besselGridStateBlock12, besselGridStateBlock13,
    besselGridStateBlock14, besselGridState009, besselGridState012, besselGridState020, besselGridState023, besselGridState025, besselGridState032, besselGridState034, besselGridState037, besselGridState043, besselGridState044, besselGridState046, besselGridState049, besselGridState051, besselGridState053, besselGridState055, besselGridState062, besselGridState065, besselGridState067, besselGridState074, besselGridState079, besselGridState080, besselGridState085, besselGridState092, besselGridState096, besselGridState098, besselStateSubset, linearInterval, widenInterval,
    rationalErrorInterval, rationalIntervalSubset, orderedInterval, Finset.sum_range_succ,
    IntervalRat.add, IntervalRat.mul, IntervalRat.scale, IntervalRat.singleton]

theorem compactCertificate259_stateChecks3 :
    compactCertificate259.stateChecks 9 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 96 12 (1203004571894731 / 4000000000000)) (orderedInterval (-2610452744 / 1000000000000) (-2610452741 / 1000000000000), orderedInterval (45938579514 / 1000000000000) (45938579518 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 55 12 (694555013419699 / 4000000000000)) (orderedInterval (-60422212650 / 1000000000000) (-60422212507 / 1000000000000), orderedInterval (4109376376 / 1000000000000) (4109376519 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 98 12 (1232500059589391 / 4000000000000)) (orderedInterval (39059646088 / 1000000000000) (39059646089 / 1000000000000), orderedInterval (23184228978 / 1000000000000) (23184228979 / 1000000000000))) = true
  norm_num [besselStateAtRationalPoint, besselIntervalStepZero,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, besselZeroTransition,
    besselInitial, besselGridStateAt, besselGridStateBlock00, besselGridStateBlock01,
    besselGridStateBlock02, besselGridStateBlock03, besselGridStateBlock04,
    besselGridStateBlock05, besselGridStateBlock06, besselGridStateBlock07,
    besselGridStateBlock08, besselGridStateBlock09, besselGridStateBlock10,
    besselGridStateBlock11, besselGridStateBlock12, besselGridStateBlock13,
    besselGridStateBlock14, besselGridState009, besselGridState012, besselGridState020, besselGridState023, besselGridState025, besselGridState032, besselGridState034, besselGridState037, besselGridState043, besselGridState044, besselGridState046, besselGridState049, besselGridState051, besselGridState053, besselGridState055, besselGridState062, besselGridState065, besselGridState067, besselGridState074, besselGridState079, besselGridState080, besselGridState085, besselGridState092, besselGridState096, besselGridState098, besselStateSubset, linearInterval, widenInterval,
    rationalErrorInterval, rationalIntervalSubset, orderedInterval, Finset.sum_range_succ,
    IntervalRat.add, IntervalRat.mul, IntervalRat.scale, IntervalRat.singleton]

theorem compactCertificate259_stateChecks4 :
    compactCertificate259.stateChecks 12 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 92 12 (1151561431371179 / 4000000000000)) (orderedInterval (-16177770933 / 1000000000000) (-16177770652 / 1000000000000), orderedInterval (44182478932 / 1000000000000) (44182479214 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 65 12 (821808574628507 / 4000000000000)) (orderedInterval (-49814200698 / 1000000000000) (-49814184477 / 1000000000000), orderedInterval (24964101784 / 1000000000000) (24964118005 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 74 12 (931843334471853 / 4000000000000)) (orderedInterval (49894775485 / 1000000000000) (49894775487 / 1000000000000), orderedInterval (15489042077 / 1000000000000) (15489042079 / 1000000000000))) = true
  norm_num [besselStateAtRationalPoint, besselIntervalStepZero,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, besselZeroTransition,
    besselInitial, besselGridStateAt, besselGridStateBlock00, besselGridStateBlock01,
    besselGridStateBlock02, besselGridStateBlock03, besselGridStateBlock04,
    besselGridStateBlock05, besselGridStateBlock06, besselGridStateBlock07,
    besselGridStateBlock08, besselGridStateBlock09, besselGridStateBlock10,
    besselGridStateBlock11, besselGridStateBlock12, besselGridStateBlock13,
    besselGridStateBlock14, besselGridState009, besselGridState012, besselGridState020, besselGridState023, besselGridState025, besselGridState032, besselGridState034, besselGridState037, besselGridState043, besselGridState044, besselGridState046, besselGridState049, besselGridState051, besselGridState053, besselGridState055, besselGridState062, besselGridState065, besselGridState067, besselGridState074, besselGridState079, besselGridState080, besselGridState085, besselGridState092, besselGridState096, besselGridState098, besselStateSubset, linearInterval, widenInterval,
    rationalErrorInterval, rationalIntervalSubset, orderedInterval, Finset.sum_range_succ,
    IntervalRat.add, IntervalRat.mul, IntervalRat.scale, IntervalRat.singleton]

theorem compactCertificate259_stateChecks5 :
    compactCertificate259.stateChecks 15 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 62 12 (776873822731357 / 4000000000000)) (orderedInterval (12743567127 / 1000000000000) (12743567128 / 1000000000000), orderedInterval (55783547503 / 1000000000000) (55783547504 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 55 12 (686391582602497 / 4000000000000)) (orderedInterval (24001092779 / 1000000000000) (24001093917 / 1000000000000), orderedInterval (-56051264021 / 1000000000000) (-56051262883 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 79 12 (198943034035203 / 800000000000)) (orderedInterval (-48441191586 / 1000000000000) (-48441191585 / 1000000000000), orderedInterval (-14512700612 / 1000000000000) (-14512700610 / 1000000000000))) = true
  norm_num [besselStateAtRationalPoint, besselIntervalStepZero,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, besselZeroTransition,
    besselInitial, besselGridStateAt, besselGridStateBlock00, besselGridStateBlock01,
    besselGridStateBlock02, besselGridStateBlock03, besselGridStateBlock04,
    besselGridStateBlock05, besselGridStateBlock06, besselGridStateBlock07,
    besselGridStateBlock08, besselGridStateBlock09, besselGridStateBlock10,
    besselGridStateBlock11, besselGridStateBlock12, besselGridStateBlock13,
    besselGridStateBlock14, besselGridState009, besselGridState012, besselGridState020, besselGridState023, besselGridState025, besselGridState032, besselGridState034, besselGridState037, besselGridState043, besselGridState044, besselGridState046, besselGridState049, besselGridState051, besselGridState053, besselGridState055, besselGridState062, besselGridState065, besselGridState067, besselGridState074, besselGridState079, besselGridState080, besselGridState085, besselGridState092, besselGridState096, besselGridState098, besselStateSubset, linearInterval, widenInterval,
    rationalErrorInterval, rationalIntervalSubset, orderedInterval, Finset.sum_range_succ,
    IntervalRat.add, IntervalRat.mul, IntervalRat.scale, IntervalRat.singleton]

theorem compactCertificate259_stateChecks6 :
    compactCertificate259.stateChecks 18 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 44 12 (550286901939641 / 4000000000000)) (orderedInterval (8557929899 / 1000000000000) (8557929900 / 1000000000000), orderedInterval (67454743529 / 1000000000000) (67454743530 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 37 12 (466484301034801 / 4000000000000)) (orderedInterval (-67926524014 / 1000000000000) (-67926524013 / 1000000000000), orderedInterval (-28774683004 / 1000000000000) (-28774683003 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 23 12 (291904216027003 / 4000000000000)) (orderedInterval (-93185668256 / 1000000000000) (-93185668246 / 1000000000000), orderedInterval (-5678904788 / 1000000000000) (-5678904779 / 1000000000000))) = true
  norm_num [besselStateAtRationalPoint, besselIntervalStepZero,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, besselZeroTransition,
    besselInitial, besselGridStateAt, besselGridStateBlock00, besselGridStateBlock01,
    besselGridStateBlock02, besselGridStateBlock03, besselGridStateBlock04,
    besselGridStateBlock05, besselGridStateBlock06, besselGridStateBlock07,
    besselGridStateBlock08, besselGridStateBlock09, besselGridStateBlock10,
    besselGridStateBlock11, besselGridStateBlock12, besselGridStateBlock13,
    besselGridStateBlock14, besselGridState009, besselGridState012, besselGridState020, besselGridState023, besselGridState025, besselGridState032, besselGridState034, besselGridState037, besselGridState043, besselGridState044, besselGridState046, besselGridState049, besselGridState051, besselGridState053, besselGridState055, besselGridState062, besselGridState065, besselGridState067, besselGridState074, besselGridState079, besselGridState080, besselGridState085, besselGridState092, besselGridState096, besselGridState098, besselStateSubset, linearInterval, widenInterval,
    rationalErrorInterval, rationalIntervalSubset, orderedInterval, Finset.sum_range_succ,
    IntervalRat.add, IntervalRat.mul, IntervalRat.scale, IntervalRat.singleton]

theorem compactCertificate259_stateChecks7 :
    compactCertificate259.stateChecks 21 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 12 12 (156987058208901 / 4000000000000)) (orderedInterval (92393894394 / 1000000000000) (92394004497 / 1000000000000), orderedInterval (-88836730919 / 1000000000000) (-88836620816 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 34 12 (426250401369703 / 4000000000000)) (orderedInterval (39252020014 / 1000000000000) (39252020015 / 1000000000000), orderedInterval (66399985010 / 1000000000000) (66399985011 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 46 12 (582008481802631 / 4000000000000)) (orderedInterval (64793161368 / 1000000000000) (64793162072 / 1000000000000), orderedInterval (-13532509118 / 1000000000000) (-13532508414 / 1000000000000))) = true
  norm_num [besselStateAtRationalPoint, besselIntervalStepZero,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, besselZeroTransition,
    besselInitial, besselGridStateAt, besselGridStateBlock00, besselGridStateBlock01,
    besselGridStateBlock02, besselGridStateBlock03, besselGridStateBlock04,
    besselGridStateBlock05, besselGridStateBlock06, besselGridStateBlock07,
    besselGridStateBlock08, besselGridStateBlock09, besselGridStateBlock10,
    besselGridStateBlock11, besselGridStateBlock12, besselGridStateBlock13,
    besselGridStateBlock14, besselGridState009, besselGridState012, besselGridState020, besselGridState023, besselGridState025, besselGridState032, besselGridState034, besselGridState037, besselGridState043, besselGridState044, besselGridState046, besselGridState049, besselGridState051, besselGridState053, besselGridState055, besselGridState062, besselGridState065, besselGridState067, besselGridState074, besselGridState079, besselGridState080, besselGridState085, besselGridState092, besselGridState096, besselGridState098, besselStateSubset, linearInterval, widenInterval,
    rationalErrorInterval, rationalIntervalSubset, orderedInterval, Finset.sum_range_succ,
    IntervalRat.add, IntervalRat.mul, IntervalRat.scale, IntervalRat.singleton]

theorem compactCertificate259_stateChecks8 :
    compactCertificate259.stateChecks 24 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 20 12 (246095783972997 / 4000000000000)) (orderedInterval (-50943449690 / 1000000000000) (-50943442050 / 1000000000000), orderedInterval (88461966238 / 1000000000000) (88461973879 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 80 12 (1000365699020837 / 4000000000000)) (orderedInterval (-21994949147 / 1000000000000) (-21994947920 / 1000000000000), orderedInterval (45450729956 / 1000000000000) (45450731184 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 53 12 (668197925934283 / 4000000000000)) (orderedInterval (-59947670574 / 1000000000000) (-59947670572 / 1000000000000), orderedInterval (-14559191406 / 1000000000000) (-14559191404 / 1000000000000))) = true
  norm_num [besselStateAtRationalPoint, besselIntervalStepZero,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, besselZeroTransition,
    besselInitial, besselGridStateAt, besselGridStateBlock00, besselGridStateBlock01,
    besselGridStateBlock02, besselGridStateBlock03, besselGridStateBlock04,
    besselGridStateBlock05, besselGridStateBlock06, besselGridStateBlock07,
    besselGridStateBlock08, besselGridStateBlock09, besselGridStateBlock10,
    besselGridStateBlock11, besselGridStateBlock12, besselGridStateBlock13,
    besselGridStateBlock14, besselGridState009, besselGridState012, besselGridState020, besselGridState023, besselGridState025, besselGridState032, besselGridState034, besselGridState037, besselGridState043, besselGridState044, besselGridState046, besselGridState049, besselGridState051, besselGridState053, besselGridState055, besselGridState062, besselGridState065, besselGridState067, besselGridState074, besselGridState079, besselGridState080, besselGridState085, besselGridState092, besselGridState096, besselGridState098, besselStateSubset, linearInterval, widenInterval,
    rationalErrorInterval, rationalIntervalSubset, orderedInterval, Finset.sum_range_succ,
    IntervalRat.add, IntervalRat.mul, IntervalRat.scale, IntervalRat.singleton]

theorem compactCertificate259_states : ∀ j,
    BesselStateValid (compactCertificate259.point j) (compactCertificate259.state j) :=
  compactCertificate259.statesValid_of_checks3 compactCertificate259_stateChecks0
    compactCertificate259_stateChecks1 compactCertificate259_stateChecks2
    compactCertificate259_stateChecks3 compactCertificate259_stateChecks4
    compactCertificate259_stateChecks5 compactCertificate259_stateChecks6
    compactCertificate259_stateChecks7 compactCertificate259_stateChecks8

theorem compactCertificate259_chunkChecks0_0 :
    compactCertificate259.chunkChecks (0 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 0) <| besselDerivativeNearFromState (269 / 2) 0 (IntervalRat.scale (269 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-13397255791 / 1000000000000) (-13397255790 / 1000000000000), orderedInterval (-67431870337 / 1000000000000) (-67431870336 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 0) <| besselDerivativeNearFromState (396288364985369 / 4000000000000) 0 (IntervalRat.scale (269 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-50075782570 / 1000000000000) (-50075755140 / 1000000000000), orderedInterval (62848699361 / 1000000000000) (62848726791 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 0) <| besselDerivativeNearFromState (128151514977977 / 800000000000) 0 (IntervalRat.scale (269 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-43099445297 / 1000000000000) (-43099445296 / 1000000000000), orderedInterval (-45872087214 / 1000000000000) (-45872087213 / 1000000000000)))) (orderedInterval (-8305936933 / 1000000000000) (-8305936667 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 0) <| besselDerivativeNearFromState (115635956545483 / 4000000000000) 0 (IntervalRat.scale (269 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-146605023640 / 1000000000000) (-146605023638 / 1000000000000), orderedInterval (-20385703638 / 1000000000000) (-20385703636 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 0) <| besselDerivativeNearFromState (310614444823951 / 4000000000000) 0 (IntervalRat.scale (269 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (9256895334 / 1000000000000) (9256895372 / 1000000000000), orderedInterval (-90129992813 / 1000000000000) (-90129992776 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 0) <| besselDerivativeNearFromState (843378640811667 / 4000000000000) 0 (IntervalRat.scale (269 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-49991402574 / 1000000000000) (-49991402573 / 1000000000000), orderedInterval (-22690052084 / 1000000000000) (-22690052083 / 1000000000000)))) (orderedInterval (5482416828 / 1000000000000) (5482416847 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 0) <| besselDerivativeNearFromState (621228889648171 / 4000000000000) 0 (IntervalRat.scale (269 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-53448966919 / 1000000000000) (-53448927680 / 1000000000000), orderedInterval (35418345575 / 1000000000000) (35418384814 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 0) <| besselDerivativeNearFromState (1064486290919383 / 4000000000000) 0 (IntervalRat.scale (269 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (6285840408 / 1000000000000) (6285840422 / 1000000000000), orderedInterval (-48516514670 / 1000000000000) (-48516514656 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 0) <| besselDerivativeNearFromState (784095783972997 / 4000000000000) 0 (IntervalRat.scale (269 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (51085485102 / 1000000000000) (51085500090 / 1000000000000), orderedInterval (-25387572617 / 1000000000000) (-25387557630 / 1000000000000)))) (orderedInterval (1040754911 / 1000000000000) (1040755282 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate259_chunkChecks0_1 :
    compactCertificate259.chunkChecks (0 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 0) <| besselDerivativeNearFromState (1203004571894731 / 4000000000000) 0 (IntervalRat.scale (269 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-2610452744 / 1000000000000) (-2610452741 / 1000000000000), orderedInterval (45938579514 / 1000000000000) (45938579518 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 0) <| besselDerivativeNearFromState (694555013419699 / 4000000000000) 0 (IntervalRat.scale (269 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-60422212650 / 1000000000000) (-60422212507 / 1000000000000), orderedInterval (4109376376 / 1000000000000) (4109376519 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 0) <| besselDerivativeNearFromState (1232500059589391 / 4000000000000) 0 (IntervalRat.scale (269 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (39059646088 / 1000000000000) (39059646089 / 1000000000000), orderedInterval (23184228978 / 1000000000000) (23184228979 / 1000000000000)))) (orderedInterval (1539615994 / 1000000000000) (1539616060 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 0) <| besselDerivativeNearFromState (1151561431371179 / 4000000000000) 0 (IntervalRat.scale (269 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-16177770933 / 1000000000000) (-16177770652 / 1000000000000), orderedInterval (44182478932 / 1000000000000) (44182479214 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 0) <| besselDerivativeNearFromState (821808574628507 / 4000000000000) 0 (IntervalRat.scale (269 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-49814200698 / 1000000000000) (-49814184477 / 1000000000000), orderedInterval (24964101784 / 1000000000000) (24964118005 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 0) <| besselDerivativeNearFromState (931843334471853 / 4000000000000) 0 (IntervalRat.scale (269 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (49894775485 / 1000000000000) (49894775487 / 1000000000000), orderedInterval (15489042077 / 1000000000000) (15489042079 / 1000000000000)))) (orderedInterval (-4671011212 / 1000000000000) (-4671009657 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 0) <| besselDerivativeNearFromState (776873822731357 / 4000000000000) 0 (IntervalRat.scale (269 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (12743567127 / 1000000000000) (12743567128 / 1000000000000), orderedInterval (55783547503 / 1000000000000) (55783547504 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 0) <| besselDerivativeNearFromState (686391582602497 / 4000000000000) 0 (IntervalRat.scale (269 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (24001092779 / 1000000000000) (24001093917 / 1000000000000), orderedInterval (-56051264021 / 1000000000000) (-56051262883 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 0) <| besselDerivativeNearFromState (198943034035203 / 800000000000) 0 (IntervalRat.scale (269 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-48441191586 / 1000000000000) (-48441191585 / 1000000000000), orderedInterval (-14512700612 / 1000000000000) (-14512700610 / 1000000000000)))) (orderedInterval (-2466630196 / 1000000000000) (-2466630117 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate259_chunkChecks0_2 :
    compactCertificate259.chunkChecks (0 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 0) <| besselDerivativeNearFromState (550286901939641 / 4000000000000) 0 (IntervalRat.scale (269 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (8557929899 / 1000000000000) (8557929900 / 1000000000000), orderedInterval (67454743529 / 1000000000000) (67454743530 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 0) <| besselDerivativeNearFromState (466484301034801 / 4000000000000) 0 (IntervalRat.scale (269 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-67926524014 / 1000000000000) (-67926524013 / 1000000000000), orderedInterval (-28774683004 / 1000000000000) (-28774683003 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 0) <| besselDerivativeNearFromState (291904216027003 / 4000000000000) 0 (IntervalRat.scale (269 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-93185668256 / 1000000000000) (-93185668246 / 1000000000000), orderedInterval (-5678904788 / 1000000000000) (-5678904779 / 1000000000000)))) (orderedInterval (-557394740 / 1000000000000) (-557394705 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 0) <| besselDerivativeNearFromState (156987058208901 / 4000000000000) 0 (IntervalRat.scale (269 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (92393894394 / 1000000000000) (92394004497 / 1000000000000), orderedInterval (-88836730919 / 1000000000000) (-88836620816 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 0) <| besselDerivativeNearFromState (426250401369703 / 4000000000000) 0 (IntervalRat.scale (269 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (39252020014 / 1000000000000) (39252020015 / 1000000000000), orderedInterval (66399985010 / 1000000000000) (66399985011 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 0) <| besselDerivativeNearFromState (582008481802631 / 4000000000000) 0 (IntervalRat.scale (269 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (64793161368 / 1000000000000) (64793162072 / 1000000000000), orderedInterval (-13532509118 / 1000000000000) (-13532508414 / 1000000000000)))) (orderedInterval (-7562245998 / 1000000000000) (-7562243894 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 0) <| besselDerivativeNearFromState (246095783972997 / 4000000000000) 0 (IntervalRat.scale (269 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-50943449690 / 1000000000000) (-50943442050 / 1000000000000), orderedInterval (88461966238 / 1000000000000) (88461973879 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 0) <| besselDerivativeNearFromState (1000365699020837 / 4000000000000) 0 (IntervalRat.scale (269 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-21994949147 / 1000000000000) (-21994947920 / 1000000000000), orderedInterval (45450729956 / 1000000000000) (45450731184 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 0) <| besselDerivativeNearFromState (668197925934283 / 4000000000000) 0 (IntervalRat.scale (269 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-59947670574 / 1000000000000) (-59947670572 / 1000000000000), orderedInterval (-14559191406 / 1000000000000) (-14559191404 / 1000000000000)))) (orderedInterval (12731097234 / 1000000000000) (12731097418 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate259_chunkChecks0 :
    compactCertificate259.chunkChecks (0 : Fin 5) 0 9 = true :=
  compactCertificate259.chunkChecks_nine_of_three (0 : Fin 5) compactCertificate259_chunkChecks0_0
    compactCertificate259_chunkChecks0_1 compactCertificate259_chunkChecks0_2

theorem compactCertificate259_chunkChecks1_0 :
    compactCertificate259.chunkChecks (1 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 1) <| besselDerivativeNearFromState (269 / 2) 1 (IntervalRat.scale (269 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-13397255791 / 1000000000000) (-13397255790 / 1000000000000), orderedInterval (-67431870337 / 1000000000000) (-67431870336 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 1) <| besselDerivativeNearFromState (396288364985369 / 4000000000000) 1 (IntervalRat.scale (269 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-50075782570 / 1000000000000) (-50075755140 / 1000000000000), orderedInterval (62848699361 / 1000000000000) (62848726791 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 1) <| besselDerivativeNearFromState (128151514977977 / 800000000000) 1 (IntervalRat.scale (269 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-43099445297 / 1000000000000) (-43099445296 / 1000000000000), orderedInterval (-45872087214 / 1000000000000) (-45872087213 / 1000000000000)))) (orderedInterval (-29502225003 / 1000000000000) (-29502224803 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 1) <| besselDerivativeNearFromState (115635956545483 / 4000000000000) 1 (IntervalRat.scale (269 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-146605023640 / 1000000000000) (-146605023638 / 1000000000000), orderedInterval (-20385703638 / 1000000000000) (-20385703636 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 1) <| besselDerivativeNearFromState (310614444823951 / 4000000000000) 1 (IntervalRat.scale (269 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (9256895334 / 1000000000000) (9256895372 / 1000000000000), orderedInterval (-90129992813 / 1000000000000) (-90129992776 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 1) <| besselDerivativeNearFromState (843378640811667 / 4000000000000) 1 (IntervalRat.scale (269 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-49991402574 / 1000000000000) (-49991402573 / 1000000000000), orderedInterval (-22690052084 / 1000000000000) (-22690052083 / 1000000000000)))) (orderedInterval (676203066 / 1000000000000) (676203086 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 1) <| besselDerivativeNearFromState (621228889648171 / 4000000000000) 1 (IntervalRat.scale (269 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-53448966919 / 1000000000000) (-53448927680 / 1000000000000), orderedInterval (35418345575 / 1000000000000) (35418384814 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 1) <| besselDerivativeNearFromState (1064486290919383 / 4000000000000) 1 (IntervalRat.scale (269 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (6285840408 / 1000000000000) (6285840422 / 1000000000000), orderedInterval (-48516514670 / 1000000000000) (-48516514656 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 1) <| besselDerivativeNearFromState (784095783972997 / 4000000000000) 1 (IntervalRat.scale (269 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (51085485102 / 1000000000000) (51085500090 / 1000000000000), orderedInterval (-25387572617 / 1000000000000) (-25387557630 / 1000000000000)))) (orderedInterval (2066631575 / 1000000000000) (2066632118 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate259_chunkChecks1_1 :
    compactCertificate259.chunkChecks (1 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 1) <| besselDerivativeNearFromState (1203004571894731 / 4000000000000) 1 (IntervalRat.scale (269 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-2610452744 / 1000000000000) (-2610452741 / 1000000000000), orderedInterval (45938579514 / 1000000000000) (45938579518 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 1) <| besselDerivativeNearFromState (694555013419699 / 4000000000000) 1 (IntervalRat.scale (269 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-60422212650 / 1000000000000) (-60422212507 / 1000000000000), orderedInterval (4109376376 / 1000000000000) (4109376519 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 1) <| besselDerivativeNearFromState (1232500059589391 / 4000000000000) 1 (IntervalRat.scale (269 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (39059646088 / 1000000000000) (39059646089 / 1000000000000), orderedInterval (23184228978 / 1000000000000) (23184228979 / 1000000000000)))) (orderedInterval (-10309085921 / 1000000000000) (-10309085795 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 1) <| besselDerivativeNearFromState (1151561431371179 / 4000000000000) 1 (IntervalRat.scale (269 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-16177770933 / 1000000000000) (-16177770652 / 1000000000000), orderedInterval (44182478932 / 1000000000000) (44182479214 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 1) <| besselDerivativeNearFromState (821808574628507 / 4000000000000) 1 (IntervalRat.scale (269 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-49814200698 / 1000000000000) (-49814184477 / 1000000000000), orderedInterval (24964101784 / 1000000000000) (24964118005 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 1) <| besselDerivativeNearFromState (931843334471853 / 4000000000000) 1 (IntervalRat.scale (269 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (49894775485 / 1000000000000) (49894775487 / 1000000000000), orderedInterval (15489042077 / 1000000000000) (15489042079 / 1000000000000)))) (orderedInterval (1762943176 / 1000000000000) (1762945557 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 1) <| besselDerivativeNearFromState (776873822731357 / 4000000000000) 1 (IntervalRat.scale (269 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (12743567127 / 1000000000000) (12743567128 / 1000000000000), orderedInterval (55783547503 / 1000000000000) (55783547504 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 1) <| besselDerivativeNearFromState (686391582602497 / 4000000000000) 1 (IntervalRat.scale (269 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (24001092779 / 1000000000000) (24001093917 / 1000000000000), orderedInterval (-56051264021 / 1000000000000) (-56051262883 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 1) <| besselDerivativeNearFromState (198943034035203 / 800000000000) 1 (IntervalRat.scale (269 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-48441191586 / 1000000000000) (-48441191585 / 1000000000000), orderedInterval (-14512700612 / 1000000000000) (-14512700610 / 1000000000000)))) (orderedInterval (4335517882 / 1000000000000) (4335517984 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate259_chunkChecks1_2 :
    compactCertificate259.chunkChecks (1 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 1) <| besselDerivativeNearFromState (550286901939641 / 4000000000000) 1 (IntervalRat.scale (269 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (8557929899 / 1000000000000) (8557929900 / 1000000000000), orderedInterval (67454743529 / 1000000000000) (67454743530 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 1) <| besselDerivativeNearFromState (466484301034801 / 4000000000000) 1 (IntervalRat.scale (269 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-67926524014 / 1000000000000) (-67926524013 / 1000000000000), orderedInterval (-28774683004 / 1000000000000) (-28774683003 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 1) <| besselDerivativeNearFromState (291904216027003 / 4000000000000) 1 (IntervalRat.scale (269 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-93185668256 / 1000000000000) (-93185668246 / 1000000000000), orderedInterval (-5678904788 / 1000000000000) (-5678904779 / 1000000000000)))) (orderedInterval (-9719982276 / 1000000000000) (-9719982244 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 1) <| besselDerivativeNearFromState (156987058208901 / 4000000000000) 1 (IntervalRat.scale (269 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (92393894394 / 1000000000000) (92394004497 / 1000000000000), orderedInterval (-88836730919 / 1000000000000) (-88836620816 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 1) <| besselDerivativeNearFromState (426250401369703 / 4000000000000) 1 (IntervalRat.scale (269 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (39252020014 / 1000000000000) (39252020015 / 1000000000000), orderedInterval (66399985010 / 1000000000000) (66399985011 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 1) <| besselDerivativeNearFromState (582008481802631 / 4000000000000) 1 (IntervalRat.scale (269 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (64793161368 / 1000000000000) (64793162072 / 1000000000000), orderedInterval (-13532509118 / 1000000000000) (-13532508414 / 1000000000000)))) (orderedInterval (407103883 / 1000000000000) (407104550 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 1) <| besselDerivativeNearFromState (246095783972997 / 4000000000000) 1 (IntervalRat.scale (269 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-50943449690 / 1000000000000) (-50943442050 / 1000000000000), orderedInterval (88461966238 / 1000000000000) (88461973879 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 1) <| besselDerivativeNearFromState (1000365699020837 / 4000000000000) 1 (IntervalRat.scale (269 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-21994949147 / 1000000000000) (-21994947920 / 1000000000000), orderedInterval (45450729956 / 1000000000000) (45450731184 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 1) <| besselDerivativeNearFromState (668197925934283 / 4000000000000) 1 (IntervalRat.scale (269 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-59947670574 / 1000000000000) (-59947670572 / 1000000000000), orderedInterval (-14559191406 / 1000000000000) (-14559191404 / 1000000000000)))) (orderedInterval (-3242706239 / 1000000000000) (-3242705978 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate259_chunkChecks1 :
    compactCertificate259.chunkChecks (1 : Fin 5) 0 9 = true :=
  compactCertificate259.chunkChecks_nine_of_three (1 : Fin 5) compactCertificate259_chunkChecks1_0
    compactCertificate259_chunkChecks1_1 compactCertificate259_chunkChecks1_2

theorem compactCertificate259_chunkChecks2_0 :
    compactCertificate259.chunkChecks (2 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 2) <| besselDerivativeNearFromState (269 / 2) 2 (IntervalRat.scale (269 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-13397255791 / 1000000000000) (-13397255790 / 1000000000000), orderedInterval (-67431870337 / 1000000000000) (-67431870336 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 2) <| besselDerivativeNearFromState (396288364985369 / 4000000000000) 2 (IntervalRat.scale (269 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-50075782570 / 1000000000000) (-50075755140 / 1000000000000), orderedInterval (62848699361 / 1000000000000) (62848726791 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 2) <| besselDerivativeNearFromState (128151514977977 / 800000000000) 2 (IntervalRat.scale (269 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-43099445297 / 1000000000000) (-43099445296 / 1000000000000), orderedInterval (-45872087214 / 1000000000000) (-45872087213 / 1000000000000)))) (orderedInterval (9370230331 / 1000000000000) (9370230484 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 2) <| besselDerivativeNearFromState (115635956545483 / 4000000000000) 2 (IntervalRat.scale (269 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-146605023640 / 1000000000000) (-146605023638 / 1000000000000), orderedInterval (-20385703638 / 1000000000000) (-20385703636 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 2) <| besselDerivativeNearFromState (310614444823951 / 4000000000000) 2 (IntervalRat.scale (269 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (9256895334 / 1000000000000) (9256895372 / 1000000000000), orderedInterval (-90129992813 / 1000000000000) (-90129992776 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 2) <| besselDerivativeNearFromState (843378640811667 / 4000000000000) 2 (IntervalRat.scale (269 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-49991402574 / 1000000000000) (-49991402573 / 1000000000000), orderedInterval (-22690052084 / 1000000000000) (-22690052083 / 1000000000000)))) (orderedInterval (-8924548334 / 1000000000000) (-8924548307 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 2) <| besselDerivativeNearFromState (621228889648171 / 4000000000000) 2 (IntervalRat.scale (269 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-53448966919 / 1000000000000) (-53448927680 / 1000000000000), orderedInterval (35418345575 / 1000000000000) (35418384814 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 2) <| besselDerivativeNearFromState (1064486290919383 / 4000000000000) 2 (IntervalRat.scale (269 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (6285840408 / 1000000000000) (6285840422 / 1000000000000), orderedInterval (-48516514670 / 1000000000000) (-48516514656 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 2) <| besselDerivativeNearFromState (784095783972997 / 4000000000000) 2 (IntervalRat.scale (269 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (51085485102 / 1000000000000) (51085500090 / 1000000000000), orderedInterval (-25387572617 / 1000000000000) (-25387557630 / 1000000000000)))) (orderedInterval (-1878833640 / 1000000000000) (-1878832841 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate259_chunkChecks2_1 :
    compactCertificate259.chunkChecks (2 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 2) <| besselDerivativeNearFromState (1203004571894731 / 4000000000000) 2 (IntervalRat.scale (269 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-2610452744 / 1000000000000) (-2610452741 / 1000000000000), orderedInterval (45938579514 / 1000000000000) (45938579518 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 2) <| besselDerivativeNearFromState (694555013419699 / 4000000000000) 2 (IntervalRat.scale (269 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-60422212650 / 1000000000000) (-60422212507 / 1000000000000), orderedInterval (4109376376 / 1000000000000) (4109376519 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 2) <| besselDerivativeNearFromState (1232500059589391 / 4000000000000) 2 (IntervalRat.scale (269 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (39059646088 / 1000000000000) (39059646089 / 1000000000000), orderedInterval (23184228978 / 1000000000000) (23184228979 / 1000000000000)))) (orderedInterval (-23922137877 / 1000000000000) (-23922137619 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 2) <| besselDerivativeNearFromState (1151561431371179 / 4000000000000) 2 (IntervalRat.scale (269 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-16177770933 / 1000000000000) (-16177770652 / 1000000000000), orderedInterval (44182478932 / 1000000000000) (44182479214 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 2) <| besselDerivativeNearFromState (821808574628507 / 4000000000000) 2 (IntervalRat.scale (269 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-49814200698 / 1000000000000) (-49814184477 / 1000000000000), orderedInterval (24964101784 / 1000000000000) (24964118005 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 2) <| besselDerivativeNearFromState (931843334471853 / 4000000000000) 2 (IntervalRat.scale (269 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (49894775485 / 1000000000000) (49894775487 / 1000000000000), orderedInterval (15489042077 / 1000000000000) (15489042079 / 1000000000000)))) (orderedInterval (10397643287 / 1000000000000) (10397646950 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 2) <| besselDerivativeNearFromState (776873822731357 / 4000000000000) 2 (IntervalRat.scale (269 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (12743567127 / 1000000000000) (12743567128 / 1000000000000), orderedInterval (55783547503 / 1000000000000) (55783547504 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 2) <| besselDerivativeNearFromState (686391582602497 / 4000000000000) 2 (IntervalRat.scale (269 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (24001092779 / 1000000000000) (24001093917 / 1000000000000), orderedInterval (-56051264021 / 1000000000000) (-56051262883 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 2) <| besselDerivativeNearFromState (198943034035203 / 800000000000) 2 (IntervalRat.scale (269 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-48441191586 / 1000000000000) (-48441191585 / 1000000000000), orderedInterval (-14512700612 / 1000000000000) (-14512700610 / 1000000000000)))) (orderedInterval (6136486112 / 1000000000000) (6136486248 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate259_chunkChecks2_2 :
    compactCertificate259.chunkChecks (2 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 2) <| besselDerivativeNearFromState (550286901939641 / 4000000000000) 2 (IntervalRat.scale (269 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (8557929899 / 1000000000000) (8557929900 / 1000000000000), orderedInterval (67454743529 / 1000000000000) (67454743530 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 2) <| besselDerivativeNearFromState (466484301034801 / 4000000000000) 2 (IntervalRat.scale (269 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-67926524014 / 1000000000000) (-67926524013 / 1000000000000), orderedInterval (-28774683004 / 1000000000000) (-28774683003 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 2) <| besselDerivativeNearFromState (291904216027003 / 4000000000000) 2 (IntervalRat.scale (269 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-93185668256 / 1000000000000) (-93185668246 / 1000000000000), orderedInterval (-5678904788 / 1000000000000) (-5678904779 / 1000000000000)))) (orderedInterval (-493544120 / 1000000000000) (-493544089 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 2) <| besselDerivativeNearFromState (156987058208901 / 4000000000000) 2 (IntervalRat.scale (269 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (92393894394 / 1000000000000) (92394004497 / 1000000000000), orderedInterval (-88836730919 / 1000000000000) (-88836620816 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 2) <| besselDerivativeNearFromState (426250401369703 / 4000000000000) 2 (IntervalRat.scale (269 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (39252020014 / 1000000000000) (39252020015 / 1000000000000), orderedInterval (66399985010 / 1000000000000) (66399985011 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 2) <| besselDerivativeNearFromState (582008481802631 / 4000000000000) 2 (IntervalRat.scale (269 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (64793161368 / 1000000000000) (64793162072 / 1000000000000), orderedInterval (-13532509118 / 1000000000000) (-13532508414 / 1000000000000)))) (orderedInterval (6512511280 / 1000000000000) (6512511536 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 2) <| besselDerivativeNearFromState (246095783972997 / 4000000000000) 2 (IntervalRat.scale (269 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-50943449690 / 1000000000000) (-50943442050 / 1000000000000), orderedInterval (88461966238 / 1000000000000) (88461973879 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 2) <| besselDerivativeNearFromState (1000365699020837 / 4000000000000) 2 (IntervalRat.scale (269 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-21994949147 / 1000000000000) (-21994947920 / 1000000000000), orderedInterval (45450729956 / 1000000000000) (45450731184 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 2) <| besselDerivativeNearFromState (668197925934283 / 4000000000000) 2 (IntervalRat.scale (269 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-59947670574 / 1000000000000) (-59947670572 / 1000000000000), orderedInterval (-14559191406 / 1000000000000) (-14559191404 / 1000000000000)))) (orderedInterval (-23452416640 / 1000000000000) (-23452416205 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate259_chunkChecks2 :
    compactCertificate259.chunkChecks (2 : Fin 5) 0 9 = true :=
  compactCertificate259.chunkChecks_nine_of_three (2 : Fin 5) compactCertificate259_chunkChecks2_0
    compactCertificate259_chunkChecks2_1 compactCertificate259_chunkChecks2_2

theorem compactCertificate259_chunkChecks3_0 :
    compactCertificate259.chunkChecks (3 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 3) <| besselDerivativeNearFromState (269 / 2) 3 (IntervalRat.scale (269 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-13397255791 / 1000000000000) (-13397255790 / 1000000000000), orderedInterval (-67431870337 / 1000000000000) (-67431870336 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 3) <| besselDerivativeNearFromState (396288364985369 / 4000000000000) 3 (IntervalRat.scale (269 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-50075782570 / 1000000000000) (-50075755140 / 1000000000000), orderedInterval (62848699361 / 1000000000000) (62848726791 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 3) <| besselDerivativeNearFromState (128151514977977 / 800000000000) 3 (IntervalRat.scale (269 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-43099445297 / 1000000000000) (-43099445296 / 1000000000000), orderedInterval (-45872087214 / 1000000000000) (-45872087213 / 1000000000000)))) (orderedInterval (30969876255 / 1000000000000) (30969876374 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 3) <| besselDerivativeNearFromState (115635956545483 / 4000000000000) 3 (IntervalRat.scale (269 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-146605023640 / 1000000000000) (-146605023638 / 1000000000000), orderedInterval (-20385703638 / 1000000000000) (-20385703636 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 3) <| besselDerivativeNearFromState (310614444823951 / 4000000000000) 3 (IntervalRat.scale (269 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (9256895334 / 1000000000000) (9256895372 / 1000000000000), orderedInterval (-90129992813 / 1000000000000) (-90129992776 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 3) <| besselDerivativeNearFromState (843378640811667 / 4000000000000) 3 (IntervalRat.scale (269 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-49991402574 / 1000000000000) (-49991402573 / 1000000000000), orderedInterval (-22690052084 / 1000000000000) (-22690052083 / 1000000000000)))) (orderedInterval (-5516368683 / 1000000000000) (-5516368643 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 3) <| besselDerivativeNearFromState (621228889648171 / 4000000000000) 3 (IntervalRat.scale (269 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-53448966919 / 1000000000000) (-53448927680 / 1000000000000), orderedInterval (35418345575 / 1000000000000) (35418384814 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 3) <| besselDerivativeNearFromState (1064486290919383 / 4000000000000) 3 (IntervalRat.scale (269 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (6285840408 / 1000000000000) (6285840422 / 1000000000000), orderedInterval (-48516514670 / 1000000000000) (-48516514656 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 3) <| besselDerivativeNearFromState (784095783972997 / 4000000000000) 3 (IntervalRat.scale (269 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (51085485102 / 1000000000000) (51085500090 / 1000000000000), orderedInterval (-25387572617 / 1000000000000) (-25387557630 / 1000000000000)))) (orderedInterval (-9677830897 / 1000000000000) (-9677829724 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate259_chunkChecks3_1 :
    compactCertificate259.chunkChecks (3 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 3) <| besselDerivativeNearFromState (1203004571894731 / 4000000000000) 3 (IntervalRat.scale (269 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-2610452744 / 1000000000000) (-2610452741 / 1000000000000), orderedInterval (45938579514 / 1000000000000) (45938579518 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 3) <| besselDerivativeNearFromState (694555013419699 / 4000000000000) 3 (IntervalRat.scale (269 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-60422212650 / 1000000000000) (-60422212507 / 1000000000000), orderedInterval (4109376376 / 1000000000000) (4109376519 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 3) <| besselDerivativeNearFromState (1232500059589391 / 4000000000000) 3 (IntervalRat.scale (269 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (39059646088 / 1000000000000) (39059646089 / 1000000000000), orderedInterval (23184228978 / 1000000000000) (23184228979 / 1000000000000)))) (orderedInterval (51159071615 / 1000000000000) (51159072168 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 3) <| besselDerivativeNearFromState (1151561431371179 / 4000000000000) 3 (IntervalRat.scale (269 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-16177770933 / 1000000000000) (-16177770652 / 1000000000000), orderedInterval (44182478932 / 1000000000000) (44182479214 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 3) <| besselDerivativeNearFromState (821808574628507 / 4000000000000) 3 (IntervalRat.scale (269 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-49814200698 / 1000000000000) (-49814184477 / 1000000000000), orderedInterval (24964101784 / 1000000000000) (24964118005 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 3) <| besselDerivativeNearFromState (931843334471853 / 4000000000000) 3 (IntervalRat.scale (269 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (49894775485 / 1000000000000) (49894775487 / 1000000000000), orderedInterval (15489042077 / 1000000000000) (15489042079 / 1000000000000)))) (orderedInterval (-261938780 / 1000000000000) (-261933163 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 3) <| besselDerivativeNearFromState (776873822731357 / 4000000000000) 3 (IntervalRat.scale (269 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (12743567127 / 1000000000000) (12743567128 / 1000000000000), orderedInterval (55783547503 / 1000000000000) (55783547504 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 3) <| besselDerivativeNearFromState (686391582602497 / 4000000000000) 3 (IntervalRat.scale (269 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (24001092779 / 1000000000000) (24001093917 / 1000000000000), orderedInterval (-56051264021 / 1000000000000) (-56051262883 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 3) <| besselDerivativeNearFromState (198943034035203 / 800000000000) 3 (IntervalRat.scale (269 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-48441191586 / 1000000000000) (-48441191585 / 1000000000000), orderedInterval (-14512700612 / 1000000000000) (-14512700610 / 1000000000000)))) (orderedInterval (-6297584864 / 1000000000000) (-6297584684 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate259_chunkChecks3_2 :
    compactCertificate259.chunkChecks (3 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 3) <| besselDerivativeNearFromState (550286901939641 / 4000000000000) 3 (IntervalRat.scale (269 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (8557929899 / 1000000000000) (8557929900 / 1000000000000), orderedInterval (67454743529 / 1000000000000) (67454743530 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 3) <| besselDerivativeNearFromState (466484301034801 / 4000000000000) 3 (IntervalRat.scale (269 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-67926524014 / 1000000000000) (-67926524013 / 1000000000000), orderedInterval (-28774683004 / 1000000000000) (-28774683003 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 3) <| besselDerivativeNearFromState (291904216027003 / 4000000000000) 3 (IntervalRat.scale (269 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-93185668256 / 1000000000000) (-93185668246 / 1000000000000), orderedInterval (-5678904788 / 1000000000000) (-5678904779 / 1000000000000)))) (orderedInterval (10512458697 / 1000000000000) (10512458727 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 3) <| besselDerivativeNearFromState (156987058208901 / 4000000000000) 3 (IntervalRat.scale (269 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (92393894394 / 1000000000000) (92394004497 / 1000000000000), orderedInterval (-88836730919 / 1000000000000) (-88836620816 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 3) <| besselDerivativeNearFromState (426250401369703 / 4000000000000) 3 (IntervalRat.scale (269 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (39252020014 / 1000000000000) (39252020015 / 1000000000000), orderedInterval (66399985010 / 1000000000000) (66399985011 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 3) <| besselDerivativeNearFromState (582008481802631 / 4000000000000) 3 (IntervalRat.scale (269 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (64793161368 / 1000000000000) (64793162072 / 1000000000000), orderedInterval (-13532509118 / 1000000000000) (-13532508414 / 1000000000000)))) (orderedInterval (-652978400 / 1000000000000) (-652978264 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 3) <| besselDerivativeNearFromState (246095783972997 / 4000000000000) 3 (IntervalRat.scale (269 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-50943449690 / 1000000000000) (-50943442050 / 1000000000000), orderedInterval (88461966238 / 1000000000000) (88461973879 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 3) <| besselDerivativeNearFromState (1000365699020837 / 4000000000000) 3 (IntervalRat.scale (269 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-21994949147 / 1000000000000) (-21994947920 / 1000000000000), orderedInterval (45450729956 / 1000000000000) (45450731184 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 3) <| besselDerivativeNearFromState (668197925934283 / 4000000000000) 3 (IntervalRat.scale (269 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-59947670574 / 1000000000000) (-59947670572 / 1000000000000), orderedInterval (-14559191406 / 1000000000000) (-14559191404 / 1000000000000)))) (orderedInterval (18674615499 / 1000000000000) (18674616269 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate259_chunkChecks3 :
    compactCertificate259.chunkChecks (3 : Fin 5) 0 9 = true :=
  compactCertificate259.chunkChecks_nine_of_three (3 : Fin 5) compactCertificate259_chunkChecks3_0
    compactCertificate259_chunkChecks3_1 compactCertificate259_chunkChecks3_2

theorem compactCertificate259_chunkChecks4_0 :
    compactCertificate259.chunkChecks (4 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 4) <| besselDerivativeNearFromState (269 / 2) 4 (IntervalRat.scale (269 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-13397255791 / 1000000000000) (-13397255790 / 1000000000000), orderedInterval (-67431870337 / 1000000000000) (-67431870336 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 4) <| besselDerivativeNearFromState (396288364985369 / 4000000000000) 4 (IntervalRat.scale (269 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-50075782570 / 1000000000000) (-50075755140 / 1000000000000), orderedInterval (62848699361 / 1000000000000) (62848726791 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 4) <| besselDerivativeNearFromState (128151514977977 / 800000000000) 4 (IntervalRat.scale (269 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-43099445297 / 1000000000000) (-43099445296 / 1000000000000), orderedInterval (-45872087214 / 1000000000000) (-45872087213 / 1000000000000)))) (orderedInterval (-10996363210 / 1000000000000) (-10996363116 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 4) <| besselDerivativeNearFromState (115635956545483 / 4000000000000) 4 (IntervalRat.scale (269 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-146605023640 / 1000000000000) (-146605023638 / 1000000000000), orderedInterval (-20385703638 / 1000000000000) (-20385703636 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 4) <| besselDerivativeNearFromState (310614444823951 / 4000000000000) 4 (IntervalRat.scale (269 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (9256895334 / 1000000000000) (9256895372 / 1000000000000), orderedInterval (-90129992813 / 1000000000000) (-90129992776 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 4) <| besselDerivativeNearFromState (843378640811667 / 4000000000000) 4 (IntervalRat.scale (269 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-49991402574 / 1000000000000) (-49991402573 / 1000000000000), orderedInterval (-22690052084 / 1000000000000) (-22690052083 / 1000000000000)))) (orderedInterval (21584124010 / 1000000000000) (21584124070 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 4) <| besselDerivativeNearFromState (621228889648171 / 4000000000000) 4 (IntervalRat.scale (269 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-53448966919 / 1000000000000) (-53448927680 / 1000000000000), orderedInterval (35418345575 / 1000000000000) (35418384814 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 4) <| besselDerivativeNearFromState (1064486290919383 / 4000000000000) 4 (IntervalRat.scale (269 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (6285840408 / 1000000000000) (6285840422 / 1000000000000), orderedInterval (-48516514670 / 1000000000000) (-48516514656 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 4) <| besselDerivativeNearFromState (784095783972997 / 4000000000000) 4 (IntervalRat.scale (269 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (51085485102 / 1000000000000) (51085500090 / 1000000000000), orderedInterval (-25387572617 / 1000000000000) (-25387557630 / 1000000000000)))) (orderedInterval (2742771519 / 1000000000000) (2742773256 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate259_chunkChecks4_1 :
    compactCertificate259.chunkChecks (4 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 4) <| besselDerivativeNearFromState (1203004571894731 / 4000000000000) 4 (IntervalRat.scale (269 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-2610452744 / 1000000000000) (-2610452741 / 1000000000000), orderedInterval (45938579514 / 1000000000000) (45938579518 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 4) <| besselDerivativeNearFromState (694555013419699 / 4000000000000) 4 (IntervalRat.scale (269 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-60422212650 / 1000000000000) (-60422212507 / 1000000000000), orderedInterval (4109376376 / 1000000000000) (4109376519 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 4) <| besselDerivativeNearFromState (1232500059589391 / 4000000000000) 4 (IntervalRat.scale (269 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (39059646088 / 1000000000000) (39059646089 / 1000000000000), orderedInterval (23184228978 / 1000000000000) (23184228979 / 1000000000000)))) (orderedInterval (151335327368 / 1000000000000) (151335328568 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 4) <| besselDerivativeNearFromState (1151561431371179 / 4000000000000) 4 (IntervalRat.scale (269 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-16177770933 / 1000000000000) (-16177770652 / 1000000000000), orderedInterval (44182478932 / 1000000000000) (44182479214 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 4) <| besselDerivativeNearFromState (821808574628507 / 4000000000000) 4 (IntervalRat.scale (269 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-49814200698 / 1000000000000) (-49814184477 / 1000000000000), orderedInterval (24964101784 / 1000000000000) (24964118005 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 4) <| besselDerivativeNearFromState (931843334471853 / 4000000000000) 4 (IntervalRat.scale (269 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (49894775485 / 1000000000000) (49894775487 / 1000000000000), orderedInterval (15489042077 / 1000000000000) (15489042079 / 1000000000000)))) (orderedInterval (-21784044799 / 1000000000000) (-21784036132 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 4) <| besselDerivativeNearFromState (776873822731357 / 4000000000000) 4 (IntervalRat.scale (269 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (12743567127 / 1000000000000) (12743567128 / 1000000000000), orderedInterval (55783547503 / 1000000000000) (55783547504 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 4) <| besselDerivativeNearFromState (686391582602497 / 4000000000000) 4 (IntervalRat.scale (269 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (24001092779 / 1000000000000) (24001093917 / 1000000000000), orderedInterval (-56051264021 / 1000000000000) (-56051262883 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 4) <| besselDerivativeNearFromState (198943034035203 / 800000000000) 4 (IntervalRat.scale (269 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-48441191586 / 1000000000000) (-48441191585 / 1000000000000), orderedInterval (-14512700612 / 1000000000000) (-14512700610 / 1000000000000)))) (orderedInterval (-17399229347 / 1000000000000) (-17399229104 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate259_chunkChecks4_2 :
    compactCertificate259.chunkChecks (4 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 4) <| besselDerivativeNearFromState (550286901939641 / 4000000000000) 4 (IntervalRat.scale (269 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (8557929899 / 1000000000000) (8557929900 / 1000000000000), orderedInterval (67454743529 / 1000000000000) (67454743530 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 4) <| besselDerivativeNearFromState (466484301034801 / 4000000000000) 4 (IntervalRat.scale (269 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-67926524014 / 1000000000000) (-67926524013 / 1000000000000), orderedInterval (-28774683004 / 1000000000000) (-28774683003 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 4) <| besselDerivativeNearFromState (291904216027003 / 4000000000000) 4 (IntervalRat.scale (269 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-93185668256 / 1000000000000) (-93185668246 / 1000000000000), orderedInterval (-5678904788 / 1000000000000) (-5678904779 / 1000000000000)))) (orderedInterval (256126160 / 1000000000000) (256126189 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 4) <| besselDerivativeNearFromState (156987058208901 / 4000000000000) 4 (IntervalRat.scale (269 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (92393894394 / 1000000000000) (92394004497 / 1000000000000), orderedInterval (-88836730919 / 1000000000000) (-88836620816 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 4) <| besselDerivativeNearFromState (426250401369703 / 4000000000000) 4 (IntervalRat.scale (269 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (39252020014 / 1000000000000) (39252020015 / 1000000000000), orderedInterval (66399985010 / 1000000000000) (66399985011 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 4) <| besselDerivativeNearFromState (582008481802631 / 4000000000000) 4 (IntervalRat.scale (269 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (64793161368 / 1000000000000) (64793162072 / 1000000000000), orderedInterval (-13532509118 / 1000000000000) (-13532508414 / 1000000000000)))) (orderedInterval (-7154086002 / 1000000000000) (-7154085895 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 4) <| besselDerivativeNearFromState (246095783972997 / 4000000000000) 4 (IntervalRat.scale (269 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-50943449690 / 1000000000000) (-50943442050 / 1000000000000), orderedInterval (88461966238 / 1000000000000) (88461973879 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 4) <| besselDerivativeNearFromState (1000365699020837 / 4000000000000) 4 (IntervalRat.scale (269 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-21994949147 / 1000000000000) (-21994947920 / 1000000000000), orderedInterval (45450729956 / 1000000000000) (45450731184 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 4) <| besselDerivativeNearFromState (668197925934283 / 4000000000000) 4 (IntervalRat.scale (269 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-59947670574 / 1000000000000) (-59947670572 / 1000000000000), orderedInterval (-14559191406 / 1000000000000) (-14559191404 / 1000000000000)))) (orderedInterval (47874416846 / 1000000000000) (47874418245 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate259_chunkChecks4 :
    compactCertificate259.chunkChecks (4 : Fin 5) 0 9 = true :=
  compactCertificate259.chunkChecks_nine_of_three (4 : Fin 5) compactCertificate259_chunkChecks4_0
    compactCertificate259_chunkChecks4_1 compactCertificate259_chunkChecks4_2

theorem compactCertificate259_chunks :
    ∀ r : Fin 5, ∀ b, compactCertificate259.chunkCheck r b = true :=
  compactCertificate259.chunkChecks_all (by
    intro r
    fin_cases r
    · exact compactCertificate259_chunkChecks0
    · exact compactCertificate259_chunkChecks1
    · exact compactCertificate259_chunkChecks2
    · exact compactCertificate259_chunkChecks3
    · exact compactCertificate259_chunkChecks4)

theorem compactCertificate259_coefficient0 :
    compactCertificate259.coefficientCheck (0 : Fin 5) = true := by
  norm_num [CompactCertificate.coefficientCheck, intervalFinSumHull,
    compactCertificate259, rationalIntervalSubset, orderedInterval, Fin.sum_univ_succ]

theorem compactCertificate259_coefficient1 :
    compactCertificate259.coefficientCheck (1 : Fin 5) = true := by
  norm_num [CompactCertificate.coefficientCheck, intervalFinSumHull,
    compactCertificate259, rationalIntervalSubset, orderedInterval, Fin.sum_univ_succ]

theorem compactCertificate259_coefficient2 :
    compactCertificate259.coefficientCheck (2 : Fin 5) = true := by
  norm_num [CompactCertificate.coefficientCheck, intervalFinSumHull,
    compactCertificate259, rationalIntervalSubset, orderedInterval, Fin.sum_univ_succ]

theorem compactCertificate259_coefficient3 :
    compactCertificate259.coefficientCheck (3 : Fin 5) = true := by
  norm_num [CompactCertificate.coefficientCheck, intervalFinSumHull,
    compactCertificate259, rationalIntervalSubset, orderedInterval, Fin.sum_univ_succ]

theorem compactCertificate259_coefficient4 :
    compactCertificate259.coefficientCheck (4 : Fin 5) = true := by
  norm_num [CompactCertificate.coefficientCheck, intervalFinSumHull,
    compactCertificate259, rationalIntervalSubset, orderedInterval, Fin.sum_univ_succ]

theorem compactCertificate259_coefficients : ∀ r : Fin 5,
    compactCertificate259.coefficientCheck r = true := by
  intro r
  fin_cases r
  · exact compactCertificate259_coefficient0
  · exact compactCertificate259_coefficient1
  · exact compactCertificate259_coefficient2
  · exact compactCertificate259_coefficient3
  · exact compactCertificate259_coefficient4

theorem compactCertificate259_lower : (1 : ℚ) ≤ compactCertificate259.output.lo := by
  norm_num [CompactCertificate.output, CompactCertificate.interval,
    CompactCertificate.coefficientTargetNat, compactCertificate259, dualConstant,
    intervalTaylorSum, intervalPow, intervalSub, intervalMaxAbs, widenInterval,
    rationalErrorInterval, orderedInterval, IntervalRat.add, IntervalRat.mul, IntervalRat.scale,
    IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4]

theorem compactCertificate259_proves {t : ℝ} (ht : t ∈ compactCertificate259.interval) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t :=
  compactCertificate259.proves compactCertificate259_states compactCertificate259_chunks
    compactCertificate259_coefficients compactCertificate259_lower ht

end Erdos232
