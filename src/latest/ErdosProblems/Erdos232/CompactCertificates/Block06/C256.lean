/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, OpenAI Codex
-/
import ErdosProblems.Erdos232.CompactBase

open LeanCert.Core
namespace Erdos232

def compactCertificate256 : CompactCertificate where
  left := 131
  right := 132
  center := 263 / 2
  grid := fun i =>
    match i.val with
    | 0 => 42
    | 1 => 31
    | 2 => 50
    | 3 => 9
    | 4 => 24
    | 5 => 66
    | 6 => 48
    | 7 => 83
    | 8 => 61
    | 9 => 94
    | 10 => 54
    | 11 => 96
    | 12 => 90
    | 13 => 64
    | 14 => 73
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
    | 25 => 78
    | _ => 52
  point := fun i =>
    match i.val with
    | 0 => 263 / 2
    | 1 => 387449219297963 / 4000000000000
    | 2 => 125293116874379 / 800000000000
    | 3 => 113056715879041 / 4000000000000
    | 4 => 303686241593677 / 4000000000000
    | 5 => 824567221314009 / 4000000000000
    | 6 => 607372483187617 / 4000000000000
    | 7 => 1040743102274341 / 4000000000000
    | 8 => 766606658679919 / 4000000000000
    | 9 => 1176171756164737 / 4000000000000
    | 10 => 679063080034873 / 4000000000000
    | 11 => 1205009351940557 / 4000000000000
    | 12 => 1125876046284833 / 4000000000000
    | 13 => 803478271848689 / 4000000000000
    | 14 => 911058724781031 / 4000000000000
    | 15 => 759545782075639 / 4000000000000
    | 16 => 671081733176419 / 4000000000000
    | 17 => 194505642941481 / 800000000000
    | 18 => 538012844647307 / 4000000000000
    | 19 => 456079446736627 / 4000000000000
    | 20 => 285393341320081 / 4000000000000
    | 21 => 153485488137327 / 4000000000000
    | 22 => 416742957472981 / 4000000000000
    | 23 => 569026879978037 / 4000000000000
    | 24 => 240606658679919 / 4000000000000
    | 25 => 978052709451599 / 4000000000000
    | _ => 653293882976641 / 4000000000000
  state := fun i =>
    match i.val with
    | 0 => (orderedInterval (23043187807 / 1000000000000) (23043187808 / 1000000000000), orderedInterval (65564907847 / 1000000000000) (65564907848 / 1000000000000))
    | 1 => (orderedInterval (-20609532368 / 1000000000000) (-20609532367 / 1000000000000), orderedInterval (-78301165508 / 1000000000000) (-78301165507 / 1000000000000))
    | 2 => (orderedInterval (20137969760 / 1000000000000) (20137969761 / 1000000000000), orderedInterval (60427969944 / 1000000000000) (60427969945 / 1000000000000))
    | 3 => (orderedInterval (-104556283432 / 1000000000000) (-104556283431 / 1000000000000), orderedInterval (-105817076639 / 1000000000000) (-105817076638 / 1000000000000))
    | 4 => (orderedInterval (88404352715 / 1000000000000) (88404352716 / 1000000000000), orderedInterval (23287120977 / 1000000000000) (23287120978 / 1000000000000))
    | 5 => (orderedInterval (-22584859103 / 1000000000000) (-22584858017 / 1000000000000), orderedInterval (50830674955 / 1000000000000) (50830676041 / 1000000000000))
    | 6 => (orderedInterval (62566442370 / 1000000000000) (62566443824 / 1000000000000), orderedInterval (-16880422937 / 1000000000000) (-16880421483 / 1000000000000))
    | 7 => (orderedInterval (-10722451732 / 1000000000000) (-10722451731 / 1000000000000), orderedInterval (-48268341932 / 1000000000000) (-48268341931 / 1000000000000))
    | 8 => (orderedInterval (-41314730872 / 1000000000000) (-41314730871 / 1000000000000), orderedInterval (-40077375709 / 1000000000000) (-40077375708 / 1000000000000))
    | 9 => (orderedInterval (-21560795872 / 1000000000000) (-21560794516 / 1000000000000), orderedInterval (41270035018 / 1000000000000) (41270036373 / 1000000000000))
    | 10 => (orderedInterval (48136711946 / 1000000000000) (48136711947 / 1000000000000), orderedInterval (37711128682 / 1000000000000) (37711128683 / 1000000000000))
    | 11 => (orderedInterval (19764350164 / 1000000000000) (19764350165 / 1000000000000), orderedInterval (41471612492 / 1000000000000) (41471612493 / 1000000000000))
    | 12 => (orderedInterval (-22355763282 / 1000000000000) (-22355761690 / 1000000000000), orderedInterval (42015866606 / 1000000000000) (42015868198 / 1000000000000))
    | 13 => (orderedInterval (31434078678 / 1000000000000) (31434078679 / 1000000000000), orderedInterval (46625305280 / 1000000000000) (46625305281 / 1000000000000))
    | 14 => (orderedInterval (37433471393 / 1000000000000) (37433513583 / 1000000000000), orderedInterval (-37415965271 / 1000000000000) (-37415923080 / 1000000000000))
    | 15 => (orderedInterval (47629954128 / 1000000000000) (47630009680 / 1000000000000), orderedInterval (-33049821455 / 1000000000000) (-33049765904 / 1000000000000))
    | 16 => (orderedInterval (-54642408482 / 1000000000000) (-54642392526 / 1000000000000), orderedInterval (28602018884 / 1000000000000) (28602034840 / 1000000000000))
    | 17 => (orderedInterval (-46219755567 / 1000000000000) (-46219739361 / 1000000000000), orderedInterval (22052795629 / 1000000000000) (22052811836 / 1000000000000))
    | 18 => (orderedInterval (-13613718409 / 1000000000000) (-13613718408 / 1000000000000), orderedInterval (-67386892625 / 1000000000000) (-67386892624 / 1000000000000))
    | 19 => (orderedInterval (74031582686 / 1000000000000) (74031582934 / 1000000000000), orderedInterval (-10457960447 / 1000000000000) (-10457960200 / 1000000000000))
    | 20 => (orderedInterval (11743769745 / 1000000000000) (11743769800 / 1000000000000), orderedInterval (-93810603571 / 1000000000000) (-93810603516 / 1000000000000))
    | 21 => (orderedInterval (127929138851 / 1000000000000) (127929138855 / 1000000000000), orderedInterval (13292416241 / 1000000000000) (13292416245 / 1000000000000))
    | 22 => (orderedInterval (-75265145394 / 1000000000000) (-75265145393 / 1000000000000), orderedInterval (-20746354917 / 1000000000000) (-20746354916 / 1000000000000))
    | 23 => (orderedInterval (-66570271477 / 1000000000000) (-66570271296 / 1000000000000), orderedInterval (6830879919 / 1000000000000) (6830880100 / 1000000000000))
    | 24 => (orderedInterval (-97454059352 / 1000000000000) (-97454059351 / 1000000000000), orderedInterval (-32144391468 / 1000000000000) (-32144391467 / 1000000000000))
    | 25 => (orderedInterval (12813567555 / 1000000000000) (12813567556 / 1000000000000), orderedInterval (49364472846 / 1000000000000) (49364472847 / 1000000000000))
    | _ => (orderedInterval (42340971440 / 1000000000000) (42340971441 / 1000000000000), orderedInterval (45752303206 / 1000000000000) (45752303207 / 1000000000000))
  chunkTarget := fun r b =>
    match r.val with
    | 0 =>
      match b.val with
      | 0 => orderedInterval (10123191132 / 1000000000000) (10123191143 / 1000000000000)
      | 1 => orderedInterval (5967708257 / 1000000000000) (5967708350 / 1000000000000)
      | 2 => orderedInterval (-667772223 / 1000000000000) (-667772215 / 1000000000000)
      | 3 => orderedInterval (10207245900 / 1000000000000) (10207246194 / 1000000000000)
      | 4 => orderedInterval (3186651910 / 1000000000000) (3186652168 / 1000000000000)
      | 5 => orderedInterval (2493609223 / 1000000000000) (2493611206 / 1000000000000)
      | 6 => orderedInterval (-1631132066 / 1000000000000) (-1631132016 / 1000000000000)
      | 7 => orderedInterval (4447173810 / 1000000000000) (4447173840 / 1000000000000)
      | _ => orderedInterval (-9574821643 / 1000000000000) (-9574821606 / 1000000000000)
    | 1 =>
      match b.val with
      | 0 => orderedInterval (29673465114 / 1000000000000) (29673465125 / 1000000000000)
      | 1 => orderedInterval (-4926992741 / 1000000000000) (-4926992601 / 1000000000000)
      | 2 => orderedInterval (1534065155 / 1000000000000) (1534065169 / 1000000000000)
      | 3 => orderedInterval (715446810 / 1000000000000) (715447458 / 1000000000000)
      | 4 => orderedInterval (5439285395 / 1000000000000) (5439285852 / 1000000000000)
      | 5 => orderedInterval (-1595396582 / 1000000000000) (-1595393704 / 1000000000000)
      | 6 => orderedInterval (9876930702 / 1000000000000) (9876930747 / 1000000000000)
      | 7 => orderedInterval (-265049277 / 1000000000000) (-265049247 / 1000000000000)
      | _ => orderedInterval (-18222221278 / 1000000000000) (-18222221226 / 1000000000000)
    | 2 =>
      match b.val with
      | 0 => orderedInterval (-10931214300 / 1000000000000) (-10931214287 / 1000000000000)
      | 1 => orderedInterval (-5036390741 / 1000000000000) (-5036390525 / 1000000000000)
      | 2 => orderedInterval (814498683 / 1000000000000) (814498707 / 1000000000000)
      | 3 => orderedInterval (-39850536566 / 1000000000000) (-39850535124 / 1000000000000)
      | 4 => orderedInterval (-8257942343 / 1000000000000) (-8257941524 / 1000000000000)
      | 5 => orderedInterval (-2179157279 / 1000000000000) (-2179152987 / 1000000000000)
      | 6 => orderedInterval (685282276 / 1000000000000) (685282317 / 1000000000000)
      | 7 => orderedInterval (-6839375139 / 1000000000000) (-6839375108 / 1000000000000)
      | _ => orderedInterval (16122402161 / 1000000000000) (16122402238 / 1000000000000)
    | 3 =>
      match b.val with
      | 0 => orderedInterval (-31601804505 / 1000000000000) (-31601804490 / 1000000000000)
      | 1 => orderedInterval (13783430137 / 1000000000000) (13783430473 / 1000000000000)
      | 2 => orderedInterval (-8539675309 / 1000000000000) (-8539675267 / 1000000000000)
      | 3 => orderedInterval (5397701924 / 1000000000000) (5397705135 / 1000000000000)
      | 4 => orderedInterval (-9197114685 / 1000000000000) (-9197113215 / 1000000000000)
      | 5 => orderedInterval (995922220 / 1000000000000) (995928745 / 1000000000000)
      | 6 => orderedInterval (-11432552402 / 1000000000000) (-11432552363 / 1000000000000)
      | 7 => orderedInterval (486789707 / 1000000000000) (486789740 / 1000000000000)
      | _ => orderedInterval (42174658547 / 1000000000000) (42174658665 / 1000000000000)
    | _ =>
      match b.val with
      | 0 => orderedInterval (11934686332 / 1000000000000) (11934686349 / 1000000000000)
      | 1 => orderedInterval (9846971715 / 1000000000000) (9846972243 / 1000000000000)
      | 2 => orderedInterval (693633946 / 1000000000000) (693634024 / 1000000000000)
      | 3 => orderedInterval (182986620323 / 1000000000000) (182986627519 / 1000000000000)
      | 4 => orderedInterval (23089575202 / 1000000000000) (23089577873 / 1000000000000)
      | 5 => orderedInterval (-3168314684 / 1000000000000) (-3168304462 / 1000000000000)
      | 6 => orderedInterval (221159871 / 1000000000000) (221159908 / 1000000000000)
      | 7 => orderedInterval (7635326197 / 1000000000000) (7635326232 / 1000000000000)
      | _ => orderedInterval (-32038283716 / 1000000000000) (-32038283526 / 1000000000000)
  coefficientTarget := fun i =>
    match i.val with
    | 0 => orderedInterval (24551854300 / 1000000000000) (24551857064 / 1000000000000)
    | 1 => orderedInterval (22229533298 / 1000000000000) (22229537573 / 1000000000000)
    | 2 => orderedInterval (-55472433248 / 1000000000000) (-55472426293 / 1000000000000)
    | 3 => orderedInterval (2067355634 / 1000000000000) (2067367423 / 1000000000000)
    | _ => orderedInterval (201201375186 / 1000000000000) (201201396160 / 1000000000000)

theorem compactCertificate256_stateChecks0 :
    compactCertificate256.stateChecks 0 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 42 12 (263 / 2)) (orderedInterval (23043187807 / 1000000000000) (23043187808 / 1000000000000), orderedInterval (65564907847 / 1000000000000) (65564907848 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 31 12 (387449219297963 / 4000000000000)) (orderedInterval (-20609532368 / 1000000000000) (-20609532367 / 1000000000000), orderedInterval (-78301165508 / 1000000000000) (-78301165507 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 50 12 (125293116874379 / 800000000000)) (orderedInterval (20137969760 / 1000000000000) (20137969761 / 1000000000000), orderedInterval (60427969944 / 1000000000000) (60427969945 / 1000000000000))) = true
  norm_num [besselStateAtRationalPoint, besselIntervalStepZero,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, besselZeroTransition,
    besselInitial, besselGridStateAt, besselGridStateBlock00, besselGridStateBlock01,
    besselGridStateBlock02, besselGridStateBlock03, besselGridStateBlock04,
    besselGridStateBlock05, besselGridStateBlock06, besselGridStateBlock07,
    besselGridStateBlock08, besselGridStateBlock09, besselGridStateBlock10,
    besselGridStateBlock11, besselGridStateBlock12, besselGridStateBlock13,
    besselGridStateBlock14, besselGridState009, besselGridState012, besselGridState019, besselGridState023, besselGridState024, besselGridState031, besselGridState033, besselGridState036, besselGridState042, besselGridState043, besselGridState045, besselGridState048, besselGridState050, besselGridState052, besselGridState053, besselGridState054, besselGridState060, besselGridState061, besselGridState064, besselGridState066, besselGridState073, besselGridState077, besselGridState078, besselGridState083, besselGridState090, besselGridState094, besselGridState096, besselStateSubset, linearInterval, widenInterval,
    rationalErrorInterval, rationalIntervalSubset, orderedInterval, Finset.sum_range_succ,
    IntervalRat.add, IntervalRat.mul, IntervalRat.scale, IntervalRat.singleton]

theorem compactCertificate256_stateChecks1 :
    compactCertificate256.stateChecks 3 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 9 12 (113056715879041 / 4000000000000)) (orderedInterval (-104556283432 / 1000000000000) (-104556283431 / 1000000000000), orderedInterval (-105817076639 / 1000000000000) (-105817076638 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 24 12 (303686241593677 / 4000000000000)) (orderedInterval (88404352715 / 1000000000000) (88404352716 / 1000000000000), orderedInterval (23287120977 / 1000000000000) (23287120978 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 66 12 (824567221314009 / 4000000000000)) (orderedInterval (-22584859103 / 1000000000000) (-22584858017 / 1000000000000), orderedInterval (50830674955 / 1000000000000) (50830676041 / 1000000000000))) = true
  norm_num [besselStateAtRationalPoint, besselIntervalStepZero,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, besselZeroTransition,
    besselInitial, besselGridStateAt, besselGridStateBlock00, besselGridStateBlock01,
    besselGridStateBlock02, besselGridStateBlock03, besselGridStateBlock04,
    besselGridStateBlock05, besselGridStateBlock06, besselGridStateBlock07,
    besselGridStateBlock08, besselGridStateBlock09, besselGridStateBlock10,
    besselGridStateBlock11, besselGridStateBlock12, besselGridStateBlock13,
    besselGridStateBlock14, besselGridState009, besselGridState012, besselGridState019, besselGridState023, besselGridState024, besselGridState031, besselGridState033, besselGridState036, besselGridState042, besselGridState043, besselGridState045, besselGridState048, besselGridState050, besselGridState052, besselGridState053, besselGridState054, besselGridState060, besselGridState061, besselGridState064, besselGridState066, besselGridState073, besselGridState077, besselGridState078, besselGridState083, besselGridState090, besselGridState094, besselGridState096, besselStateSubset, linearInterval, widenInterval,
    rationalErrorInterval, rationalIntervalSubset, orderedInterval, Finset.sum_range_succ,
    IntervalRat.add, IntervalRat.mul, IntervalRat.scale, IntervalRat.singleton]

theorem compactCertificate256_stateChecks2 :
    compactCertificate256.stateChecks 6 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 48 12 (607372483187617 / 4000000000000)) (orderedInterval (62566442370 / 1000000000000) (62566443824 / 1000000000000), orderedInterval (-16880422937 / 1000000000000) (-16880421483 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 83 12 (1040743102274341 / 4000000000000)) (orderedInterval (-10722451732 / 1000000000000) (-10722451731 / 1000000000000), orderedInterval (-48268341932 / 1000000000000) (-48268341931 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 61 12 (766606658679919 / 4000000000000)) (orderedInterval (-41314730872 / 1000000000000) (-41314730871 / 1000000000000), orderedInterval (-40077375709 / 1000000000000) (-40077375708 / 1000000000000))) = true
  norm_num [besselStateAtRationalPoint, besselIntervalStepZero,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, besselZeroTransition,
    besselInitial, besselGridStateAt, besselGridStateBlock00, besselGridStateBlock01,
    besselGridStateBlock02, besselGridStateBlock03, besselGridStateBlock04,
    besselGridStateBlock05, besselGridStateBlock06, besselGridStateBlock07,
    besselGridStateBlock08, besselGridStateBlock09, besselGridStateBlock10,
    besselGridStateBlock11, besselGridStateBlock12, besselGridStateBlock13,
    besselGridStateBlock14, besselGridState009, besselGridState012, besselGridState019, besselGridState023, besselGridState024, besselGridState031, besselGridState033, besselGridState036, besselGridState042, besselGridState043, besselGridState045, besselGridState048, besselGridState050, besselGridState052, besselGridState053, besselGridState054, besselGridState060, besselGridState061, besselGridState064, besselGridState066, besselGridState073, besselGridState077, besselGridState078, besselGridState083, besselGridState090, besselGridState094, besselGridState096, besselStateSubset, linearInterval, widenInterval,
    rationalErrorInterval, rationalIntervalSubset, orderedInterval, Finset.sum_range_succ,
    IntervalRat.add, IntervalRat.mul, IntervalRat.scale, IntervalRat.singleton]

theorem compactCertificate256_stateChecks3 :
    compactCertificate256.stateChecks 9 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 94 12 (1176171756164737 / 4000000000000)) (orderedInterval (-21560795872 / 1000000000000) (-21560794516 / 1000000000000), orderedInterval (41270035018 / 1000000000000) (41270036373 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 54 12 (679063080034873 / 4000000000000)) (orderedInterval (48136711946 / 1000000000000) (48136711947 / 1000000000000), orderedInterval (37711128682 / 1000000000000) (37711128683 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 96 12 (1205009351940557 / 4000000000000)) (orderedInterval (19764350164 / 1000000000000) (19764350165 / 1000000000000), orderedInterval (41471612492 / 1000000000000) (41471612493 / 1000000000000))) = true
  norm_num [besselStateAtRationalPoint, besselIntervalStepZero,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, besselZeroTransition,
    besselInitial, besselGridStateAt, besselGridStateBlock00, besselGridStateBlock01,
    besselGridStateBlock02, besselGridStateBlock03, besselGridStateBlock04,
    besselGridStateBlock05, besselGridStateBlock06, besselGridStateBlock07,
    besselGridStateBlock08, besselGridStateBlock09, besselGridStateBlock10,
    besselGridStateBlock11, besselGridStateBlock12, besselGridStateBlock13,
    besselGridStateBlock14, besselGridState009, besselGridState012, besselGridState019, besselGridState023, besselGridState024, besselGridState031, besselGridState033, besselGridState036, besselGridState042, besselGridState043, besselGridState045, besselGridState048, besselGridState050, besselGridState052, besselGridState053, besselGridState054, besselGridState060, besselGridState061, besselGridState064, besselGridState066, besselGridState073, besselGridState077, besselGridState078, besselGridState083, besselGridState090, besselGridState094, besselGridState096, besselStateSubset, linearInterval, widenInterval,
    rationalErrorInterval, rationalIntervalSubset, orderedInterval, Finset.sum_range_succ,
    IntervalRat.add, IntervalRat.mul, IntervalRat.scale, IntervalRat.singleton]

theorem compactCertificate256_stateChecks4 :
    compactCertificate256.stateChecks 12 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 90 12 (1125876046284833 / 4000000000000)) (orderedInterval (-22355763282 / 1000000000000) (-22355761690 / 1000000000000), orderedInterval (42015866606 / 1000000000000) (42015868198 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 64 12 (803478271848689 / 4000000000000)) (orderedInterval (31434078678 / 1000000000000) (31434078679 / 1000000000000), orderedInterval (46625305280 / 1000000000000) (46625305281 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 73 12 (911058724781031 / 4000000000000)) (orderedInterval (37433471393 / 1000000000000) (37433513583 / 1000000000000), orderedInterval (-37415965271 / 1000000000000) (-37415923080 / 1000000000000))) = true
  norm_num [besselStateAtRationalPoint, besselIntervalStepZero,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, besselZeroTransition,
    besselInitial, besselGridStateAt, besselGridStateBlock00, besselGridStateBlock01,
    besselGridStateBlock02, besselGridStateBlock03, besselGridStateBlock04,
    besselGridStateBlock05, besselGridStateBlock06, besselGridStateBlock07,
    besselGridStateBlock08, besselGridStateBlock09, besselGridStateBlock10,
    besselGridStateBlock11, besselGridStateBlock12, besselGridStateBlock13,
    besselGridStateBlock14, besselGridState009, besselGridState012, besselGridState019, besselGridState023, besselGridState024, besselGridState031, besselGridState033, besselGridState036, besselGridState042, besselGridState043, besselGridState045, besselGridState048, besselGridState050, besselGridState052, besselGridState053, besselGridState054, besselGridState060, besselGridState061, besselGridState064, besselGridState066, besselGridState073, besselGridState077, besselGridState078, besselGridState083, besselGridState090, besselGridState094, besselGridState096, besselStateSubset, linearInterval, widenInterval,
    rationalErrorInterval, rationalIntervalSubset, orderedInterval, Finset.sum_range_succ,
    IntervalRat.add, IntervalRat.mul, IntervalRat.scale, IntervalRat.singleton]

theorem compactCertificate256_stateChecks5 :
    compactCertificate256.stateChecks 15 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 60 12 (759545782075639 / 4000000000000)) (orderedInterval (47629954128 / 1000000000000) (47630009680 / 1000000000000), orderedInterval (-33049821455 / 1000000000000) (-33049765904 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 53 12 (671081733176419 / 4000000000000)) (orderedInterval (-54642408482 / 1000000000000) (-54642392526 / 1000000000000), orderedInterval (28602018884 / 1000000000000) (28602034840 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 77 12 (194505642941481 / 800000000000)) (orderedInterval (-46219755567 / 1000000000000) (-46219739361 / 1000000000000), orderedInterval (22052795629 / 1000000000000) (22052811836 / 1000000000000))) = true
  norm_num [besselStateAtRationalPoint, besselIntervalStepZero,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, besselZeroTransition,
    besselInitial, besselGridStateAt, besselGridStateBlock00, besselGridStateBlock01,
    besselGridStateBlock02, besselGridStateBlock03, besselGridStateBlock04,
    besselGridStateBlock05, besselGridStateBlock06, besselGridStateBlock07,
    besselGridStateBlock08, besselGridStateBlock09, besselGridStateBlock10,
    besselGridStateBlock11, besselGridStateBlock12, besselGridStateBlock13,
    besselGridStateBlock14, besselGridState009, besselGridState012, besselGridState019, besselGridState023, besselGridState024, besselGridState031, besselGridState033, besselGridState036, besselGridState042, besselGridState043, besselGridState045, besselGridState048, besselGridState050, besselGridState052, besselGridState053, besselGridState054, besselGridState060, besselGridState061, besselGridState064, besselGridState066, besselGridState073, besselGridState077, besselGridState078, besselGridState083, besselGridState090, besselGridState094, besselGridState096, besselStateSubset, linearInterval, widenInterval,
    rationalErrorInterval, rationalIntervalSubset, orderedInterval, Finset.sum_range_succ,
    IntervalRat.add, IntervalRat.mul, IntervalRat.scale, IntervalRat.singleton]

theorem compactCertificate256_stateChecks6 :
    compactCertificate256.stateChecks 18 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 43 12 (538012844647307 / 4000000000000)) (orderedInterval (-13613718409 / 1000000000000) (-13613718408 / 1000000000000), orderedInterval (-67386892625 / 1000000000000) (-67386892624 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 36 12 (456079446736627 / 4000000000000)) (orderedInterval (74031582686 / 1000000000000) (74031582934 / 1000000000000), orderedInterval (-10457960447 / 1000000000000) (-10457960200 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 23 12 (285393341320081 / 4000000000000)) (orderedInterval (11743769745 / 1000000000000) (11743769800 / 1000000000000), orderedInterval (-93810603571 / 1000000000000) (-93810603516 / 1000000000000))) = true
  norm_num [besselStateAtRationalPoint, besselIntervalStepZero,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, besselZeroTransition,
    besselInitial, besselGridStateAt, besselGridStateBlock00, besselGridStateBlock01,
    besselGridStateBlock02, besselGridStateBlock03, besselGridStateBlock04,
    besselGridStateBlock05, besselGridStateBlock06, besselGridStateBlock07,
    besselGridStateBlock08, besselGridStateBlock09, besselGridStateBlock10,
    besselGridStateBlock11, besselGridStateBlock12, besselGridStateBlock13,
    besselGridStateBlock14, besselGridState009, besselGridState012, besselGridState019, besselGridState023, besselGridState024, besselGridState031, besselGridState033, besselGridState036, besselGridState042, besselGridState043, besselGridState045, besselGridState048, besselGridState050, besselGridState052, besselGridState053, besselGridState054, besselGridState060, besselGridState061, besselGridState064, besselGridState066, besselGridState073, besselGridState077, besselGridState078, besselGridState083, besselGridState090, besselGridState094, besselGridState096, besselStateSubset, linearInterval, widenInterval,
    rationalErrorInterval, rationalIntervalSubset, orderedInterval, Finset.sum_range_succ,
    IntervalRat.add, IntervalRat.mul, IntervalRat.scale, IntervalRat.singleton]

theorem compactCertificate256_stateChecks7 :
    compactCertificate256.stateChecks 21 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 12 12 (153485488137327 / 4000000000000)) (orderedInterval (127929138851 / 1000000000000) (127929138855 / 1000000000000), orderedInterval (13292416241 / 1000000000000) (13292416245 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 33 12 (416742957472981 / 4000000000000)) (orderedInterval (-75265145394 / 1000000000000) (-75265145393 / 1000000000000), orderedInterval (-20746354917 / 1000000000000) (-20746354916 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 45 12 (569026879978037 / 4000000000000)) (orderedInterval (-66570271477 / 1000000000000) (-66570271296 / 1000000000000), orderedInterval (6830879919 / 1000000000000) (6830880100 / 1000000000000))) = true
  norm_num [besselStateAtRationalPoint, besselIntervalStepZero,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, besselZeroTransition,
    besselInitial, besselGridStateAt, besselGridStateBlock00, besselGridStateBlock01,
    besselGridStateBlock02, besselGridStateBlock03, besselGridStateBlock04,
    besselGridStateBlock05, besselGridStateBlock06, besselGridStateBlock07,
    besselGridStateBlock08, besselGridStateBlock09, besselGridStateBlock10,
    besselGridStateBlock11, besselGridStateBlock12, besselGridStateBlock13,
    besselGridStateBlock14, besselGridState009, besselGridState012, besselGridState019, besselGridState023, besselGridState024, besselGridState031, besselGridState033, besselGridState036, besselGridState042, besselGridState043, besselGridState045, besselGridState048, besselGridState050, besselGridState052, besselGridState053, besselGridState054, besselGridState060, besselGridState061, besselGridState064, besselGridState066, besselGridState073, besselGridState077, besselGridState078, besselGridState083, besselGridState090, besselGridState094, besselGridState096, besselStateSubset, linearInterval, widenInterval,
    rationalErrorInterval, rationalIntervalSubset, orderedInterval, Finset.sum_range_succ,
    IntervalRat.add, IntervalRat.mul, IntervalRat.scale, IntervalRat.singleton]

theorem compactCertificate256_stateChecks8 :
    compactCertificate256.stateChecks 24 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 19 12 (240606658679919 / 4000000000000)) (orderedInterval (-97454059352 / 1000000000000) (-97454059351 / 1000000000000), orderedInterval (-32144391468 / 1000000000000) (-32144391467 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 78 12 (978052709451599 / 4000000000000)) (orderedInterval (12813567555 / 1000000000000) (12813567556 / 1000000000000), orderedInterval (49364472846 / 1000000000000) (49364472847 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 52 12 (653293882976641 / 4000000000000)) (orderedInterval (42340971440 / 1000000000000) (42340971441 / 1000000000000), orderedInterval (45752303206 / 1000000000000) (45752303207 / 1000000000000))) = true
  norm_num [besselStateAtRationalPoint, besselIntervalStepZero,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, besselZeroTransition,
    besselInitial, besselGridStateAt, besselGridStateBlock00, besselGridStateBlock01,
    besselGridStateBlock02, besselGridStateBlock03, besselGridStateBlock04,
    besselGridStateBlock05, besselGridStateBlock06, besselGridStateBlock07,
    besselGridStateBlock08, besselGridStateBlock09, besselGridStateBlock10,
    besselGridStateBlock11, besselGridStateBlock12, besselGridStateBlock13,
    besselGridStateBlock14, besselGridState009, besselGridState012, besselGridState019, besselGridState023, besselGridState024, besselGridState031, besselGridState033, besselGridState036, besselGridState042, besselGridState043, besselGridState045, besselGridState048, besselGridState050, besselGridState052, besselGridState053, besselGridState054, besselGridState060, besselGridState061, besselGridState064, besselGridState066, besselGridState073, besselGridState077, besselGridState078, besselGridState083, besselGridState090, besselGridState094, besselGridState096, besselStateSubset, linearInterval, widenInterval,
    rationalErrorInterval, rationalIntervalSubset, orderedInterval, Finset.sum_range_succ,
    IntervalRat.add, IntervalRat.mul, IntervalRat.scale, IntervalRat.singleton]

theorem compactCertificate256_states : ∀ j,
    BesselStateValid (compactCertificate256.point j) (compactCertificate256.state j) :=
  compactCertificate256.statesValid_of_checks3 compactCertificate256_stateChecks0
    compactCertificate256_stateChecks1 compactCertificate256_stateChecks2
    compactCertificate256_stateChecks3 compactCertificate256_stateChecks4
    compactCertificate256_stateChecks5 compactCertificate256_stateChecks6
    compactCertificate256_stateChecks7 compactCertificate256_stateChecks8

theorem compactCertificate256_chunkChecks0_0 :
    compactCertificate256.chunkChecks (0 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 0) <| besselDerivativeNearFromState (263 / 2) 0 (IntervalRat.scale (263 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (23043187807 / 1000000000000) (23043187808 / 1000000000000), orderedInterval (65564907847 / 1000000000000) (65564907848 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 0) <| besselDerivativeNearFromState (387449219297963 / 4000000000000) 0 (IntervalRat.scale (263 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-20609532368 / 1000000000000) (-20609532367 / 1000000000000), orderedInterval (-78301165508 / 1000000000000) (-78301165507 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 0) <| besselDerivativeNearFromState (125293116874379 / 800000000000) 0 (IntervalRat.scale (263 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (20137969760 / 1000000000000) (20137969761 / 1000000000000), orderedInterval (60427969944 / 1000000000000) (60427969945 / 1000000000000)))) (orderedInterval (10123191132 / 1000000000000) (10123191143 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 0) <| besselDerivativeNearFromState (113056715879041 / 4000000000000) 0 (IntervalRat.scale (263 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-104556283432 / 1000000000000) (-104556283431 / 1000000000000), orderedInterval (-105817076639 / 1000000000000) (-105817076638 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 0) <| besselDerivativeNearFromState (303686241593677 / 4000000000000) 0 (IntervalRat.scale (263 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (88404352715 / 1000000000000) (88404352716 / 1000000000000), orderedInterval (23287120977 / 1000000000000) (23287120978 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 0) <| besselDerivativeNearFromState (824567221314009 / 4000000000000) 0 (IntervalRat.scale (263 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-22584859103 / 1000000000000) (-22584858017 / 1000000000000), orderedInterval (50830674955 / 1000000000000) (50830676041 / 1000000000000)))) (orderedInterval (5967708257 / 1000000000000) (5967708350 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 0) <| besselDerivativeNearFromState (607372483187617 / 4000000000000) 0 (IntervalRat.scale (263 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (62566442370 / 1000000000000) (62566443824 / 1000000000000), orderedInterval (-16880422937 / 1000000000000) (-16880421483 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 0) <| besselDerivativeNearFromState (1040743102274341 / 4000000000000) 0 (IntervalRat.scale (263 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-10722451732 / 1000000000000) (-10722451731 / 1000000000000), orderedInterval (-48268341932 / 1000000000000) (-48268341931 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 0) <| besselDerivativeNearFromState (766606658679919 / 4000000000000) 0 (IntervalRat.scale (263 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-41314730872 / 1000000000000) (-41314730871 / 1000000000000), orderedInterval (-40077375709 / 1000000000000) (-40077375708 / 1000000000000)))) (orderedInterval (-667772223 / 1000000000000) (-667772215 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate256_chunkChecks0_1 :
    compactCertificate256.chunkChecks (0 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 0) <| besselDerivativeNearFromState (1176171756164737 / 4000000000000) 0 (IntervalRat.scale (263 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-21560795872 / 1000000000000) (-21560794516 / 1000000000000), orderedInterval (41270035018 / 1000000000000) (41270036373 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 0) <| besselDerivativeNearFromState (679063080034873 / 4000000000000) 0 (IntervalRat.scale (263 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (48136711946 / 1000000000000) (48136711947 / 1000000000000), orderedInterval (37711128682 / 1000000000000) (37711128683 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 0) <| besselDerivativeNearFromState (1205009351940557 / 4000000000000) 0 (IntervalRat.scale (263 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (19764350164 / 1000000000000) (19764350165 / 1000000000000), orderedInterval (41471612492 / 1000000000000) (41471612493 / 1000000000000)))) (orderedInterval (10207245900 / 1000000000000) (10207246194 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 0) <| besselDerivativeNearFromState (1125876046284833 / 4000000000000) 0 (IntervalRat.scale (263 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-22355763282 / 1000000000000) (-22355761690 / 1000000000000), orderedInterval (42015866606 / 1000000000000) (42015868198 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 0) <| besselDerivativeNearFromState (803478271848689 / 4000000000000) 0 (IntervalRat.scale (263 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (31434078678 / 1000000000000) (31434078679 / 1000000000000), orderedInterval (46625305280 / 1000000000000) (46625305281 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 0) <| besselDerivativeNearFromState (911058724781031 / 4000000000000) 0 (IntervalRat.scale (263 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (37433471393 / 1000000000000) (37433513583 / 1000000000000), orderedInterval (-37415965271 / 1000000000000) (-37415923080 / 1000000000000)))) (orderedInterval (3186651910 / 1000000000000) (3186652168 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 0) <| besselDerivativeNearFromState (759545782075639 / 4000000000000) 0 (IntervalRat.scale (263 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (47629954128 / 1000000000000) (47630009680 / 1000000000000), orderedInterval (-33049821455 / 1000000000000) (-33049765904 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 0) <| besselDerivativeNearFromState (671081733176419 / 4000000000000) 0 (IntervalRat.scale (263 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-54642408482 / 1000000000000) (-54642392526 / 1000000000000), orderedInterval (28602018884 / 1000000000000) (28602034840 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 0) <| besselDerivativeNearFromState (194505642941481 / 800000000000) 0 (IntervalRat.scale (263 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-46219755567 / 1000000000000) (-46219739361 / 1000000000000), orderedInterval (22052795629 / 1000000000000) (22052811836 / 1000000000000)))) (orderedInterval (2493609223 / 1000000000000) (2493611206 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate256_chunkChecks0_2 :
    compactCertificate256.chunkChecks (0 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 0) <| besselDerivativeNearFromState (538012844647307 / 4000000000000) 0 (IntervalRat.scale (263 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-13613718409 / 1000000000000) (-13613718408 / 1000000000000), orderedInterval (-67386892625 / 1000000000000) (-67386892624 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 0) <| besselDerivativeNearFromState (456079446736627 / 4000000000000) 0 (IntervalRat.scale (263 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (74031582686 / 1000000000000) (74031582934 / 1000000000000), orderedInterval (-10457960447 / 1000000000000) (-10457960200 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 0) <| besselDerivativeNearFromState (285393341320081 / 4000000000000) 0 (IntervalRat.scale (263 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (11743769745 / 1000000000000) (11743769800 / 1000000000000), orderedInterval (-93810603571 / 1000000000000) (-93810603516 / 1000000000000)))) (orderedInterval (-1631132066 / 1000000000000) (-1631132016 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 0) <| besselDerivativeNearFromState (153485488137327 / 4000000000000) 0 (IntervalRat.scale (263 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (127929138851 / 1000000000000) (127929138855 / 1000000000000), orderedInterval (13292416241 / 1000000000000) (13292416245 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 0) <| besselDerivativeNearFromState (416742957472981 / 4000000000000) 0 (IntervalRat.scale (263 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-75265145394 / 1000000000000) (-75265145393 / 1000000000000), orderedInterval (-20746354917 / 1000000000000) (-20746354916 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 0) <| besselDerivativeNearFromState (569026879978037 / 4000000000000) 0 (IntervalRat.scale (263 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-66570271477 / 1000000000000) (-66570271296 / 1000000000000), orderedInterval (6830879919 / 1000000000000) (6830880100 / 1000000000000)))) (orderedInterval (4447173810 / 1000000000000) (4447173840 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 0) <| besselDerivativeNearFromState (240606658679919 / 4000000000000) 0 (IntervalRat.scale (263 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-97454059352 / 1000000000000) (-97454059351 / 1000000000000), orderedInterval (-32144391468 / 1000000000000) (-32144391467 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 0) <| besselDerivativeNearFromState (978052709451599 / 4000000000000) 0 (IntervalRat.scale (263 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (12813567555 / 1000000000000) (12813567556 / 1000000000000), orderedInterval (49364472846 / 1000000000000) (49364472847 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 0) <| besselDerivativeNearFromState (653293882976641 / 4000000000000) 0 (IntervalRat.scale (263 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (42340971440 / 1000000000000) (42340971441 / 1000000000000), orderedInterval (45752303206 / 1000000000000) (45752303207 / 1000000000000)))) (orderedInterval (-9574821643 / 1000000000000) (-9574821606 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate256_chunkChecks0 :
    compactCertificate256.chunkChecks (0 : Fin 5) 0 9 = true :=
  compactCertificate256.chunkChecks_nine_of_three (0 : Fin 5) compactCertificate256_chunkChecks0_0
    compactCertificate256_chunkChecks0_1 compactCertificate256_chunkChecks0_2

theorem compactCertificate256_chunkChecks1_0 :
    compactCertificate256.chunkChecks (1 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 1) <| besselDerivativeNearFromState (263 / 2) 1 (IntervalRat.scale (263 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (23043187807 / 1000000000000) (23043187808 / 1000000000000), orderedInterval (65564907847 / 1000000000000) (65564907848 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 1) <| besselDerivativeNearFromState (387449219297963 / 4000000000000) 1 (IntervalRat.scale (263 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-20609532368 / 1000000000000) (-20609532367 / 1000000000000), orderedInterval (-78301165508 / 1000000000000) (-78301165507 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 1) <| besselDerivativeNearFromState (125293116874379 / 800000000000) 1 (IntervalRat.scale (263 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (20137969760 / 1000000000000) (20137969761 / 1000000000000), orderedInterval (60427969944 / 1000000000000) (60427969945 / 1000000000000)))) (orderedInterval (29673465114 / 1000000000000) (29673465125 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 1) <| besselDerivativeNearFromState (113056715879041 / 4000000000000) 1 (IntervalRat.scale (263 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-104556283432 / 1000000000000) (-104556283431 / 1000000000000), orderedInterval (-105817076639 / 1000000000000) (-105817076638 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 1) <| besselDerivativeNearFromState (303686241593677 / 4000000000000) 1 (IntervalRat.scale (263 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (88404352715 / 1000000000000) (88404352716 / 1000000000000), orderedInterval (23287120977 / 1000000000000) (23287120978 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 1) <| besselDerivativeNearFromState (824567221314009 / 4000000000000) 1 (IntervalRat.scale (263 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-22584859103 / 1000000000000) (-22584858017 / 1000000000000), orderedInterval (50830674955 / 1000000000000) (50830676041 / 1000000000000)))) (orderedInterval (-4926992741 / 1000000000000) (-4926992601 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 1) <| besselDerivativeNearFromState (607372483187617 / 4000000000000) 1 (IntervalRat.scale (263 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (62566442370 / 1000000000000) (62566443824 / 1000000000000), orderedInterval (-16880422937 / 1000000000000) (-16880421483 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 1) <| besselDerivativeNearFromState (1040743102274341 / 4000000000000) 1 (IntervalRat.scale (263 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-10722451732 / 1000000000000) (-10722451731 / 1000000000000), orderedInterval (-48268341932 / 1000000000000) (-48268341931 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 1) <| besselDerivativeNearFromState (766606658679919 / 4000000000000) 1 (IntervalRat.scale (263 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-41314730872 / 1000000000000) (-41314730871 / 1000000000000), orderedInterval (-40077375709 / 1000000000000) (-40077375708 / 1000000000000)))) (orderedInterval (1534065155 / 1000000000000) (1534065169 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate256_chunkChecks1_1 :
    compactCertificate256.chunkChecks (1 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 1) <| besselDerivativeNearFromState (1176171756164737 / 4000000000000) 1 (IntervalRat.scale (263 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-21560795872 / 1000000000000) (-21560794516 / 1000000000000), orderedInterval (41270035018 / 1000000000000) (41270036373 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 1) <| besselDerivativeNearFromState (679063080034873 / 4000000000000) 1 (IntervalRat.scale (263 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (48136711946 / 1000000000000) (48136711947 / 1000000000000), orderedInterval (37711128682 / 1000000000000) (37711128683 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 1) <| besselDerivativeNearFromState (1205009351940557 / 4000000000000) 1 (IntervalRat.scale (263 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (19764350164 / 1000000000000) (19764350165 / 1000000000000), orderedInterval (41471612492 / 1000000000000) (41471612493 / 1000000000000)))) (orderedInterval (715446810 / 1000000000000) (715447458 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 1) <| besselDerivativeNearFromState (1125876046284833 / 4000000000000) 1 (IntervalRat.scale (263 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-22355763282 / 1000000000000) (-22355761690 / 1000000000000), orderedInterval (42015866606 / 1000000000000) (42015868198 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 1) <| besselDerivativeNearFromState (803478271848689 / 4000000000000) 1 (IntervalRat.scale (263 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (31434078678 / 1000000000000) (31434078679 / 1000000000000), orderedInterval (46625305280 / 1000000000000) (46625305281 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 1) <| besselDerivativeNearFromState (911058724781031 / 4000000000000) 1 (IntervalRat.scale (263 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (37433471393 / 1000000000000) (37433513583 / 1000000000000), orderedInterval (-37415965271 / 1000000000000) (-37415923080 / 1000000000000)))) (orderedInterval (5439285395 / 1000000000000) (5439285852 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 1) <| besselDerivativeNearFromState (759545782075639 / 4000000000000) 1 (IntervalRat.scale (263 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (47629954128 / 1000000000000) (47630009680 / 1000000000000), orderedInterval (-33049821455 / 1000000000000) (-33049765904 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 1) <| besselDerivativeNearFromState (671081733176419 / 4000000000000) 1 (IntervalRat.scale (263 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-54642408482 / 1000000000000) (-54642392526 / 1000000000000), orderedInterval (28602018884 / 1000000000000) (28602034840 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 1) <| besselDerivativeNearFromState (194505642941481 / 800000000000) 1 (IntervalRat.scale (263 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-46219755567 / 1000000000000) (-46219739361 / 1000000000000), orderedInterval (22052795629 / 1000000000000) (22052811836 / 1000000000000)))) (orderedInterval (-1595396582 / 1000000000000) (-1595393704 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate256_chunkChecks1_2 :
    compactCertificate256.chunkChecks (1 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 1) <| besselDerivativeNearFromState (538012844647307 / 4000000000000) 1 (IntervalRat.scale (263 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-13613718409 / 1000000000000) (-13613718408 / 1000000000000), orderedInterval (-67386892625 / 1000000000000) (-67386892624 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 1) <| besselDerivativeNearFromState (456079446736627 / 4000000000000) 1 (IntervalRat.scale (263 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (74031582686 / 1000000000000) (74031582934 / 1000000000000), orderedInterval (-10457960447 / 1000000000000) (-10457960200 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 1) <| besselDerivativeNearFromState (285393341320081 / 4000000000000) 1 (IntervalRat.scale (263 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (11743769745 / 1000000000000) (11743769800 / 1000000000000), orderedInterval (-93810603571 / 1000000000000) (-93810603516 / 1000000000000)))) (orderedInterval (9876930702 / 1000000000000) (9876930747 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 1) <| besselDerivativeNearFromState (153485488137327 / 4000000000000) 1 (IntervalRat.scale (263 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (127929138851 / 1000000000000) (127929138855 / 1000000000000), orderedInterval (13292416241 / 1000000000000) (13292416245 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 1) <| besselDerivativeNearFromState (416742957472981 / 4000000000000) 1 (IntervalRat.scale (263 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-75265145394 / 1000000000000) (-75265145393 / 1000000000000), orderedInterval (-20746354917 / 1000000000000) (-20746354916 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 1) <| besselDerivativeNearFromState (569026879978037 / 4000000000000) 1 (IntervalRat.scale (263 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-66570271477 / 1000000000000) (-66570271296 / 1000000000000), orderedInterval (6830879919 / 1000000000000) (6830880100 / 1000000000000)))) (orderedInterval (-265049277 / 1000000000000) (-265049247 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 1) <| besselDerivativeNearFromState (240606658679919 / 4000000000000) 1 (IntervalRat.scale (263 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-97454059352 / 1000000000000) (-97454059351 / 1000000000000), orderedInterval (-32144391468 / 1000000000000) (-32144391467 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 1) <| besselDerivativeNearFromState (978052709451599 / 4000000000000) 1 (IntervalRat.scale (263 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (12813567555 / 1000000000000) (12813567556 / 1000000000000), orderedInterval (49364472846 / 1000000000000) (49364472847 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 1) <| besselDerivativeNearFromState (653293882976641 / 4000000000000) 1 (IntervalRat.scale (263 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (42340971440 / 1000000000000) (42340971441 / 1000000000000), orderedInterval (45752303206 / 1000000000000) (45752303207 / 1000000000000)))) (orderedInterval (-18222221278 / 1000000000000) (-18222221226 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate256_chunkChecks1 :
    compactCertificate256.chunkChecks (1 : Fin 5) 0 9 = true :=
  compactCertificate256.chunkChecks_nine_of_three (1 : Fin 5) compactCertificate256_chunkChecks1_0
    compactCertificate256_chunkChecks1_1 compactCertificate256_chunkChecks1_2

theorem compactCertificate256_chunkChecks2_0 :
    compactCertificate256.chunkChecks (2 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 2) <| besselDerivativeNearFromState (263 / 2) 2 (IntervalRat.scale (263 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (23043187807 / 1000000000000) (23043187808 / 1000000000000), orderedInterval (65564907847 / 1000000000000) (65564907848 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 2) <| besselDerivativeNearFromState (387449219297963 / 4000000000000) 2 (IntervalRat.scale (263 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-20609532368 / 1000000000000) (-20609532367 / 1000000000000), orderedInterval (-78301165508 / 1000000000000) (-78301165507 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 2) <| besselDerivativeNearFromState (125293116874379 / 800000000000) 2 (IntervalRat.scale (263 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (20137969760 / 1000000000000) (20137969761 / 1000000000000), orderedInterval (60427969944 / 1000000000000) (60427969945 / 1000000000000)))) (orderedInterval (-10931214300 / 1000000000000) (-10931214287 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 2) <| besselDerivativeNearFromState (113056715879041 / 4000000000000) 2 (IntervalRat.scale (263 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-104556283432 / 1000000000000) (-104556283431 / 1000000000000), orderedInterval (-105817076639 / 1000000000000) (-105817076638 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 2) <| besselDerivativeNearFromState (303686241593677 / 4000000000000) 2 (IntervalRat.scale (263 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (88404352715 / 1000000000000) (88404352716 / 1000000000000), orderedInterval (23287120977 / 1000000000000) (23287120978 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 2) <| besselDerivativeNearFromState (824567221314009 / 4000000000000) 2 (IntervalRat.scale (263 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-22584859103 / 1000000000000) (-22584858017 / 1000000000000), orderedInterval (50830674955 / 1000000000000) (50830676041 / 1000000000000)))) (orderedInterval (-5036390741 / 1000000000000) (-5036390525 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 2) <| besselDerivativeNearFromState (607372483187617 / 4000000000000) 2 (IntervalRat.scale (263 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (62566442370 / 1000000000000) (62566443824 / 1000000000000), orderedInterval (-16880422937 / 1000000000000) (-16880421483 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 2) <| besselDerivativeNearFromState (1040743102274341 / 4000000000000) 2 (IntervalRat.scale (263 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-10722451732 / 1000000000000) (-10722451731 / 1000000000000), orderedInterval (-48268341932 / 1000000000000) (-48268341931 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 2) <| besselDerivativeNearFromState (766606658679919 / 4000000000000) 2 (IntervalRat.scale (263 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-41314730872 / 1000000000000) (-41314730871 / 1000000000000), orderedInterval (-40077375709 / 1000000000000) (-40077375708 / 1000000000000)))) (orderedInterval (814498683 / 1000000000000) (814498707 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate256_chunkChecks2_1 :
    compactCertificate256.chunkChecks (2 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 2) <| besselDerivativeNearFromState (1176171756164737 / 4000000000000) 2 (IntervalRat.scale (263 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-21560795872 / 1000000000000) (-21560794516 / 1000000000000), orderedInterval (41270035018 / 1000000000000) (41270036373 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 2) <| besselDerivativeNearFromState (679063080034873 / 4000000000000) 2 (IntervalRat.scale (263 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (48136711946 / 1000000000000) (48136711947 / 1000000000000), orderedInterval (37711128682 / 1000000000000) (37711128683 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 2) <| besselDerivativeNearFromState (1205009351940557 / 4000000000000) 2 (IntervalRat.scale (263 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (19764350164 / 1000000000000) (19764350165 / 1000000000000), orderedInterval (41471612492 / 1000000000000) (41471612493 / 1000000000000)))) (orderedInterval (-39850536566 / 1000000000000) (-39850535124 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 2) <| besselDerivativeNearFromState (1125876046284833 / 4000000000000) 2 (IntervalRat.scale (263 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-22355763282 / 1000000000000) (-22355761690 / 1000000000000), orderedInterval (42015866606 / 1000000000000) (42015868198 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 2) <| besselDerivativeNearFromState (803478271848689 / 4000000000000) 2 (IntervalRat.scale (263 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (31434078678 / 1000000000000) (31434078679 / 1000000000000), orderedInterval (46625305280 / 1000000000000) (46625305281 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 2) <| besselDerivativeNearFromState (911058724781031 / 4000000000000) 2 (IntervalRat.scale (263 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (37433471393 / 1000000000000) (37433513583 / 1000000000000), orderedInterval (-37415965271 / 1000000000000) (-37415923080 / 1000000000000)))) (orderedInterval (-8257942343 / 1000000000000) (-8257941524 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 2) <| besselDerivativeNearFromState (759545782075639 / 4000000000000) 2 (IntervalRat.scale (263 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (47629954128 / 1000000000000) (47630009680 / 1000000000000), orderedInterval (-33049821455 / 1000000000000) (-33049765904 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 2) <| besselDerivativeNearFromState (671081733176419 / 4000000000000) 2 (IntervalRat.scale (263 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-54642408482 / 1000000000000) (-54642392526 / 1000000000000), orderedInterval (28602018884 / 1000000000000) (28602034840 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 2) <| besselDerivativeNearFromState (194505642941481 / 800000000000) 2 (IntervalRat.scale (263 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-46219755567 / 1000000000000) (-46219739361 / 1000000000000), orderedInterval (22052795629 / 1000000000000) (22052811836 / 1000000000000)))) (orderedInterval (-2179157279 / 1000000000000) (-2179152987 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate256_chunkChecks2_2 :
    compactCertificate256.chunkChecks (2 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 2) <| besselDerivativeNearFromState (538012844647307 / 4000000000000) 2 (IntervalRat.scale (263 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-13613718409 / 1000000000000) (-13613718408 / 1000000000000), orderedInterval (-67386892625 / 1000000000000) (-67386892624 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 2) <| besselDerivativeNearFromState (456079446736627 / 4000000000000) 2 (IntervalRat.scale (263 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (74031582686 / 1000000000000) (74031582934 / 1000000000000), orderedInterval (-10457960447 / 1000000000000) (-10457960200 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 2) <| besselDerivativeNearFromState (285393341320081 / 4000000000000) 2 (IntervalRat.scale (263 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (11743769745 / 1000000000000) (11743769800 / 1000000000000), orderedInterval (-93810603571 / 1000000000000) (-93810603516 / 1000000000000)))) (orderedInterval (685282276 / 1000000000000) (685282317 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 2) <| besselDerivativeNearFromState (153485488137327 / 4000000000000) 2 (IntervalRat.scale (263 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (127929138851 / 1000000000000) (127929138855 / 1000000000000), orderedInterval (13292416241 / 1000000000000) (13292416245 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 2) <| besselDerivativeNearFromState (416742957472981 / 4000000000000) 2 (IntervalRat.scale (263 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-75265145394 / 1000000000000) (-75265145393 / 1000000000000), orderedInterval (-20746354917 / 1000000000000) (-20746354916 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 2) <| besselDerivativeNearFromState (569026879978037 / 4000000000000) 2 (IntervalRat.scale (263 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-66570271477 / 1000000000000) (-66570271296 / 1000000000000), orderedInterval (6830879919 / 1000000000000) (6830880100 / 1000000000000)))) (orderedInterval (-6839375139 / 1000000000000) (-6839375108 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 2) <| besselDerivativeNearFromState (240606658679919 / 4000000000000) 2 (IntervalRat.scale (263 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-97454059352 / 1000000000000) (-97454059351 / 1000000000000), orderedInterval (-32144391468 / 1000000000000) (-32144391467 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 2) <| besselDerivativeNearFromState (978052709451599 / 4000000000000) 2 (IntervalRat.scale (263 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (12813567555 / 1000000000000) (12813567556 / 1000000000000), orderedInterval (49364472846 / 1000000000000) (49364472847 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 2) <| besselDerivativeNearFromState (653293882976641 / 4000000000000) 2 (IntervalRat.scale (263 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (42340971440 / 1000000000000) (42340971441 / 1000000000000), orderedInterval (45752303206 / 1000000000000) (45752303207 / 1000000000000)))) (orderedInterval (16122402161 / 1000000000000) (16122402238 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate256_chunkChecks2 :
    compactCertificate256.chunkChecks (2 : Fin 5) 0 9 = true :=
  compactCertificate256.chunkChecks_nine_of_three (2 : Fin 5) compactCertificate256_chunkChecks2_0
    compactCertificate256_chunkChecks2_1 compactCertificate256_chunkChecks2_2

theorem compactCertificate256_chunkChecks3_0 :
    compactCertificate256.chunkChecks (3 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 3) <| besselDerivativeNearFromState (263 / 2) 3 (IntervalRat.scale (263 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (23043187807 / 1000000000000) (23043187808 / 1000000000000), orderedInterval (65564907847 / 1000000000000) (65564907848 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 3) <| besselDerivativeNearFromState (387449219297963 / 4000000000000) 3 (IntervalRat.scale (263 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-20609532368 / 1000000000000) (-20609532367 / 1000000000000), orderedInterval (-78301165508 / 1000000000000) (-78301165507 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 3) <| besselDerivativeNearFromState (125293116874379 / 800000000000) 3 (IntervalRat.scale (263 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (20137969760 / 1000000000000) (20137969761 / 1000000000000), orderedInterval (60427969944 / 1000000000000) (60427969945 / 1000000000000)))) (orderedInterval (-31601804505 / 1000000000000) (-31601804490 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 3) <| besselDerivativeNearFromState (113056715879041 / 4000000000000) 3 (IntervalRat.scale (263 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-104556283432 / 1000000000000) (-104556283431 / 1000000000000), orderedInterval (-105817076639 / 1000000000000) (-105817076638 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 3) <| besselDerivativeNearFromState (303686241593677 / 4000000000000) 3 (IntervalRat.scale (263 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (88404352715 / 1000000000000) (88404352716 / 1000000000000), orderedInterval (23287120977 / 1000000000000) (23287120978 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 3) <| besselDerivativeNearFromState (824567221314009 / 4000000000000) 3 (IntervalRat.scale (263 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-22584859103 / 1000000000000) (-22584858017 / 1000000000000), orderedInterval (50830674955 / 1000000000000) (50830676041 / 1000000000000)))) (orderedInterval (13783430137 / 1000000000000) (13783430473 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 3) <| besselDerivativeNearFromState (607372483187617 / 4000000000000) 3 (IntervalRat.scale (263 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (62566442370 / 1000000000000) (62566443824 / 1000000000000), orderedInterval (-16880422937 / 1000000000000) (-16880421483 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 3) <| besselDerivativeNearFromState (1040743102274341 / 4000000000000) 3 (IntervalRat.scale (263 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-10722451732 / 1000000000000) (-10722451731 / 1000000000000), orderedInterval (-48268341932 / 1000000000000) (-48268341931 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 3) <| besselDerivativeNearFromState (766606658679919 / 4000000000000) 3 (IntervalRat.scale (263 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-41314730872 / 1000000000000) (-41314730871 / 1000000000000), orderedInterval (-40077375709 / 1000000000000) (-40077375708 / 1000000000000)))) (orderedInterval (-8539675309 / 1000000000000) (-8539675267 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate256_chunkChecks3_1 :
    compactCertificate256.chunkChecks (3 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 3) <| besselDerivativeNearFromState (1176171756164737 / 4000000000000) 3 (IntervalRat.scale (263 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-21560795872 / 1000000000000) (-21560794516 / 1000000000000), orderedInterval (41270035018 / 1000000000000) (41270036373 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 3) <| besselDerivativeNearFromState (679063080034873 / 4000000000000) 3 (IntervalRat.scale (263 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (48136711946 / 1000000000000) (48136711947 / 1000000000000), orderedInterval (37711128682 / 1000000000000) (37711128683 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 3) <| besselDerivativeNearFromState (1205009351940557 / 4000000000000) 3 (IntervalRat.scale (263 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (19764350164 / 1000000000000) (19764350165 / 1000000000000), orderedInterval (41471612492 / 1000000000000) (41471612493 / 1000000000000)))) (orderedInterval (5397701924 / 1000000000000) (5397705135 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 3) <| besselDerivativeNearFromState (1125876046284833 / 4000000000000) 3 (IntervalRat.scale (263 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-22355763282 / 1000000000000) (-22355761690 / 1000000000000), orderedInterval (42015866606 / 1000000000000) (42015868198 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 3) <| besselDerivativeNearFromState (803478271848689 / 4000000000000) 3 (IntervalRat.scale (263 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (31434078678 / 1000000000000) (31434078679 / 1000000000000), orderedInterval (46625305280 / 1000000000000) (46625305281 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 3) <| besselDerivativeNearFromState (911058724781031 / 4000000000000) 3 (IntervalRat.scale (263 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (37433471393 / 1000000000000) (37433513583 / 1000000000000), orderedInterval (-37415965271 / 1000000000000) (-37415923080 / 1000000000000)))) (orderedInterval (-9197114685 / 1000000000000) (-9197113215 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 3) <| besselDerivativeNearFromState (759545782075639 / 4000000000000) 3 (IntervalRat.scale (263 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (47629954128 / 1000000000000) (47630009680 / 1000000000000), orderedInterval (-33049821455 / 1000000000000) (-33049765904 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 3) <| besselDerivativeNearFromState (671081733176419 / 4000000000000) 3 (IntervalRat.scale (263 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-54642408482 / 1000000000000) (-54642392526 / 1000000000000), orderedInterval (28602018884 / 1000000000000) (28602034840 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 3) <| besselDerivativeNearFromState (194505642941481 / 800000000000) 3 (IntervalRat.scale (263 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-46219755567 / 1000000000000) (-46219739361 / 1000000000000), orderedInterval (22052795629 / 1000000000000) (22052811836 / 1000000000000)))) (orderedInterval (995922220 / 1000000000000) (995928745 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate256_chunkChecks3_2 :
    compactCertificate256.chunkChecks (3 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 3) <| besselDerivativeNearFromState (538012844647307 / 4000000000000) 3 (IntervalRat.scale (263 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-13613718409 / 1000000000000) (-13613718408 / 1000000000000), orderedInterval (-67386892625 / 1000000000000) (-67386892624 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 3) <| besselDerivativeNearFromState (456079446736627 / 4000000000000) 3 (IntervalRat.scale (263 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (74031582686 / 1000000000000) (74031582934 / 1000000000000), orderedInterval (-10457960447 / 1000000000000) (-10457960200 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 3) <| besselDerivativeNearFromState (285393341320081 / 4000000000000) 3 (IntervalRat.scale (263 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (11743769745 / 1000000000000) (11743769800 / 1000000000000), orderedInterval (-93810603571 / 1000000000000) (-93810603516 / 1000000000000)))) (orderedInterval (-11432552402 / 1000000000000) (-11432552363 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 3) <| besselDerivativeNearFromState (153485488137327 / 4000000000000) 3 (IntervalRat.scale (263 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (127929138851 / 1000000000000) (127929138855 / 1000000000000), orderedInterval (13292416241 / 1000000000000) (13292416245 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 3) <| besselDerivativeNearFromState (416742957472981 / 4000000000000) 3 (IntervalRat.scale (263 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-75265145394 / 1000000000000) (-75265145393 / 1000000000000), orderedInterval (-20746354917 / 1000000000000) (-20746354916 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 3) <| besselDerivativeNearFromState (569026879978037 / 4000000000000) 3 (IntervalRat.scale (263 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-66570271477 / 1000000000000) (-66570271296 / 1000000000000), orderedInterval (6830879919 / 1000000000000) (6830880100 / 1000000000000)))) (orderedInterval (486789707 / 1000000000000) (486789740 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 3) <| besselDerivativeNearFromState (240606658679919 / 4000000000000) 3 (IntervalRat.scale (263 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-97454059352 / 1000000000000) (-97454059351 / 1000000000000), orderedInterval (-32144391468 / 1000000000000) (-32144391467 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 3) <| besselDerivativeNearFromState (978052709451599 / 4000000000000) 3 (IntervalRat.scale (263 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (12813567555 / 1000000000000) (12813567556 / 1000000000000), orderedInterval (49364472846 / 1000000000000) (49364472847 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 3) <| besselDerivativeNearFromState (653293882976641 / 4000000000000) 3 (IntervalRat.scale (263 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (42340971440 / 1000000000000) (42340971441 / 1000000000000), orderedInterval (45752303206 / 1000000000000) (45752303207 / 1000000000000)))) (orderedInterval (42174658547 / 1000000000000) (42174658665 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate256_chunkChecks3 :
    compactCertificate256.chunkChecks (3 : Fin 5) 0 9 = true :=
  compactCertificate256.chunkChecks_nine_of_three (3 : Fin 5) compactCertificate256_chunkChecks3_0
    compactCertificate256_chunkChecks3_1 compactCertificate256_chunkChecks3_2

theorem compactCertificate256_chunkChecks4_0 :
    compactCertificate256.chunkChecks (4 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 4) <| besselDerivativeNearFromState (263 / 2) 4 (IntervalRat.scale (263 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (23043187807 / 1000000000000) (23043187808 / 1000000000000), orderedInterval (65564907847 / 1000000000000) (65564907848 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 4) <| besselDerivativeNearFromState (387449219297963 / 4000000000000) 4 (IntervalRat.scale (263 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-20609532368 / 1000000000000) (-20609532367 / 1000000000000), orderedInterval (-78301165508 / 1000000000000) (-78301165507 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 4) <| besselDerivativeNearFromState (125293116874379 / 800000000000) 4 (IntervalRat.scale (263 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (20137969760 / 1000000000000) (20137969761 / 1000000000000), orderedInterval (60427969944 / 1000000000000) (60427969945 / 1000000000000)))) (orderedInterval (11934686332 / 1000000000000) (11934686349 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 4) <| besselDerivativeNearFromState (113056715879041 / 4000000000000) 4 (IntervalRat.scale (263 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-104556283432 / 1000000000000) (-104556283431 / 1000000000000), orderedInterval (-105817076639 / 1000000000000) (-105817076638 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 4) <| besselDerivativeNearFromState (303686241593677 / 4000000000000) 4 (IntervalRat.scale (263 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (88404352715 / 1000000000000) (88404352716 / 1000000000000), orderedInterval (23287120977 / 1000000000000) (23287120978 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 4) <| besselDerivativeNearFromState (824567221314009 / 4000000000000) 4 (IntervalRat.scale (263 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-22584859103 / 1000000000000) (-22584858017 / 1000000000000), orderedInterval (50830674955 / 1000000000000) (50830676041 / 1000000000000)))) (orderedInterval (9846971715 / 1000000000000) (9846972243 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 4) <| besselDerivativeNearFromState (607372483187617 / 4000000000000) 4 (IntervalRat.scale (263 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (62566442370 / 1000000000000) (62566443824 / 1000000000000), orderedInterval (-16880422937 / 1000000000000) (-16880421483 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 4) <| besselDerivativeNearFromState (1040743102274341 / 4000000000000) 4 (IntervalRat.scale (263 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-10722451732 / 1000000000000) (-10722451731 / 1000000000000), orderedInterval (-48268341932 / 1000000000000) (-48268341931 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 4) <| besselDerivativeNearFromState (766606658679919 / 4000000000000) 4 (IntervalRat.scale (263 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-41314730872 / 1000000000000) (-41314730871 / 1000000000000), orderedInterval (-40077375709 / 1000000000000) (-40077375708 / 1000000000000)))) (orderedInterval (693633946 / 1000000000000) (693634024 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate256_chunkChecks4_1 :
    compactCertificate256.chunkChecks (4 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 4) <| besselDerivativeNearFromState (1176171756164737 / 4000000000000) 4 (IntervalRat.scale (263 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-21560795872 / 1000000000000) (-21560794516 / 1000000000000), orderedInterval (41270035018 / 1000000000000) (41270036373 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 4) <| besselDerivativeNearFromState (679063080034873 / 4000000000000) 4 (IntervalRat.scale (263 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (48136711946 / 1000000000000) (48136711947 / 1000000000000), orderedInterval (37711128682 / 1000000000000) (37711128683 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 4) <| besselDerivativeNearFromState (1205009351940557 / 4000000000000) 4 (IntervalRat.scale (263 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (19764350164 / 1000000000000) (19764350165 / 1000000000000), orderedInterval (41471612492 / 1000000000000) (41471612493 / 1000000000000)))) (orderedInterval (182986620323 / 1000000000000) (182986627519 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 4) <| besselDerivativeNearFromState (1125876046284833 / 4000000000000) 4 (IntervalRat.scale (263 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-22355763282 / 1000000000000) (-22355761690 / 1000000000000), orderedInterval (42015866606 / 1000000000000) (42015868198 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 4) <| besselDerivativeNearFromState (803478271848689 / 4000000000000) 4 (IntervalRat.scale (263 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (31434078678 / 1000000000000) (31434078679 / 1000000000000), orderedInterval (46625305280 / 1000000000000) (46625305281 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 4) <| besselDerivativeNearFromState (911058724781031 / 4000000000000) 4 (IntervalRat.scale (263 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (37433471393 / 1000000000000) (37433513583 / 1000000000000), orderedInterval (-37415965271 / 1000000000000) (-37415923080 / 1000000000000)))) (orderedInterval (23089575202 / 1000000000000) (23089577873 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 4) <| besselDerivativeNearFromState (759545782075639 / 4000000000000) 4 (IntervalRat.scale (263 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (47629954128 / 1000000000000) (47630009680 / 1000000000000), orderedInterval (-33049821455 / 1000000000000) (-33049765904 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 4) <| besselDerivativeNearFromState (671081733176419 / 4000000000000) 4 (IntervalRat.scale (263 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-54642408482 / 1000000000000) (-54642392526 / 1000000000000), orderedInterval (28602018884 / 1000000000000) (28602034840 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 4) <| besselDerivativeNearFromState (194505642941481 / 800000000000) 4 (IntervalRat.scale (263 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-46219755567 / 1000000000000) (-46219739361 / 1000000000000), orderedInterval (22052795629 / 1000000000000) (22052811836 / 1000000000000)))) (orderedInterval (-3168314684 / 1000000000000) (-3168304462 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate256_chunkChecks4_2 :
    compactCertificate256.chunkChecks (4 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 4) <| besselDerivativeNearFromState (538012844647307 / 4000000000000) 4 (IntervalRat.scale (263 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-13613718409 / 1000000000000) (-13613718408 / 1000000000000), orderedInterval (-67386892625 / 1000000000000) (-67386892624 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 4) <| besselDerivativeNearFromState (456079446736627 / 4000000000000) 4 (IntervalRat.scale (263 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (74031582686 / 1000000000000) (74031582934 / 1000000000000), orderedInterval (-10457960447 / 1000000000000) (-10457960200 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 4) <| besselDerivativeNearFromState (285393341320081 / 4000000000000) 4 (IntervalRat.scale (263 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (11743769745 / 1000000000000) (11743769800 / 1000000000000), orderedInterval (-93810603571 / 1000000000000) (-93810603516 / 1000000000000)))) (orderedInterval (221159871 / 1000000000000) (221159908 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 4) <| besselDerivativeNearFromState (153485488137327 / 4000000000000) 4 (IntervalRat.scale (263 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (127929138851 / 1000000000000) (127929138855 / 1000000000000), orderedInterval (13292416241 / 1000000000000) (13292416245 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 4) <| besselDerivativeNearFromState (416742957472981 / 4000000000000) 4 (IntervalRat.scale (263 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-75265145394 / 1000000000000) (-75265145393 / 1000000000000), orderedInterval (-20746354917 / 1000000000000) (-20746354916 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 4) <| besselDerivativeNearFromState (569026879978037 / 4000000000000) 4 (IntervalRat.scale (263 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-66570271477 / 1000000000000) (-66570271296 / 1000000000000), orderedInterval (6830879919 / 1000000000000) (6830880100 / 1000000000000)))) (orderedInterval (7635326197 / 1000000000000) (7635326232 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 4) <| besselDerivativeNearFromState (240606658679919 / 4000000000000) 4 (IntervalRat.scale (263 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-97454059352 / 1000000000000) (-97454059351 / 1000000000000), orderedInterval (-32144391468 / 1000000000000) (-32144391467 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 4) <| besselDerivativeNearFromState (978052709451599 / 4000000000000) 4 (IntervalRat.scale (263 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (12813567555 / 1000000000000) (12813567556 / 1000000000000), orderedInterval (49364472846 / 1000000000000) (49364472847 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 4) <| besselDerivativeNearFromState (653293882976641 / 4000000000000) 4 (IntervalRat.scale (263 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (42340971440 / 1000000000000) (42340971441 / 1000000000000), orderedInterval (45752303206 / 1000000000000) (45752303207 / 1000000000000)))) (orderedInterval (-32038283716 / 1000000000000) (-32038283526 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate256_chunkChecks4 :
    compactCertificate256.chunkChecks (4 : Fin 5) 0 9 = true :=
  compactCertificate256.chunkChecks_nine_of_three (4 : Fin 5) compactCertificate256_chunkChecks4_0
    compactCertificate256_chunkChecks4_1 compactCertificate256_chunkChecks4_2

theorem compactCertificate256_chunks :
    ∀ r : Fin 5, ∀ b, compactCertificate256.chunkCheck r b = true :=
  compactCertificate256.chunkChecks_all (by
    intro r
    fin_cases r
    · exact compactCertificate256_chunkChecks0
    · exact compactCertificate256_chunkChecks1
    · exact compactCertificate256_chunkChecks2
    · exact compactCertificate256_chunkChecks3
    · exact compactCertificate256_chunkChecks4)

theorem compactCertificate256_coefficient0 :
    compactCertificate256.coefficientCheck (0 : Fin 5) = true := by
  norm_num [CompactCertificate.coefficientCheck, intervalFinSumHull,
    compactCertificate256, rationalIntervalSubset, orderedInterval, Fin.sum_univ_succ]

theorem compactCertificate256_coefficient1 :
    compactCertificate256.coefficientCheck (1 : Fin 5) = true := by
  norm_num [CompactCertificate.coefficientCheck, intervalFinSumHull,
    compactCertificate256, rationalIntervalSubset, orderedInterval, Fin.sum_univ_succ]

theorem compactCertificate256_coefficient2 :
    compactCertificate256.coefficientCheck (2 : Fin 5) = true := by
  norm_num [CompactCertificate.coefficientCheck, intervalFinSumHull,
    compactCertificate256, rationalIntervalSubset, orderedInterval, Fin.sum_univ_succ]

theorem compactCertificate256_coefficient3 :
    compactCertificate256.coefficientCheck (3 : Fin 5) = true := by
  norm_num [CompactCertificate.coefficientCheck, intervalFinSumHull,
    compactCertificate256, rationalIntervalSubset, orderedInterval, Fin.sum_univ_succ]

theorem compactCertificate256_coefficient4 :
    compactCertificate256.coefficientCheck (4 : Fin 5) = true := by
  norm_num [CompactCertificate.coefficientCheck, intervalFinSumHull,
    compactCertificate256, rationalIntervalSubset, orderedInterval, Fin.sum_univ_succ]

theorem compactCertificate256_coefficients : ∀ r : Fin 5,
    compactCertificate256.coefficientCheck r = true := by
  intro r
  fin_cases r
  · exact compactCertificate256_coefficient0
  · exact compactCertificate256_coefficient1
  · exact compactCertificate256_coefficient2
  · exact compactCertificate256_coefficient3
  · exact compactCertificate256_coefficient4

theorem compactCertificate256_lower : (1 : ℚ) ≤ compactCertificate256.output.lo := by
  norm_num [CompactCertificate.output, CompactCertificate.interval,
    CompactCertificate.coefficientTargetNat, compactCertificate256, dualConstant,
    intervalTaylorSum, intervalPow, intervalSub, intervalMaxAbs, widenInterval,
    rationalErrorInterval, orderedInterval, IntervalRat.add, IntervalRat.mul, IntervalRat.scale,
    IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4]

theorem compactCertificate256_proves {t : ℝ} (ht : t ∈ compactCertificate256.interval) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t :=
  compactCertificate256.proves compactCertificate256_states compactCertificate256_chunks
    compactCertificate256_coefficients compactCertificate256_lower ht

end Erdos232
