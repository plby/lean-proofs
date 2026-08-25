/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, OpenAI Codex
-/
import ErdosProblems.Erdos232.CompactBase

open LeanCert.Core
namespace Erdos232

def compactCertificate245 : CompactCertificate where
  left := 120
  right := 121
  center := 241 / 2
  grid := fun i =>
    match i.val with
    | 0 => 38
    | 1 => 28
    | 2 => 46
    | 3 => 8
    | 4 => 22
    | 5 => 60
    | 6 => 44
    | 7 => 76
    | 8 => 56
    | 9 => 86
    | 10 => 50
    | 11 => 88
    | 12 => 82
    | 13 => 59
    | 14 => 66
    | 15 => 55
    | 16 => 49
    | 17 => 71
    | 18 => 39
    | 19 => 33
    | 20 => 21
    | 21 => 11
    | 22 => 30
    | 23 => 42
    | 24 => 18
    | 25 => 71
    | _ => 48
  point := fun i =>
    match i.val with
    | 0 => 241 / 2
    | 1 => 355039018444141 / 4000000000000
    | 2 => 114812323827853 / 800000000000
    | 3 => 103599500102087 / 4000000000000
    | 4 => 278282829749339 / 4000000000000
    | 5 => 755592016489263 / 4000000000000
    | 6 => 556565659498919 / 4000000000000
    | 7 => 953684743909187 / 4000000000000
    | 8 => 702479865938633 / 4000000000000
    | 9 => 1077784765154759 / 4000000000000
    | 10 => 622259324290511 / 4000000000000
    | 11 => 1104210090561499 / 4000000000000
    | 12 => 1031696300968231 / 4000000000000
    | 13 => 736267161656023 / 4000000000000
    | 14 => 834848489248017 / 4000000000000
    | 15 => 696009633004673 / 4000000000000
    | 16 => 614945618614133 / 4000000000000
    | 17 => 178235208931167 / 800000000000
    | 18 => 493007967908749 / 4000000000000
    | 19 => 417928314309989 / 4000000000000
    | 20 => 261520134061367 / 4000000000000
    | 21 => 140646397874889 / 4000000000000
    | 22 => 381882329851667 / 4000000000000
    | 23 => 521427673287859 / 4000000000000
    | 24 => 220479865938633 / 4000000000000
    | 25 => 896238414364393 / 4000000000000
    | _ => 598645725465287 / 4000000000000
  state := fun i =>
    match i.val with
    | 0 => (orderedInterval (68691059673 / 1000000000000) (68691062436 / 1000000000000), orderedInterval (-24047471026 / 1000000000000) (-24047468263 / 1000000000000))
    | 1 => (orderedInterval (84686350137 / 1000000000000) (84686350171 / 1000000000000), orderedInterval (-1184531379 / 1000000000000) (-1184531345 / 1000000000000))
    | 2 => (orderedInterval (-14100758331 / 1000000000000) (-14100758214 / 1000000000000), orderedInterval (65142071845 / 1000000000000) (65142071962 / 1000000000000))
    | 3 => (orderedInterval (156723856386 / 1000000000000) (156723856400 / 1000000000000), orderedInterval (595136691 / 1000000000000) (595136705 / 1000000000000))
    | 4 => (orderedInterval (90449111699 / 1000000000000) (90449111700 / 1000000000000), orderedInterval (30486119500 / 1000000000000) (30486119501 / 1000000000000))
    | 5 => (orderedInterval (53833692055 / 1000000000000) (53833692056 / 1000000000000), orderedInterval (21585425323 / 1000000000000) (21585425324 / 1000000000000))
    | 6 => (orderedInterval (67112958133 / 1000000000000) (67112958386 / 1000000000000), orderedInterval (-8677144308 / 1000000000000) (-8677144055 / 1000000000000))
    | 7 => (orderedInterval (22244076991 / 1000000000000) (22244076992 / 1000000000000), orderedInterval (46594024703 / 1000000000000) (46594024704 / 1000000000000))
    | 8 => (orderedInterval (27560165118 / 1000000000000) (27560165119 / 1000000000000), orderedInterval (53451255937 / 1000000000000) (53451255938 / 1000000000000))
    | 9 => (orderedInterval (2631168165 / 1000000000000) (2631168167 / 1000000000000), orderedInterval (48531477422 / 1000000000000) (48531477424 / 1000000000000))
    | 10 => (orderedInterval (-42670207196 / 1000000000000) (-42670172000 / 1000000000000), orderedInterval (47798104423 / 1000000000000) (47798139620 / 1000000000000))
    | 11 => (orderedInterval (17692661019 / 1000000000000) (17692661020 / 1000000000000), orderedInterval (44612405449 / 1000000000000) (44612405450 / 1000000000000))
    | 12 => (orderedInterval (44240105214 / 1000000000000) (44240105215 / 1000000000000), orderedInterval (22520769161 / 1000000000000) (22520769162 / 1000000000000))
    | 13 => (orderedInterval (28321763775 / 1000000000000) (28321766968 / 1000000000000), orderedInterval (-51618364846 / 1000000000000) (-51618361653 / 1000000000000))
    | 14 => (orderedInterval (46166206171 / 1000000000000) (46166255152 / 1000000000000), orderedInterval (-30424060043 / 1000000000000) (-30424011062 / 1000000000000))
    | 15 => (orderedInterval (-55013391205 / 1000000000000) (-55013381239 / 1000000000000), orderedInterval (25301685578 / 1000000000000) (25301695544 / 1000000000000))
    | 16 => (orderedInterval (-35424123164 / 1000000000000) (-35424123163 / 1000000000000), orderedInterval (-53607436665 / 1000000000000) (-53607436664 / 1000000000000))
    | 17 => (orderedInterval (-26827908787 / 1000000000000) (-26827908786 / 1000000000000), orderedInterval (-46175098509 / 1000000000000) (-46175098508 / 1000000000000))
    | 18 => (orderedInterval (-71754131624 / 1000000000000) (-71754131608 / 1000000000000), orderedInterval (-3769813732 / 1000000000000) (-3769813716 / 1000000000000))
    | 19 => (orderedInterval (-78037352204 / 1000000000000) (-78037352157 / 1000000000000), orderedInterval (2162899281 / 1000000000000) (2162899328 / 1000000000000))
    | 20 => (orderedInterval (-18643021921 / 1000000000000) (-18643021920 / 1000000000000), orderedInterval (-96759044417 / 1000000000000) (-96759044416 / 1000000000000))
    | 21 => (orderedInterval (-132257291366 / 1000000000000) (-132257291364 / 1000000000000), orderedInterval (-22855176006 / 1000000000000) (-22855176005 / 1000000000000))
    | 22 => (orderedInterval (74016055712 / 1000000000000) (74016062937 / 1000000000000), orderedInterval (-34881018841 / 1000000000000) (-34881011616 / 1000000000000))
    | 23 => (orderedInterval (-50399680435 / 1000000000000) (-50399604200 / 1000000000000), orderedInterval (48603408189 / 1000000000000) (48603484424 / 1000000000000))
    | 24 => (orderedInterval (-64658215819 / 1000000000000) (-64658190317 / 1000000000000), orderedInterval (86430274455 / 1000000000000) (86430299957 / 1000000000000))
    | 25 => (orderedInterval (-52012362502 / 1000000000000) (-52012361106 / 1000000000000), orderedInterval (11778156768 / 1000000000000) (11778158164 / 1000000000000))
    | _ => (orderedInterval (-22391709273 / 1000000000000) (-22391708599 / 1000000000000), orderedInterval (61331337214 / 1000000000000) (61331337888 / 1000000000000))
  chunkTarget := fun r b =>
    match r.val with
    | 0 =>
      match b.val with
      | 0 => orderedInterval (27188395300 / 1000000000000) (27188396411 / 1000000000000)
      | 1 => orderedInterval (-2224905582 / 1000000000000) (-2224905567 / 1000000000000)
      | 2 => orderedInterval (-20021522 / 1000000000000) (-20021514 / 1000000000000)
      | 3 => orderedInterval (-1113922050 / 1000000000000) (-1113919393 / 1000000000000)
      | 4 => orderedInterval (1645888878 / 1000000000000) (1645889443 / 1000000000000)
      | 5 => orderedInterval (705027926 / 1000000000000) (705028053 / 1000000000000)
      | 6 => orderedInterval (15282925378 / 1000000000000) (15282925415 / 1000000000000)
      | 7 => orderedInterval (4625522860 / 1000000000000) (4625528882 / 1000000000000)
      | _ => orderedInterval (8045396188 / 1000000000000) (8045396616 / 1000000000000)
    | 1 =>
      match b.val with
      | 0 => orderedInterval (-4986979162 / 1000000000000) (-4986978049 / 1000000000000)
      | 1 => orderedInterval (-1764248875 / 1000000000000) (-1764248857 / 1000000000000)
      | 2 => orderedInterval (-960815060 / 1000000000000) (-960815048 / 1000000000000)
      | 3 => orderedInterval (-182002758 / 1000000000000) (-181999290 / 1000000000000)
      | 4 => orderedInterval (-8059695570 / 1000000000000) (-8059694655 / 1000000000000)
      | 5 => orderedInterval (2149929211 / 1000000000000) (2149929394 / 1000000000000)
      | 6 => orderedInterval (-1198729936 / 1000000000000) (-1198729902 / 1000000000000)
      | 7 => orderedInterval (-3279500492 / 1000000000000) (-3279494028 / 1000000000000)
      | _ => orderedInterval (-15836620346 / 1000000000000) (-15836619860 / 1000000000000)
    | 2 =>
      match b.val with
      | 0 => orderedInterval (-26439779311 / 1000000000000) (-26439778186 / 1000000000000)
      | 1 => orderedInterval (8396992197 / 1000000000000) (8396992221 / 1000000000000)
      | 2 => orderedInterval (1279135312 / 1000000000000) (1279135334 / 1000000000000)
      | 3 => orderedInterval (-5591475170 / 1000000000000) (-5591470580 / 1000000000000)
      | 4 => orderedInterval (-1822210637 / 1000000000000) (-1822209142 / 1000000000000)
      | 5 => orderedInterval (355237690 / 1000000000000) (355237957 / 1000000000000)
      | 6 => orderedInterval (-15135037623 / 1000000000000) (-15135037591 / 1000000000000)
      | 7 => orderedInterval (-3647000988 / 1000000000000) (-3646993981 / 1000000000000)
      | _ => orderedInterval (-20906193048 / 1000000000000) (-20906192354 / 1000000000000)
    | 3 =>
      match b.val with
      | 0 => orderedInterval (3297111804 / 1000000000000) (3297112933 / 1000000000000)
      | 1 => orderedInterval (5627408206 / 1000000000000) (5627408241 / 1000000000000)
      | 2 => orderedInterval (7122271638 / 1000000000000) (7122271677 / 1000000000000)
      | 3 => orderedInterval (12590526040 / 1000000000000) (12590532158 / 1000000000000)
      | 4 => orderedInterval (20599204545 / 1000000000000) (20599206988 / 1000000000000)
      | 5 => orderedInterval (219162162 / 1000000000000) (219162550 / 1000000000000)
      | 6 => orderedInterval (63446893 / 1000000000000) (63446924 / 1000000000000)
      | 7 => orderedInterval (4341811005 / 1000000000000) (4341818554 / 1000000000000)
      | _ => orderedInterval (28333008011 / 1000000000000) (28333009111 / 1000000000000)
    | _ =>
      match b.val with
      | 0 => orderedInterval (25737597410 / 1000000000000) (25737598553 / 1000000000000)
      | 1 => orderedInterval (-22840672883 / 1000000000000) (-22840672829 / 1000000000000)
      | 2 => orderedInterval (-7628113807 / 1000000000000) (-7628113735 / 1000000000000)
      | 3 => orderedInterval (48595525797 / 1000000000000) (48595534179 / 1000000000000)
      | 4 => orderedInterval (-4627784550 / 1000000000000) (-4627780522 / 1000000000000)
      | 5 => orderedInterval (-5421793939 / 1000000000000) (-5421793371 / 1000000000000)
      | 6 => orderedInterval (14999320764 / 1000000000000) (14999320794 / 1000000000000)
      | 7 => orderedInterval (4573845026 / 1000000000000) (4573853230 / 1000000000000)
      | _ => orderedInterval (60119506355 / 1000000000000) (60119508210 / 1000000000000)
  coefficientTarget := fun i =>
    match i.val with
    | 0 => orderedInterval (54134307376 / 1000000000000) (54134318346 / 1000000000000)
    | 1 => orderedInterval (-34118662988 / 1000000000000) (-34118650295 / 1000000000000)
    | 2 => orderedInterval (-63510331578 / 1000000000000) (-63510316322 / 1000000000000)
    | 3 => orderedInterval (82193950304 / 1000000000000) (82193969136 / 1000000000000)
    | _ => orderedInterval (113507430173 / 1000000000000) (113507454509 / 1000000000000)

theorem compactCertificate245_stateChecks0 :
    compactCertificate245.stateChecks 0 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 38 12 (241 / 2)) (orderedInterval (68691059673 / 1000000000000) (68691062436 / 1000000000000), orderedInterval (-24047471026 / 1000000000000) (-24047468263 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 28 12 (355039018444141 / 4000000000000)) (orderedInterval (84686350137 / 1000000000000) (84686350171 / 1000000000000), orderedInterval (-1184531379 / 1000000000000) (-1184531345 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 46 12 (114812323827853 / 800000000000)) (orderedInterval (-14100758331 / 1000000000000) (-14100758214 / 1000000000000), orderedInterval (65142071845 / 1000000000000) (65142071962 / 1000000000000))) = true
  norm_num [besselStateAtRationalPoint, besselIntervalStepZero,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, besselZeroTransition,
    besselInitial, besselGridStateAt, besselGridStateBlock00, besselGridStateBlock01,
    besselGridStateBlock02, besselGridStateBlock03, besselGridStateBlock04,
    besselGridStateBlock05, besselGridStateBlock06, besselGridStateBlock07,
    besselGridStateBlock08, besselGridStateBlock09, besselGridStateBlock10,
    besselGridStateBlock11, besselGridStateBlock12, besselGridStateBlock13,
    besselGridStateBlock14, besselGridState008, besselGridState011, besselGridState018, besselGridState021, besselGridState022, besselGridState028, besselGridState030, besselGridState033, besselGridState038, besselGridState039, besselGridState042, besselGridState044, besselGridState046, besselGridState048, besselGridState049, besselGridState050, besselGridState055, besselGridState056, besselGridState059, besselGridState060, besselGridState066, besselGridState071, besselGridState076, besselGridState082, besselGridState086, besselGridState088, besselStateSubset, linearInterval, widenInterval,
    rationalErrorInterval, rationalIntervalSubset, orderedInterval, Finset.sum_range_succ,
    IntervalRat.add, IntervalRat.mul, IntervalRat.scale, IntervalRat.singleton]

theorem compactCertificate245_stateChecks1 :
    compactCertificate245.stateChecks 3 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 8 12 (103599500102087 / 4000000000000)) (orderedInterval (156723856386 / 1000000000000) (156723856400 / 1000000000000), orderedInterval (595136691 / 1000000000000) (595136705 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 22 12 (278282829749339 / 4000000000000)) (orderedInterval (90449111699 / 1000000000000) (90449111700 / 1000000000000), orderedInterval (30486119500 / 1000000000000) (30486119501 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 60 12 (755592016489263 / 4000000000000)) (orderedInterval (53833692055 / 1000000000000) (53833692056 / 1000000000000), orderedInterval (21585425323 / 1000000000000) (21585425324 / 1000000000000))) = true
  norm_num [besselStateAtRationalPoint, besselIntervalStepZero,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, besselZeroTransition,
    besselInitial, besselGridStateAt, besselGridStateBlock00, besselGridStateBlock01,
    besselGridStateBlock02, besselGridStateBlock03, besselGridStateBlock04,
    besselGridStateBlock05, besselGridStateBlock06, besselGridStateBlock07,
    besselGridStateBlock08, besselGridStateBlock09, besselGridStateBlock10,
    besselGridStateBlock11, besselGridStateBlock12, besselGridStateBlock13,
    besselGridStateBlock14, besselGridState008, besselGridState011, besselGridState018, besselGridState021, besselGridState022, besselGridState028, besselGridState030, besselGridState033, besselGridState038, besselGridState039, besselGridState042, besselGridState044, besselGridState046, besselGridState048, besselGridState049, besselGridState050, besselGridState055, besselGridState056, besselGridState059, besselGridState060, besselGridState066, besselGridState071, besselGridState076, besselGridState082, besselGridState086, besselGridState088, besselStateSubset, linearInterval, widenInterval,
    rationalErrorInterval, rationalIntervalSubset, orderedInterval, Finset.sum_range_succ,
    IntervalRat.add, IntervalRat.mul, IntervalRat.scale, IntervalRat.singleton]

theorem compactCertificate245_stateChecks2 :
    compactCertificate245.stateChecks 6 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 44 12 (556565659498919 / 4000000000000)) (orderedInterval (67112958133 / 1000000000000) (67112958386 / 1000000000000), orderedInterval (-8677144308 / 1000000000000) (-8677144055 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 76 12 (953684743909187 / 4000000000000)) (orderedInterval (22244076991 / 1000000000000) (22244076992 / 1000000000000), orderedInterval (46594024703 / 1000000000000) (46594024704 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 56 12 (702479865938633 / 4000000000000)) (orderedInterval (27560165118 / 1000000000000) (27560165119 / 1000000000000), orderedInterval (53451255937 / 1000000000000) (53451255938 / 1000000000000))) = true
  norm_num [besselStateAtRationalPoint, besselIntervalStepZero,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, besselZeroTransition,
    besselInitial, besselGridStateAt, besselGridStateBlock00, besselGridStateBlock01,
    besselGridStateBlock02, besselGridStateBlock03, besselGridStateBlock04,
    besselGridStateBlock05, besselGridStateBlock06, besselGridStateBlock07,
    besselGridStateBlock08, besselGridStateBlock09, besselGridStateBlock10,
    besselGridStateBlock11, besselGridStateBlock12, besselGridStateBlock13,
    besselGridStateBlock14, besselGridState008, besselGridState011, besselGridState018, besselGridState021, besselGridState022, besselGridState028, besselGridState030, besselGridState033, besselGridState038, besselGridState039, besselGridState042, besselGridState044, besselGridState046, besselGridState048, besselGridState049, besselGridState050, besselGridState055, besselGridState056, besselGridState059, besselGridState060, besselGridState066, besselGridState071, besselGridState076, besselGridState082, besselGridState086, besselGridState088, besselStateSubset, linearInterval, widenInterval,
    rationalErrorInterval, rationalIntervalSubset, orderedInterval, Finset.sum_range_succ,
    IntervalRat.add, IntervalRat.mul, IntervalRat.scale, IntervalRat.singleton]

theorem compactCertificate245_stateChecks3 :
    compactCertificate245.stateChecks 9 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 86 12 (1077784765154759 / 4000000000000)) (orderedInterval (2631168165 / 1000000000000) (2631168167 / 1000000000000), orderedInterval (48531477422 / 1000000000000) (48531477424 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 50 12 (622259324290511 / 4000000000000)) (orderedInterval (-42670207196 / 1000000000000) (-42670172000 / 1000000000000), orderedInterval (47798104423 / 1000000000000) (47798139620 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 88 12 (1104210090561499 / 4000000000000)) (orderedInterval (17692661019 / 1000000000000) (17692661020 / 1000000000000), orderedInterval (44612405449 / 1000000000000) (44612405450 / 1000000000000))) = true
  norm_num [besselStateAtRationalPoint, besselIntervalStepZero,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, besselZeroTransition,
    besselInitial, besselGridStateAt, besselGridStateBlock00, besselGridStateBlock01,
    besselGridStateBlock02, besselGridStateBlock03, besselGridStateBlock04,
    besselGridStateBlock05, besselGridStateBlock06, besselGridStateBlock07,
    besselGridStateBlock08, besselGridStateBlock09, besselGridStateBlock10,
    besselGridStateBlock11, besselGridStateBlock12, besselGridStateBlock13,
    besselGridStateBlock14, besselGridState008, besselGridState011, besselGridState018, besselGridState021, besselGridState022, besselGridState028, besselGridState030, besselGridState033, besselGridState038, besselGridState039, besselGridState042, besselGridState044, besselGridState046, besselGridState048, besselGridState049, besselGridState050, besselGridState055, besselGridState056, besselGridState059, besselGridState060, besselGridState066, besselGridState071, besselGridState076, besselGridState082, besselGridState086, besselGridState088, besselStateSubset, linearInterval, widenInterval,
    rationalErrorInterval, rationalIntervalSubset, orderedInterval, Finset.sum_range_succ,
    IntervalRat.add, IntervalRat.mul, IntervalRat.scale, IntervalRat.singleton]

theorem compactCertificate245_stateChecks4 :
    compactCertificate245.stateChecks 12 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 82 12 (1031696300968231 / 4000000000000)) (orderedInterval (44240105214 / 1000000000000) (44240105215 / 1000000000000), orderedInterval (22520769161 / 1000000000000) (22520769162 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 59 12 (736267161656023 / 4000000000000)) (orderedInterval (28321763775 / 1000000000000) (28321766968 / 1000000000000), orderedInterval (-51618364846 / 1000000000000) (-51618361653 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 66 12 (834848489248017 / 4000000000000)) (orderedInterval (46166206171 / 1000000000000) (46166255152 / 1000000000000), orderedInterval (-30424060043 / 1000000000000) (-30424011062 / 1000000000000))) = true
  norm_num [besselStateAtRationalPoint, besselIntervalStepZero,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, besselZeroTransition,
    besselInitial, besselGridStateAt, besselGridStateBlock00, besselGridStateBlock01,
    besselGridStateBlock02, besselGridStateBlock03, besselGridStateBlock04,
    besselGridStateBlock05, besselGridStateBlock06, besselGridStateBlock07,
    besselGridStateBlock08, besselGridStateBlock09, besselGridStateBlock10,
    besselGridStateBlock11, besselGridStateBlock12, besselGridStateBlock13,
    besselGridStateBlock14, besselGridState008, besselGridState011, besselGridState018, besselGridState021, besselGridState022, besselGridState028, besselGridState030, besselGridState033, besselGridState038, besselGridState039, besselGridState042, besselGridState044, besselGridState046, besselGridState048, besselGridState049, besselGridState050, besselGridState055, besselGridState056, besselGridState059, besselGridState060, besselGridState066, besselGridState071, besselGridState076, besselGridState082, besselGridState086, besselGridState088, besselStateSubset, linearInterval, widenInterval,
    rationalErrorInterval, rationalIntervalSubset, orderedInterval, Finset.sum_range_succ,
    IntervalRat.add, IntervalRat.mul, IntervalRat.scale, IntervalRat.singleton]

theorem compactCertificate245_stateChecks5 :
    compactCertificate245.stateChecks 15 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 55 12 (696009633004673 / 4000000000000)) (orderedInterval (-55013391205 / 1000000000000) (-55013381239 / 1000000000000), orderedInterval (25301685578 / 1000000000000) (25301695544 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 49 12 (614945618614133 / 4000000000000)) (orderedInterval (-35424123164 / 1000000000000) (-35424123163 / 1000000000000), orderedInterval (-53607436665 / 1000000000000) (-53607436664 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 71 12 (178235208931167 / 800000000000)) (orderedInterval (-26827908787 / 1000000000000) (-26827908786 / 1000000000000), orderedInterval (-46175098509 / 1000000000000) (-46175098508 / 1000000000000))) = true
  norm_num [besselStateAtRationalPoint, besselIntervalStepZero,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, besselZeroTransition,
    besselInitial, besselGridStateAt, besselGridStateBlock00, besselGridStateBlock01,
    besselGridStateBlock02, besselGridStateBlock03, besselGridStateBlock04,
    besselGridStateBlock05, besselGridStateBlock06, besselGridStateBlock07,
    besselGridStateBlock08, besselGridStateBlock09, besselGridStateBlock10,
    besselGridStateBlock11, besselGridStateBlock12, besselGridStateBlock13,
    besselGridStateBlock14, besselGridState008, besselGridState011, besselGridState018, besselGridState021, besselGridState022, besselGridState028, besselGridState030, besselGridState033, besselGridState038, besselGridState039, besselGridState042, besselGridState044, besselGridState046, besselGridState048, besselGridState049, besselGridState050, besselGridState055, besselGridState056, besselGridState059, besselGridState060, besselGridState066, besselGridState071, besselGridState076, besselGridState082, besselGridState086, besselGridState088, besselStateSubset, linearInterval, widenInterval,
    rationalErrorInterval, rationalIntervalSubset, orderedInterval, Finset.sum_range_succ,
    IntervalRat.add, IntervalRat.mul, IntervalRat.scale, IntervalRat.singleton]

theorem compactCertificate245_stateChecks6 :
    compactCertificate245.stateChecks 18 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 39 12 (493007967908749 / 4000000000000)) (orderedInterval (-71754131624 / 1000000000000) (-71754131608 / 1000000000000), orderedInterval (-3769813732 / 1000000000000) (-3769813716 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 33 12 (417928314309989 / 4000000000000)) (orderedInterval (-78037352204 / 1000000000000) (-78037352157 / 1000000000000), orderedInterval (2162899281 / 1000000000000) (2162899328 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 21 12 (261520134061367 / 4000000000000)) (orderedInterval (-18643021921 / 1000000000000) (-18643021920 / 1000000000000), orderedInterval (-96759044417 / 1000000000000) (-96759044416 / 1000000000000))) = true
  norm_num [besselStateAtRationalPoint, besselIntervalStepZero,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, besselZeroTransition,
    besselInitial, besselGridStateAt, besselGridStateBlock00, besselGridStateBlock01,
    besselGridStateBlock02, besselGridStateBlock03, besselGridStateBlock04,
    besselGridStateBlock05, besselGridStateBlock06, besselGridStateBlock07,
    besselGridStateBlock08, besselGridStateBlock09, besselGridStateBlock10,
    besselGridStateBlock11, besselGridStateBlock12, besselGridStateBlock13,
    besselGridStateBlock14, besselGridState008, besselGridState011, besselGridState018, besselGridState021, besselGridState022, besselGridState028, besselGridState030, besselGridState033, besselGridState038, besselGridState039, besselGridState042, besselGridState044, besselGridState046, besselGridState048, besselGridState049, besselGridState050, besselGridState055, besselGridState056, besselGridState059, besselGridState060, besselGridState066, besselGridState071, besselGridState076, besselGridState082, besselGridState086, besselGridState088, besselStateSubset, linearInterval, widenInterval,
    rationalErrorInterval, rationalIntervalSubset, orderedInterval, Finset.sum_range_succ,
    IntervalRat.add, IntervalRat.mul, IntervalRat.scale, IntervalRat.singleton]

theorem compactCertificate245_stateChecks7 :
    compactCertificate245.stateChecks 21 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 11 12 (140646397874889 / 4000000000000)) (orderedInterval (-132257291366 / 1000000000000) (-132257291364 / 1000000000000), orderedInterval (-22855176006 / 1000000000000) (-22855176005 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 30 12 (381882329851667 / 4000000000000)) (orderedInterval (74016055712 / 1000000000000) (74016062937 / 1000000000000), orderedInterval (-34881018841 / 1000000000000) (-34881011616 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 42 12 (521427673287859 / 4000000000000)) (orderedInterval (-50399680435 / 1000000000000) (-50399604200 / 1000000000000), orderedInterval (48603408189 / 1000000000000) (48603484424 / 1000000000000))) = true
  norm_num [besselStateAtRationalPoint, besselIntervalStepZero,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, besselZeroTransition,
    besselInitial, besselGridStateAt, besselGridStateBlock00, besselGridStateBlock01,
    besselGridStateBlock02, besselGridStateBlock03, besselGridStateBlock04,
    besselGridStateBlock05, besselGridStateBlock06, besselGridStateBlock07,
    besselGridStateBlock08, besselGridStateBlock09, besselGridStateBlock10,
    besselGridStateBlock11, besselGridStateBlock12, besselGridStateBlock13,
    besselGridStateBlock14, besselGridState008, besselGridState011, besselGridState018, besselGridState021, besselGridState022, besselGridState028, besselGridState030, besselGridState033, besselGridState038, besselGridState039, besselGridState042, besselGridState044, besselGridState046, besselGridState048, besselGridState049, besselGridState050, besselGridState055, besselGridState056, besselGridState059, besselGridState060, besselGridState066, besselGridState071, besselGridState076, besselGridState082, besselGridState086, besselGridState088, besselStateSubset, linearInterval, widenInterval,
    rationalErrorInterval, rationalIntervalSubset, orderedInterval, Finset.sum_range_succ,
    IntervalRat.add, IntervalRat.mul, IntervalRat.scale, IntervalRat.singleton]

theorem compactCertificate245_stateChecks8 :
    compactCertificate245.stateChecks 24 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 18 12 (220479865938633 / 4000000000000)) (orderedInterval (-64658215819 / 1000000000000) (-64658190317 / 1000000000000), orderedInterval (86430274455 / 1000000000000) (86430299957 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 71 12 (896238414364393 / 4000000000000)) (orderedInterval (-52012362502 / 1000000000000) (-52012361106 / 1000000000000), orderedInterval (11778156768 / 1000000000000) (11778158164 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 48 12 (598645725465287 / 4000000000000)) (orderedInterval (-22391709273 / 1000000000000) (-22391708599 / 1000000000000), orderedInterval (61331337214 / 1000000000000) (61331337888 / 1000000000000))) = true
  norm_num [besselStateAtRationalPoint, besselIntervalStepZero,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, besselZeroTransition,
    besselInitial, besselGridStateAt, besselGridStateBlock00, besselGridStateBlock01,
    besselGridStateBlock02, besselGridStateBlock03, besselGridStateBlock04,
    besselGridStateBlock05, besselGridStateBlock06, besselGridStateBlock07,
    besselGridStateBlock08, besselGridStateBlock09, besselGridStateBlock10,
    besselGridStateBlock11, besselGridStateBlock12, besselGridStateBlock13,
    besselGridStateBlock14, besselGridState008, besselGridState011, besselGridState018, besselGridState021, besselGridState022, besselGridState028, besselGridState030, besselGridState033, besselGridState038, besselGridState039, besselGridState042, besselGridState044, besselGridState046, besselGridState048, besselGridState049, besselGridState050, besselGridState055, besselGridState056, besselGridState059, besselGridState060, besselGridState066, besselGridState071, besselGridState076, besselGridState082, besselGridState086, besselGridState088, besselStateSubset, linearInterval, widenInterval,
    rationalErrorInterval, rationalIntervalSubset, orderedInterval, Finset.sum_range_succ,
    IntervalRat.add, IntervalRat.mul, IntervalRat.scale, IntervalRat.singleton]

theorem compactCertificate245_states : ∀ j,
    BesselStateValid (compactCertificate245.point j) (compactCertificate245.state j) :=
  compactCertificate245.statesValid_of_checks3 compactCertificate245_stateChecks0
    compactCertificate245_stateChecks1 compactCertificate245_stateChecks2
    compactCertificate245_stateChecks3 compactCertificate245_stateChecks4
    compactCertificate245_stateChecks5 compactCertificate245_stateChecks6
    compactCertificate245_stateChecks7 compactCertificate245_stateChecks8

theorem compactCertificate245_chunkChecks0_0 :
    compactCertificate245.chunkChecks (0 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 0) <| besselDerivativeNearFromState (241 / 2) 0 (IntervalRat.scale (241 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (68691059673 / 1000000000000) (68691062436 / 1000000000000), orderedInterval (-24047471026 / 1000000000000) (-24047468263 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 0) <| besselDerivativeNearFromState (355039018444141 / 4000000000000) 0 (IntervalRat.scale (241 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (84686350137 / 1000000000000) (84686350171 / 1000000000000), orderedInterval (-1184531379 / 1000000000000) (-1184531345 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 0) <| besselDerivativeNearFromState (114812323827853 / 800000000000) 0 (IntervalRat.scale (241 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-14100758331 / 1000000000000) (-14100758214 / 1000000000000), orderedInterval (65142071845 / 1000000000000) (65142071962 / 1000000000000)))) (orderedInterval (27188395300 / 1000000000000) (27188396411 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 0) <| besselDerivativeNearFromState (103599500102087 / 4000000000000) 0 (IntervalRat.scale (241 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (156723856386 / 1000000000000) (156723856400 / 1000000000000), orderedInterval (595136691 / 1000000000000) (595136705 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 0) <| besselDerivativeNearFromState (278282829749339 / 4000000000000) 0 (IntervalRat.scale (241 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (90449111699 / 1000000000000) (90449111700 / 1000000000000), orderedInterval (30486119500 / 1000000000000) (30486119501 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 0) <| besselDerivativeNearFromState (755592016489263 / 4000000000000) 0 (IntervalRat.scale (241 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (53833692055 / 1000000000000) (53833692056 / 1000000000000), orderedInterval (21585425323 / 1000000000000) (21585425324 / 1000000000000)))) (orderedInterval (-2224905582 / 1000000000000) (-2224905567 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 0) <| besselDerivativeNearFromState (556565659498919 / 4000000000000) 0 (IntervalRat.scale (241 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (67112958133 / 1000000000000) (67112958386 / 1000000000000), orderedInterval (-8677144308 / 1000000000000) (-8677144055 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 0) <| besselDerivativeNearFromState (953684743909187 / 4000000000000) 0 (IntervalRat.scale (241 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (22244076991 / 1000000000000) (22244076992 / 1000000000000), orderedInterval (46594024703 / 1000000000000) (46594024704 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 0) <| besselDerivativeNearFromState (702479865938633 / 4000000000000) 0 (IntervalRat.scale (241 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (27560165118 / 1000000000000) (27560165119 / 1000000000000), orderedInterval (53451255937 / 1000000000000) (53451255938 / 1000000000000)))) (orderedInterval (-20021522 / 1000000000000) (-20021514 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate245_chunkChecks0_1 :
    compactCertificate245.chunkChecks (0 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 0) <| besselDerivativeNearFromState (1077784765154759 / 4000000000000) 0 (IntervalRat.scale (241 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (2631168165 / 1000000000000) (2631168167 / 1000000000000), orderedInterval (48531477422 / 1000000000000) (48531477424 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 0) <| besselDerivativeNearFromState (622259324290511 / 4000000000000) 0 (IntervalRat.scale (241 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-42670207196 / 1000000000000) (-42670172000 / 1000000000000), orderedInterval (47798104423 / 1000000000000) (47798139620 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 0) <| besselDerivativeNearFromState (1104210090561499 / 4000000000000) 0 (IntervalRat.scale (241 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (17692661019 / 1000000000000) (17692661020 / 1000000000000), orderedInterval (44612405449 / 1000000000000) (44612405450 / 1000000000000)))) (orderedInterval (-1113922050 / 1000000000000) (-1113919393 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 0) <| besselDerivativeNearFromState (1031696300968231 / 4000000000000) 0 (IntervalRat.scale (241 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (44240105214 / 1000000000000) (44240105215 / 1000000000000), orderedInterval (22520769161 / 1000000000000) (22520769162 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 0) <| besselDerivativeNearFromState (736267161656023 / 4000000000000) 0 (IntervalRat.scale (241 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (28321763775 / 1000000000000) (28321766968 / 1000000000000), orderedInterval (-51618364846 / 1000000000000) (-51618361653 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 0) <| besselDerivativeNearFromState (834848489248017 / 4000000000000) 0 (IntervalRat.scale (241 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (46166206171 / 1000000000000) (46166255152 / 1000000000000), orderedInterval (-30424060043 / 1000000000000) (-30424011062 / 1000000000000)))) (orderedInterval (1645888878 / 1000000000000) (1645889443 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 0) <| besselDerivativeNearFromState (696009633004673 / 4000000000000) 0 (IntervalRat.scale (241 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-55013391205 / 1000000000000) (-55013381239 / 1000000000000), orderedInterval (25301685578 / 1000000000000) (25301695544 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 0) <| besselDerivativeNearFromState (614945618614133 / 4000000000000) 0 (IntervalRat.scale (241 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-35424123164 / 1000000000000) (-35424123163 / 1000000000000), orderedInterval (-53607436665 / 1000000000000) (-53607436664 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 0) <| besselDerivativeNearFromState (178235208931167 / 800000000000) 0 (IntervalRat.scale (241 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-26827908787 / 1000000000000) (-26827908786 / 1000000000000), orderedInterval (-46175098509 / 1000000000000) (-46175098508 / 1000000000000)))) (orderedInterval (705027926 / 1000000000000) (705028053 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate245_chunkChecks0_2 :
    compactCertificate245.chunkChecks (0 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 0) <| besselDerivativeNearFromState (493007967908749 / 4000000000000) 0 (IntervalRat.scale (241 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-71754131624 / 1000000000000) (-71754131608 / 1000000000000), orderedInterval (-3769813732 / 1000000000000) (-3769813716 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 0) <| besselDerivativeNearFromState (417928314309989 / 4000000000000) 0 (IntervalRat.scale (241 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-78037352204 / 1000000000000) (-78037352157 / 1000000000000), orderedInterval (2162899281 / 1000000000000) (2162899328 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 0) <| besselDerivativeNearFromState (261520134061367 / 4000000000000) 0 (IntervalRat.scale (241 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-18643021921 / 1000000000000) (-18643021920 / 1000000000000), orderedInterval (-96759044417 / 1000000000000) (-96759044416 / 1000000000000)))) (orderedInterval (15282925378 / 1000000000000) (15282925415 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 0) <| besselDerivativeNearFromState (140646397874889 / 4000000000000) 0 (IntervalRat.scale (241 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-132257291366 / 1000000000000) (-132257291364 / 1000000000000), orderedInterval (-22855176006 / 1000000000000) (-22855176005 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 0) <| besselDerivativeNearFromState (381882329851667 / 4000000000000) 0 (IntervalRat.scale (241 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (74016055712 / 1000000000000) (74016062937 / 1000000000000), orderedInterval (-34881018841 / 1000000000000) (-34881011616 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 0) <| besselDerivativeNearFromState (521427673287859 / 4000000000000) 0 (IntervalRat.scale (241 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-50399680435 / 1000000000000) (-50399604200 / 1000000000000), orderedInterval (48603408189 / 1000000000000) (48603484424 / 1000000000000)))) (orderedInterval (4625522860 / 1000000000000) (4625528882 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 0) <| besselDerivativeNearFromState (220479865938633 / 4000000000000) 0 (IntervalRat.scale (241 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-64658215819 / 1000000000000) (-64658190317 / 1000000000000), orderedInterval (86430274455 / 1000000000000) (86430299957 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 0) <| besselDerivativeNearFromState (896238414364393 / 4000000000000) 0 (IntervalRat.scale (241 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-52012362502 / 1000000000000) (-52012361106 / 1000000000000), orderedInterval (11778156768 / 1000000000000) (11778158164 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 0) <| besselDerivativeNearFromState (598645725465287 / 4000000000000) 0 (IntervalRat.scale (241 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-22391709273 / 1000000000000) (-22391708599 / 1000000000000), orderedInterval (61331337214 / 1000000000000) (61331337888 / 1000000000000)))) (orderedInterval (8045396188 / 1000000000000) (8045396616 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate245_chunkChecks0 :
    compactCertificate245.chunkChecks (0 : Fin 5) 0 9 = true :=
  compactCertificate245.chunkChecks_nine_of_three (0 : Fin 5) compactCertificate245_chunkChecks0_0
    compactCertificate245_chunkChecks0_1 compactCertificate245_chunkChecks0_2

theorem compactCertificate245_chunkChecks1_0 :
    compactCertificate245.chunkChecks (1 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 1) <| besselDerivativeNearFromState (241 / 2) 1 (IntervalRat.scale (241 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (68691059673 / 1000000000000) (68691062436 / 1000000000000), orderedInterval (-24047471026 / 1000000000000) (-24047468263 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 1) <| besselDerivativeNearFromState (355039018444141 / 4000000000000) 1 (IntervalRat.scale (241 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (84686350137 / 1000000000000) (84686350171 / 1000000000000), orderedInterval (-1184531379 / 1000000000000) (-1184531345 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 1) <| besselDerivativeNearFromState (114812323827853 / 800000000000) 1 (IntervalRat.scale (241 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-14100758331 / 1000000000000) (-14100758214 / 1000000000000), orderedInterval (65142071845 / 1000000000000) (65142071962 / 1000000000000)))) (orderedInterval (-4986979162 / 1000000000000) (-4986978049 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 1) <| besselDerivativeNearFromState (103599500102087 / 4000000000000) 1 (IntervalRat.scale (241 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (156723856386 / 1000000000000) (156723856400 / 1000000000000), orderedInterval (595136691 / 1000000000000) (595136705 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 1) <| besselDerivativeNearFromState (278282829749339 / 4000000000000) 1 (IntervalRat.scale (241 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (90449111699 / 1000000000000) (90449111700 / 1000000000000), orderedInterval (30486119500 / 1000000000000) (30486119501 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 1) <| besselDerivativeNearFromState (755592016489263 / 4000000000000) 1 (IntervalRat.scale (241 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (53833692055 / 1000000000000) (53833692056 / 1000000000000), orderedInterval (21585425323 / 1000000000000) (21585425324 / 1000000000000)))) (orderedInterval (-1764248875 / 1000000000000) (-1764248857 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 1) <| besselDerivativeNearFromState (556565659498919 / 4000000000000) 1 (IntervalRat.scale (241 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (67112958133 / 1000000000000) (67112958386 / 1000000000000), orderedInterval (-8677144308 / 1000000000000) (-8677144055 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 1) <| besselDerivativeNearFromState (953684743909187 / 4000000000000) 1 (IntervalRat.scale (241 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (22244076991 / 1000000000000) (22244076992 / 1000000000000), orderedInterval (46594024703 / 1000000000000) (46594024704 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 1) <| besselDerivativeNearFromState (702479865938633 / 4000000000000) 1 (IntervalRat.scale (241 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (27560165118 / 1000000000000) (27560165119 / 1000000000000), orderedInterval (53451255937 / 1000000000000) (53451255938 / 1000000000000)))) (orderedInterval (-960815060 / 1000000000000) (-960815048 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate245_chunkChecks1_1 :
    compactCertificate245.chunkChecks (1 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 1) <| besselDerivativeNearFromState (1077784765154759 / 4000000000000) 1 (IntervalRat.scale (241 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (2631168165 / 1000000000000) (2631168167 / 1000000000000), orderedInterval (48531477422 / 1000000000000) (48531477424 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 1) <| besselDerivativeNearFromState (622259324290511 / 4000000000000) 1 (IntervalRat.scale (241 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-42670207196 / 1000000000000) (-42670172000 / 1000000000000), orderedInterval (47798104423 / 1000000000000) (47798139620 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 1) <| besselDerivativeNearFromState (1104210090561499 / 4000000000000) 1 (IntervalRat.scale (241 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (17692661019 / 1000000000000) (17692661020 / 1000000000000), orderedInterval (44612405449 / 1000000000000) (44612405450 / 1000000000000)))) (orderedInterval (-182002758 / 1000000000000) (-181999290 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 1) <| besselDerivativeNearFromState (1031696300968231 / 4000000000000) 1 (IntervalRat.scale (241 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (44240105214 / 1000000000000) (44240105215 / 1000000000000), orderedInterval (22520769161 / 1000000000000) (22520769162 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 1) <| besselDerivativeNearFromState (736267161656023 / 4000000000000) 1 (IntervalRat.scale (241 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (28321763775 / 1000000000000) (28321766968 / 1000000000000), orderedInterval (-51618364846 / 1000000000000) (-51618361653 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 1) <| besselDerivativeNearFromState (834848489248017 / 4000000000000) 1 (IntervalRat.scale (241 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (46166206171 / 1000000000000) (46166255152 / 1000000000000), orderedInterval (-30424060043 / 1000000000000) (-30424011062 / 1000000000000)))) (orderedInterval (-8059695570 / 1000000000000) (-8059694655 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 1) <| besselDerivativeNearFromState (696009633004673 / 4000000000000) 1 (IntervalRat.scale (241 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-55013391205 / 1000000000000) (-55013381239 / 1000000000000), orderedInterval (25301685578 / 1000000000000) (25301695544 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 1) <| besselDerivativeNearFromState (614945618614133 / 4000000000000) 1 (IntervalRat.scale (241 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-35424123164 / 1000000000000) (-35424123163 / 1000000000000), orderedInterval (-53607436665 / 1000000000000) (-53607436664 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 1) <| besselDerivativeNearFromState (178235208931167 / 800000000000) 1 (IntervalRat.scale (241 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-26827908787 / 1000000000000) (-26827908786 / 1000000000000), orderedInterval (-46175098509 / 1000000000000) (-46175098508 / 1000000000000)))) (orderedInterval (2149929211 / 1000000000000) (2149929394 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate245_chunkChecks1_2 :
    compactCertificate245.chunkChecks (1 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 1) <| besselDerivativeNearFromState (493007967908749 / 4000000000000) 1 (IntervalRat.scale (241 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-71754131624 / 1000000000000) (-71754131608 / 1000000000000), orderedInterval (-3769813732 / 1000000000000) (-3769813716 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 1) <| besselDerivativeNearFromState (417928314309989 / 4000000000000) 1 (IntervalRat.scale (241 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-78037352204 / 1000000000000) (-78037352157 / 1000000000000), orderedInterval (2162899281 / 1000000000000) (2162899328 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 1) <| besselDerivativeNearFromState (261520134061367 / 4000000000000) 1 (IntervalRat.scale (241 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-18643021921 / 1000000000000) (-18643021920 / 1000000000000), orderedInterval (-96759044417 / 1000000000000) (-96759044416 / 1000000000000)))) (orderedInterval (-1198729936 / 1000000000000) (-1198729902 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 1) <| besselDerivativeNearFromState (140646397874889 / 4000000000000) 1 (IntervalRat.scale (241 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-132257291366 / 1000000000000) (-132257291364 / 1000000000000), orderedInterval (-22855176006 / 1000000000000) (-22855176005 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 1) <| besselDerivativeNearFromState (381882329851667 / 4000000000000) 1 (IntervalRat.scale (241 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (74016055712 / 1000000000000) (74016062937 / 1000000000000), orderedInterval (-34881018841 / 1000000000000) (-34881011616 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 1) <| besselDerivativeNearFromState (521427673287859 / 4000000000000) 1 (IntervalRat.scale (241 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-50399680435 / 1000000000000) (-50399604200 / 1000000000000), orderedInterval (48603408189 / 1000000000000) (48603484424 / 1000000000000)))) (orderedInterval (-3279500492 / 1000000000000) (-3279494028 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 1) <| besselDerivativeNearFromState (220479865938633 / 4000000000000) 1 (IntervalRat.scale (241 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-64658215819 / 1000000000000) (-64658190317 / 1000000000000), orderedInterval (86430274455 / 1000000000000) (86430299957 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 1) <| besselDerivativeNearFromState (896238414364393 / 4000000000000) 1 (IntervalRat.scale (241 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-52012362502 / 1000000000000) (-52012361106 / 1000000000000), orderedInterval (11778156768 / 1000000000000) (11778158164 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 1) <| besselDerivativeNearFromState (598645725465287 / 4000000000000) 1 (IntervalRat.scale (241 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-22391709273 / 1000000000000) (-22391708599 / 1000000000000), orderedInterval (61331337214 / 1000000000000) (61331337888 / 1000000000000)))) (orderedInterval (-15836620346 / 1000000000000) (-15836619860 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate245_chunkChecks1 :
    compactCertificate245.chunkChecks (1 : Fin 5) 0 9 = true :=
  compactCertificate245.chunkChecks_nine_of_three (1 : Fin 5) compactCertificate245_chunkChecks1_0
    compactCertificate245_chunkChecks1_1 compactCertificate245_chunkChecks1_2

theorem compactCertificate245_chunkChecks2_0 :
    compactCertificate245.chunkChecks (2 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 2) <| besselDerivativeNearFromState (241 / 2) 2 (IntervalRat.scale (241 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (68691059673 / 1000000000000) (68691062436 / 1000000000000), orderedInterval (-24047471026 / 1000000000000) (-24047468263 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 2) <| besselDerivativeNearFromState (355039018444141 / 4000000000000) 2 (IntervalRat.scale (241 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (84686350137 / 1000000000000) (84686350171 / 1000000000000), orderedInterval (-1184531379 / 1000000000000) (-1184531345 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 2) <| besselDerivativeNearFromState (114812323827853 / 800000000000) 2 (IntervalRat.scale (241 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-14100758331 / 1000000000000) (-14100758214 / 1000000000000), orderedInterval (65142071845 / 1000000000000) (65142071962 / 1000000000000)))) (orderedInterval (-26439779311 / 1000000000000) (-26439778186 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 2) <| besselDerivativeNearFromState (103599500102087 / 4000000000000) 2 (IntervalRat.scale (241 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (156723856386 / 1000000000000) (156723856400 / 1000000000000), orderedInterval (595136691 / 1000000000000) (595136705 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 2) <| besselDerivativeNearFromState (278282829749339 / 4000000000000) 2 (IntervalRat.scale (241 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (90449111699 / 1000000000000) (90449111700 / 1000000000000), orderedInterval (30486119500 / 1000000000000) (30486119501 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 2) <| besselDerivativeNearFromState (755592016489263 / 4000000000000) 2 (IntervalRat.scale (241 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (53833692055 / 1000000000000) (53833692056 / 1000000000000), orderedInterval (21585425323 / 1000000000000) (21585425324 / 1000000000000)))) (orderedInterval (8396992197 / 1000000000000) (8396992221 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 2) <| besselDerivativeNearFromState (556565659498919 / 4000000000000) 2 (IntervalRat.scale (241 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (67112958133 / 1000000000000) (67112958386 / 1000000000000), orderedInterval (-8677144308 / 1000000000000) (-8677144055 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 2) <| besselDerivativeNearFromState (953684743909187 / 4000000000000) 2 (IntervalRat.scale (241 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (22244076991 / 1000000000000) (22244076992 / 1000000000000), orderedInterval (46594024703 / 1000000000000) (46594024704 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 2) <| besselDerivativeNearFromState (702479865938633 / 4000000000000) 2 (IntervalRat.scale (241 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (27560165118 / 1000000000000) (27560165119 / 1000000000000), orderedInterval (53451255937 / 1000000000000) (53451255938 / 1000000000000)))) (orderedInterval (1279135312 / 1000000000000) (1279135334 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate245_chunkChecks2_1 :
    compactCertificate245.chunkChecks (2 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 2) <| besselDerivativeNearFromState (1077784765154759 / 4000000000000) 2 (IntervalRat.scale (241 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (2631168165 / 1000000000000) (2631168167 / 1000000000000), orderedInterval (48531477422 / 1000000000000) (48531477424 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 2) <| besselDerivativeNearFromState (622259324290511 / 4000000000000) 2 (IntervalRat.scale (241 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-42670207196 / 1000000000000) (-42670172000 / 1000000000000), orderedInterval (47798104423 / 1000000000000) (47798139620 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 2) <| besselDerivativeNearFromState (1104210090561499 / 4000000000000) 2 (IntervalRat.scale (241 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (17692661019 / 1000000000000) (17692661020 / 1000000000000), orderedInterval (44612405449 / 1000000000000) (44612405450 / 1000000000000)))) (orderedInterval (-5591475170 / 1000000000000) (-5591470580 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 2) <| besselDerivativeNearFromState (1031696300968231 / 4000000000000) 2 (IntervalRat.scale (241 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (44240105214 / 1000000000000) (44240105215 / 1000000000000), orderedInterval (22520769161 / 1000000000000) (22520769162 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 2) <| besselDerivativeNearFromState (736267161656023 / 4000000000000) 2 (IntervalRat.scale (241 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (28321763775 / 1000000000000) (28321766968 / 1000000000000), orderedInterval (-51618364846 / 1000000000000) (-51618361653 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 2) <| besselDerivativeNearFromState (834848489248017 / 4000000000000) 2 (IntervalRat.scale (241 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (46166206171 / 1000000000000) (46166255152 / 1000000000000), orderedInterval (-30424060043 / 1000000000000) (-30424011062 / 1000000000000)))) (orderedInterval (-1822210637 / 1000000000000) (-1822209142 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 2) <| besselDerivativeNearFromState (696009633004673 / 4000000000000) 2 (IntervalRat.scale (241 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-55013391205 / 1000000000000) (-55013381239 / 1000000000000), orderedInterval (25301685578 / 1000000000000) (25301695544 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 2) <| besselDerivativeNearFromState (614945618614133 / 4000000000000) 2 (IntervalRat.scale (241 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-35424123164 / 1000000000000) (-35424123163 / 1000000000000), orderedInterval (-53607436665 / 1000000000000) (-53607436664 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 2) <| besselDerivativeNearFromState (178235208931167 / 800000000000) 2 (IntervalRat.scale (241 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-26827908787 / 1000000000000) (-26827908786 / 1000000000000), orderedInterval (-46175098509 / 1000000000000) (-46175098508 / 1000000000000)))) (orderedInterval (355237690 / 1000000000000) (355237957 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate245_chunkChecks2_2 :
    compactCertificate245.chunkChecks (2 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 2) <| besselDerivativeNearFromState (493007967908749 / 4000000000000) 2 (IntervalRat.scale (241 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-71754131624 / 1000000000000) (-71754131608 / 1000000000000), orderedInterval (-3769813732 / 1000000000000) (-3769813716 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 2) <| besselDerivativeNearFromState (417928314309989 / 4000000000000) 2 (IntervalRat.scale (241 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-78037352204 / 1000000000000) (-78037352157 / 1000000000000), orderedInterval (2162899281 / 1000000000000) (2162899328 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 2) <| besselDerivativeNearFromState (261520134061367 / 4000000000000) 2 (IntervalRat.scale (241 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-18643021921 / 1000000000000) (-18643021920 / 1000000000000), orderedInterval (-96759044417 / 1000000000000) (-96759044416 / 1000000000000)))) (orderedInterval (-15135037623 / 1000000000000) (-15135037591 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 2) <| besselDerivativeNearFromState (140646397874889 / 4000000000000) 2 (IntervalRat.scale (241 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-132257291366 / 1000000000000) (-132257291364 / 1000000000000), orderedInterval (-22855176006 / 1000000000000) (-22855176005 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 2) <| besselDerivativeNearFromState (381882329851667 / 4000000000000) 2 (IntervalRat.scale (241 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (74016055712 / 1000000000000) (74016062937 / 1000000000000), orderedInterval (-34881018841 / 1000000000000) (-34881011616 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 2) <| besselDerivativeNearFromState (521427673287859 / 4000000000000) 2 (IntervalRat.scale (241 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-50399680435 / 1000000000000) (-50399604200 / 1000000000000), orderedInterval (48603408189 / 1000000000000) (48603484424 / 1000000000000)))) (orderedInterval (-3647000988 / 1000000000000) (-3646993981 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 2) <| besselDerivativeNearFromState (220479865938633 / 4000000000000) 2 (IntervalRat.scale (241 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-64658215819 / 1000000000000) (-64658190317 / 1000000000000), orderedInterval (86430274455 / 1000000000000) (86430299957 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 2) <| besselDerivativeNearFromState (896238414364393 / 4000000000000) 2 (IntervalRat.scale (241 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-52012362502 / 1000000000000) (-52012361106 / 1000000000000), orderedInterval (11778156768 / 1000000000000) (11778158164 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 2) <| besselDerivativeNearFromState (598645725465287 / 4000000000000) 2 (IntervalRat.scale (241 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-22391709273 / 1000000000000) (-22391708599 / 1000000000000), orderedInterval (61331337214 / 1000000000000) (61331337888 / 1000000000000)))) (orderedInterval (-20906193048 / 1000000000000) (-20906192354 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate245_chunkChecks2 :
    compactCertificate245.chunkChecks (2 : Fin 5) 0 9 = true :=
  compactCertificate245.chunkChecks_nine_of_three (2 : Fin 5) compactCertificate245_chunkChecks2_0
    compactCertificate245_chunkChecks2_1 compactCertificate245_chunkChecks2_2

theorem compactCertificate245_chunkChecks3_0 :
    compactCertificate245.chunkChecks (3 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 3) <| besselDerivativeNearFromState (241 / 2) 3 (IntervalRat.scale (241 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (68691059673 / 1000000000000) (68691062436 / 1000000000000), orderedInterval (-24047471026 / 1000000000000) (-24047468263 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 3) <| besselDerivativeNearFromState (355039018444141 / 4000000000000) 3 (IntervalRat.scale (241 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (84686350137 / 1000000000000) (84686350171 / 1000000000000), orderedInterval (-1184531379 / 1000000000000) (-1184531345 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 3) <| besselDerivativeNearFromState (114812323827853 / 800000000000) 3 (IntervalRat.scale (241 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-14100758331 / 1000000000000) (-14100758214 / 1000000000000), orderedInterval (65142071845 / 1000000000000) (65142071962 / 1000000000000)))) (orderedInterval (3297111804 / 1000000000000) (3297112933 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 3) <| besselDerivativeNearFromState (103599500102087 / 4000000000000) 3 (IntervalRat.scale (241 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (156723856386 / 1000000000000) (156723856400 / 1000000000000), orderedInterval (595136691 / 1000000000000) (595136705 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 3) <| besselDerivativeNearFromState (278282829749339 / 4000000000000) 3 (IntervalRat.scale (241 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (90449111699 / 1000000000000) (90449111700 / 1000000000000), orderedInterval (30486119500 / 1000000000000) (30486119501 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 3) <| besselDerivativeNearFromState (755592016489263 / 4000000000000) 3 (IntervalRat.scale (241 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (53833692055 / 1000000000000) (53833692056 / 1000000000000), orderedInterval (21585425323 / 1000000000000) (21585425324 / 1000000000000)))) (orderedInterval (5627408206 / 1000000000000) (5627408241 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 3) <| besselDerivativeNearFromState (556565659498919 / 4000000000000) 3 (IntervalRat.scale (241 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (67112958133 / 1000000000000) (67112958386 / 1000000000000), orderedInterval (-8677144308 / 1000000000000) (-8677144055 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 3) <| besselDerivativeNearFromState (953684743909187 / 4000000000000) 3 (IntervalRat.scale (241 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (22244076991 / 1000000000000) (22244076992 / 1000000000000), orderedInterval (46594024703 / 1000000000000) (46594024704 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 3) <| besselDerivativeNearFromState (702479865938633 / 4000000000000) 3 (IntervalRat.scale (241 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (27560165118 / 1000000000000) (27560165119 / 1000000000000), orderedInterval (53451255937 / 1000000000000) (53451255938 / 1000000000000)))) (orderedInterval (7122271638 / 1000000000000) (7122271677 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate245_chunkChecks3_1 :
    compactCertificate245.chunkChecks (3 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 3) <| besselDerivativeNearFromState (1077784765154759 / 4000000000000) 3 (IntervalRat.scale (241 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (2631168165 / 1000000000000) (2631168167 / 1000000000000), orderedInterval (48531477422 / 1000000000000) (48531477424 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 3) <| besselDerivativeNearFromState (622259324290511 / 4000000000000) 3 (IntervalRat.scale (241 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-42670207196 / 1000000000000) (-42670172000 / 1000000000000), orderedInterval (47798104423 / 1000000000000) (47798139620 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 3) <| besselDerivativeNearFromState (1104210090561499 / 4000000000000) 3 (IntervalRat.scale (241 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (17692661019 / 1000000000000) (17692661020 / 1000000000000), orderedInterval (44612405449 / 1000000000000) (44612405450 / 1000000000000)))) (orderedInterval (12590526040 / 1000000000000) (12590532158 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 3) <| besselDerivativeNearFromState (1031696300968231 / 4000000000000) 3 (IntervalRat.scale (241 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (44240105214 / 1000000000000) (44240105215 / 1000000000000), orderedInterval (22520769161 / 1000000000000) (22520769162 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 3) <| besselDerivativeNearFromState (736267161656023 / 4000000000000) 3 (IntervalRat.scale (241 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (28321763775 / 1000000000000) (28321766968 / 1000000000000), orderedInterval (-51618364846 / 1000000000000) (-51618361653 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 3) <| besselDerivativeNearFromState (834848489248017 / 4000000000000) 3 (IntervalRat.scale (241 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (46166206171 / 1000000000000) (46166255152 / 1000000000000), orderedInterval (-30424060043 / 1000000000000) (-30424011062 / 1000000000000)))) (orderedInterval (20599204545 / 1000000000000) (20599206988 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 3) <| besselDerivativeNearFromState (696009633004673 / 4000000000000) 3 (IntervalRat.scale (241 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-55013391205 / 1000000000000) (-55013381239 / 1000000000000), orderedInterval (25301685578 / 1000000000000) (25301695544 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 3) <| besselDerivativeNearFromState (614945618614133 / 4000000000000) 3 (IntervalRat.scale (241 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-35424123164 / 1000000000000) (-35424123163 / 1000000000000), orderedInterval (-53607436665 / 1000000000000) (-53607436664 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 3) <| besselDerivativeNearFromState (178235208931167 / 800000000000) 3 (IntervalRat.scale (241 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-26827908787 / 1000000000000) (-26827908786 / 1000000000000), orderedInterval (-46175098509 / 1000000000000) (-46175098508 / 1000000000000)))) (orderedInterval (219162162 / 1000000000000) (219162550 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate245_chunkChecks3_2 :
    compactCertificate245.chunkChecks (3 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 3) <| besselDerivativeNearFromState (493007967908749 / 4000000000000) 3 (IntervalRat.scale (241 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-71754131624 / 1000000000000) (-71754131608 / 1000000000000), orderedInterval (-3769813732 / 1000000000000) (-3769813716 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 3) <| besselDerivativeNearFromState (417928314309989 / 4000000000000) 3 (IntervalRat.scale (241 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-78037352204 / 1000000000000) (-78037352157 / 1000000000000), orderedInterval (2162899281 / 1000000000000) (2162899328 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 3) <| besselDerivativeNearFromState (261520134061367 / 4000000000000) 3 (IntervalRat.scale (241 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-18643021921 / 1000000000000) (-18643021920 / 1000000000000), orderedInterval (-96759044417 / 1000000000000) (-96759044416 / 1000000000000)))) (orderedInterval (63446893 / 1000000000000) (63446924 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 3) <| besselDerivativeNearFromState (140646397874889 / 4000000000000) 3 (IntervalRat.scale (241 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-132257291366 / 1000000000000) (-132257291364 / 1000000000000), orderedInterval (-22855176006 / 1000000000000) (-22855176005 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 3) <| besselDerivativeNearFromState (381882329851667 / 4000000000000) 3 (IntervalRat.scale (241 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (74016055712 / 1000000000000) (74016062937 / 1000000000000), orderedInterval (-34881018841 / 1000000000000) (-34881011616 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 3) <| besselDerivativeNearFromState (521427673287859 / 4000000000000) 3 (IntervalRat.scale (241 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-50399680435 / 1000000000000) (-50399604200 / 1000000000000), orderedInterval (48603408189 / 1000000000000) (48603484424 / 1000000000000)))) (orderedInterval (4341811005 / 1000000000000) (4341818554 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 3) <| besselDerivativeNearFromState (220479865938633 / 4000000000000) 3 (IntervalRat.scale (241 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-64658215819 / 1000000000000) (-64658190317 / 1000000000000), orderedInterval (86430274455 / 1000000000000) (86430299957 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 3) <| besselDerivativeNearFromState (896238414364393 / 4000000000000) 3 (IntervalRat.scale (241 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-52012362502 / 1000000000000) (-52012361106 / 1000000000000), orderedInterval (11778156768 / 1000000000000) (11778158164 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 3) <| besselDerivativeNearFromState (598645725465287 / 4000000000000) 3 (IntervalRat.scale (241 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-22391709273 / 1000000000000) (-22391708599 / 1000000000000), orderedInterval (61331337214 / 1000000000000) (61331337888 / 1000000000000)))) (orderedInterval (28333008011 / 1000000000000) (28333009111 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate245_chunkChecks3 :
    compactCertificate245.chunkChecks (3 : Fin 5) 0 9 = true :=
  compactCertificate245.chunkChecks_nine_of_three (3 : Fin 5) compactCertificate245_chunkChecks3_0
    compactCertificate245_chunkChecks3_1 compactCertificate245_chunkChecks3_2

theorem compactCertificate245_chunkChecks4_0 :
    compactCertificate245.chunkChecks (4 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 4) <| besselDerivativeNearFromState (241 / 2) 4 (IntervalRat.scale (241 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (68691059673 / 1000000000000) (68691062436 / 1000000000000), orderedInterval (-24047471026 / 1000000000000) (-24047468263 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 4) <| besselDerivativeNearFromState (355039018444141 / 4000000000000) 4 (IntervalRat.scale (241 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (84686350137 / 1000000000000) (84686350171 / 1000000000000), orderedInterval (-1184531379 / 1000000000000) (-1184531345 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 4) <| besselDerivativeNearFromState (114812323827853 / 800000000000) 4 (IntervalRat.scale (241 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-14100758331 / 1000000000000) (-14100758214 / 1000000000000), orderedInterval (65142071845 / 1000000000000) (65142071962 / 1000000000000)))) (orderedInterval (25737597410 / 1000000000000) (25737598553 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 4) <| besselDerivativeNearFromState (103599500102087 / 4000000000000) 4 (IntervalRat.scale (241 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (156723856386 / 1000000000000) (156723856400 / 1000000000000), orderedInterval (595136691 / 1000000000000) (595136705 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 4) <| besselDerivativeNearFromState (278282829749339 / 4000000000000) 4 (IntervalRat.scale (241 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (90449111699 / 1000000000000) (90449111700 / 1000000000000), orderedInterval (30486119500 / 1000000000000) (30486119501 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 4) <| besselDerivativeNearFromState (755592016489263 / 4000000000000) 4 (IntervalRat.scale (241 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (53833692055 / 1000000000000) (53833692056 / 1000000000000), orderedInterval (21585425323 / 1000000000000) (21585425324 / 1000000000000)))) (orderedInterval (-22840672883 / 1000000000000) (-22840672829 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 4) <| besselDerivativeNearFromState (556565659498919 / 4000000000000) 4 (IntervalRat.scale (241 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (67112958133 / 1000000000000) (67112958386 / 1000000000000), orderedInterval (-8677144308 / 1000000000000) (-8677144055 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 4) <| besselDerivativeNearFromState (953684743909187 / 4000000000000) 4 (IntervalRat.scale (241 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (22244076991 / 1000000000000) (22244076992 / 1000000000000), orderedInterval (46594024703 / 1000000000000) (46594024704 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 4) <| besselDerivativeNearFromState (702479865938633 / 4000000000000) 4 (IntervalRat.scale (241 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (27560165118 / 1000000000000) (27560165119 / 1000000000000), orderedInterval (53451255937 / 1000000000000) (53451255938 / 1000000000000)))) (orderedInterval (-7628113807 / 1000000000000) (-7628113735 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate245_chunkChecks4_1 :
    compactCertificate245.chunkChecks (4 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 4) <| besselDerivativeNearFromState (1077784765154759 / 4000000000000) 4 (IntervalRat.scale (241 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (2631168165 / 1000000000000) (2631168167 / 1000000000000), orderedInterval (48531477422 / 1000000000000) (48531477424 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 4) <| besselDerivativeNearFromState (622259324290511 / 4000000000000) 4 (IntervalRat.scale (241 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-42670207196 / 1000000000000) (-42670172000 / 1000000000000), orderedInterval (47798104423 / 1000000000000) (47798139620 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 4) <| besselDerivativeNearFromState (1104210090561499 / 4000000000000) 4 (IntervalRat.scale (241 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (17692661019 / 1000000000000) (17692661020 / 1000000000000), orderedInterval (44612405449 / 1000000000000) (44612405450 / 1000000000000)))) (orderedInterval (48595525797 / 1000000000000) (48595534179 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 4) <| besselDerivativeNearFromState (1031696300968231 / 4000000000000) 4 (IntervalRat.scale (241 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (44240105214 / 1000000000000) (44240105215 / 1000000000000), orderedInterval (22520769161 / 1000000000000) (22520769162 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 4) <| besselDerivativeNearFromState (736267161656023 / 4000000000000) 4 (IntervalRat.scale (241 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (28321763775 / 1000000000000) (28321766968 / 1000000000000), orderedInterval (-51618364846 / 1000000000000) (-51618361653 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 4) <| besselDerivativeNearFromState (834848489248017 / 4000000000000) 4 (IntervalRat.scale (241 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (46166206171 / 1000000000000) (46166255152 / 1000000000000), orderedInterval (-30424060043 / 1000000000000) (-30424011062 / 1000000000000)))) (orderedInterval (-4627784550 / 1000000000000) (-4627780522 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 4) <| besselDerivativeNearFromState (696009633004673 / 4000000000000) 4 (IntervalRat.scale (241 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-55013391205 / 1000000000000) (-55013381239 / 1000000000000), orderedInterval (25301685578 / 1000000000000) (25301695544 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 4) <| besselDerivativeNearFromState (614945618614133 / 4000000000000) 4 (IntervalRat.scale (241 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-35424123164 / 1000000000000) (-35424123163 / 1000000000000), orderedInterval (-53607436665 / 1000000000000) (-53607436664 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 4) <| besselDerivativeNearFromState (178235208931167 / 800000000000) 4 (IntervalRat.scale (241 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-26827908787 / 1000000000000) (-26827908786 / 1000000000000), orderedInterval (-46175098509 / 1000000000000) (-46175098508 / 1000000000000)))) (orderedInterval (-5421793939 / 1000000000000) (-5421793371 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate245_chunkChecks4_2 :
    compactCertificate245.chunkChecks (4 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 4) <| besselDerivativeNearFromState (493007967908749 / 4000000000000) 4 (IntervalRat.scale (241 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-71754131624 / 1000000000000) (-71754131608 / 1000000000000), orderedInterval (-3769813732 / 1000000000000) (-3769813716 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 4) <| besselDerivativeNearFromState (417928314309989 / 4000000000000) 4 (IntervalRat.scale (241 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-78037352204 / 1000000000000) (-78037352157 / 1000000000000), orderedInterval (2162899281 / 1000000000000) (2162899328 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 4) <| besselDerivativeNearFromState (261520134061367 / 4000000000000) 4 (IntervalRat.scale (241 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-18643021921 / 1000000000000) (-18643021920 / 1000000000000), orderedInterval (-96759044417 / 1000000000000) (-96759044416 / 1000000000000)))) (orderedInterval (14999320764 / 1000000000000) (14999320794 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 4) <| besselDerivativeNearFromState (140646397874889 / 4000000000000) 4 (IntervalRat.scale (241 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-132257291366 / 1000000000000) (-132257291364 / 1000000000000), orderedInterval (-22855176006 / 1000000000000) (-22855176005 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 4) <| besselDerivativeNearFromState (381882329851667 / 4000000000000) 4 (IntervalRat.scale (241 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (74016055712 / 1000000000000) (74016062937 / 1000000000000), orderedInterval (-34881018841 / 1000000000000) (-34881011616 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 4) <| besselDerivativeNearFromState (521427673287859 / 4000000000000) 4 (IntervalRat.scale (241 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-50399680435 / 1000000000000) (-50399604200 / 1000000000000), orderedInterval (48603408189 / 1000000000000) (48603484424 / 1000000000000)))) (orderedInterval (4573845026 / 1000000000000) (4573853230 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 4) <| besselDerivativeNearFromState (220479865938633 / 4000000000000) 4 (IntervalRat.scale (241 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-64658215819 / 1000000000000) (-64658190317 / 1000000000000), orderedInterval (86430274455 / 1000000000000) (86430299957 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 4) <| besselDerivativeNearFromState (896238414364393 / 4000000000000) 4 (IntervalRat.scale (241 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-52012362502 / 1000000000000) (-52012361106 / 1000000000000), orderedInterval (11778156768 / 1000000000000) (11778158164 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 4) <| besselDerivativeNearFromState (598645725465287 / 4000000000000) 4 (IntervalRat.scale (241 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-22391709273 / 1000000000000) (-22391708599 / 1000000000000), orderedInterval (61331337214 / 1000000000000) (61331337888 / 1000000000000)))) (orderedInterval (60119506355 / 1000000000000) (60119508210 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate245_chunkChecks4 :
    compactCertificate245.chunkChecks (4 : Fin 5) 0 9 = true :=
  compactCertificate245.chunkChecks_nine_of_three (4 : Fin 5) compactCertificate245_chunkChecks4_0
    compactCertificate245_chunkChecks4_1 compactCertificate245_chunkChecks4_2

theorem compactCertificate245_chunks :
    ∀ r : Fin 5, ∀ b, compactCertificate245.chunkCheck r b = true :=
  compactCertificate245.chunkChecks_all (by
    intro r
    fin_cases r
    · exact compactCertificate245_chunkChecks0
    · exact compactCertificate245_chunkChecks1
    · exact compactCertificate245_chunkChecks2
    · exact compactCertificate245_chunkChecks3
    · exact compactCertificate245_chunkChecks4)

theorem compactCertificate245_coefficient0 :
    compactCertificate245.coefficientCheck (0 : Fin 5) = true := by
  norm_num [CompactCertificate.coefficientCheck, intervalFinSumHull,
    compactCertificate245, rationalIntervalSubset, orderedInterval, Fin.sum_univ_succ]

theorem compactCertificate245_coefficient1 :
    compactCertificate245.coefficientCheck (1 : Fin 5) = true := by
  norm_num [CompactCertificate.coefficientCheck, intervalFinSumHull,
    compactCertificate245, rationalIntervalSubset, orderedInterval, Fin.sum_univ_succ]

theorem compactCertificate245_coefficient2 :
    compactCertificate245.coefficientCheck (2 : Fin 5) = true := by
  norm_num [CompactCertificate.coefficientCheck, intervalFinSumHull,
    compactCertificate245, rationalIntervalSubset, orderedInterval, Fin.sum_univ_succ]

theorem compactCertificate245_coefficient3 :
    compactCertificate245.coefficientCheck (3 : Fin 5) = true := by
  norm_num [CompactCertificate.coefficientCheck, intervalFinSumHull,
    compactCertificate245, rationalIntervalSubset, orderedInterval, Fin.sum_univ_succ]

theorem compactCertificate245_coefficient4 :
    compactCertificate245.coefficientCheck (4 : Fin 5) = true := by
  norm_num [CompactCertificate.coefficientCheck, intervalFinSumHull,
    compactCertificate245, rationalIntervalSubset, orderedInterval, Fin.sum_univ_succ]

theorem compactCertificate245_coefficients : ∀ r : Fin 5,
    compactCertificate245.coefficientCheck r = true := by
  intro r
  fin_cases r
  · exact compactCertificate245_coefficient0
  · exact compactCertificate245_coefficient1
  · exact compactCertificate245_coefficient2
  · exact compactCertificate245_coefficient3
  · exact compactCertificate245_coefficient4

theorem compactCertificate245_lower : (1 : ℚ) ≤ compactCertificate245.output.lo := by
  norm_num [CompactCertificate.output, CompactCertificate.interval,
    CompactCertificate.coefficientTargetNat, compactCertificate245, dualConstant,
    intervalTaylorSum, intervalPow, intervalSub, intervalMaxAbs, widenInterval,
    rationalErrorInterval, orderedInterval, IntervalRat.add, IntervalRat.mul, IntervalRat.scale,
    IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4]

theorem compactCertificate245_proves {t : ℝ} (ht : t ∈ compactCertificate245.interval) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t :=
  compactCertificate245.proves compactCertificate245_states compactCertificate245_chunks
    compactCertificate245_coefficients compactCertificate245_lower ht

end Erdos232
