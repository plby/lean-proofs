/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, OpenAI Codex
-/
import ErdosProblems.Erdos232.CompactBase

open LeanCert.Core
namespace Erdos232

def compactCertificate200 : CompactCertificate where
  left := 183 / 2
  right := 92
  center := 367 / 4
  grid := fun i =>
    match i.val with
    | 0 => 29
    | 1 => 22
    | 2 => 35
    | 3 => 6
    | 4 => 17
    | 5 => 46
    | 6 => 34
    | 7 => 58
    | 8 => 43
    | 9 => 65
    | 10 => 38
    | 11 => 67
    | 12 => 63
    | 13 => 45
    | 14 => 51
    | 15 => 42
    | 16 => 37
    | 17 => 54
    | 18 => 30
    | 19 => 25
    | 20 => 16
    | 21 => 9
    | 22 => 23
    | 23 => 32
    | 24 => 13
    | 25 => 54
    | _ => 36
  point := fun i =>
    match i.val with
    | 0 => 367 / 4
    | 1 => 540661077879667 / 8000000000000
    | 2 => 174838684003411 / 1600000000000
    | 3 => 157763554097369 / 8000000000000
    | 4 => 423775097585093 / 8000000000000
    | 5 => 1150631825940081 / 8000000000000
    | 6 => 847550195170553 / 8000000000000
    | 7 => 1452291705455069 / 8000000000000
    | 8 => 1069751497093271 / 8000000000000
    | 9 => 1641273895484633 / 8000000000000
    | 10 => 947589925371857 / 8000000000000
    | 11 => 1681514951187013 / 8000000000000
    | 12 => 1571089387781497 / 8000000000000
    | 13 => 1121203520032201 / 8000000000000
    | 14 => 1271325292755279 / 8000000000000
    | 15 => 1059898486774751 / 8000000000000
    | 16 => 936452456561771 / 8000000000000
    | 17 => 271420421899329 / 1600000000000
    | 18 => 750763171047763 / 8000000000000
    | 19 => 636430254571643 / 8000000000000
    | 20 => 398248502906729 / 8000000000000
    | 21 => 214179369377943 / 8000000000000
    | 22 => 581538651682829 / 8000000000000
    | 23 => 794041311604333 / 8000000000000
    | 24 => 335751497093271 / 8000000000000
    | 25 => 1364811195318391 / 8000000000000
    | _ => 911630627575769 / 8000000000000
  state := fun i =>
    match i.val with
    | 0 => (orderedInterval (-82448247165 / 1000000000000) (-82448247162 / 1000000000000), orderedInterval (-11417583665 / 1000000000000) (-11417583661 / 1000000000000))
    | 1 => (orderedInterval (-66074907872 / 1000000000000) (-66074846775 / 1000000000000), orderedInterval (71580284501 / 1000000000000) (71580345598 / 1000000000000))
    | 2 => (orderedInterval (-7824184704 / 1000000000000) (-7824184702 / 1000000000000), orderedInterval (-75890057346 / 1000000000000) (-75890057345 / 1000000000000))
    | 3 => (orderedInterval (179081231183 / 1000000000000) (179081231245 / 1000000000000), orderedInterval (-18747904734 / 1000000000000) (-18747904672 / 1000000000000))
    | 4 => (orderedInterval (-37368612099 / 1000000000000) (-37368612098 / 1000000000000), orderedInterval (-102710718475 / 1000000000000) (-102710718474 / 1000000000000))
    | 5 => (orderedInterval (6658123401 / 1000000000000) (6658123402 / 1000000000000), orderedInterval (66172949779 / 1000000000000) (66172949780 / 1000000000000))
    | 6 => (orderedInterval (-6670455164 / 1000000000000) (-6670455140 / 1000000000000), orderedInterval (77262337128 / 1000000000000) (77262337152 / 1000000000000))
    | 7 => (orderedInterval (6430201591 / 1000000000000) (6430201592 / 1000000000000), orderedInterval (58850854496 / 1000000000000) (58850854497 / 1000000000000))
    | 8 => (orderedInterval (38105945087 / 1000000000000) (38105954920 / 1000000000000), orderedInterval (-57664911638 / 1000000000000) (-57664901805 / 1000000000000))
    | 9 => (orderedInterval (-54904720742 / 1000000000000) (-54904720062 / 1000000000000), orderedInterval (9542047126 / 1000000000000) (9542047806 / 1000000000000))
    | 10 => (orderedInterval (-10769749850 / 1000000000000) (-10769749796 / 1000000000000), orderedInterval (72562368877 / 1000000000000) (72562368932 / 1000000000000))
    | 11 => (orderedInterval (-25777403877 / 1000000000000) (-25777403876 / 1000000000000), orderedInterval (-48562972654 / 1000000000000) (-48562972653 / 1000000000000))
    | 12 => (orderedInterval (38784576022 / 1000000000000) (38784610793 / 1000000000000), orderedInterval (-41781241331 / 1000000000000) (-41781206560 / 1000000000000))
    | 13 => (orderedInterval (28507129024 / 1000000000000) (28507130991 / 1000000000000), orderedInterval (-61173503955 / 1000000000000) (-61173501987 / 1000000000000))
    | 14 => (orderedInterval (31501312798 / 1000000000000) (31501317261 / 1000000000000), orderedInterval (-54996291124 / 1000000000000) (-54996286661 / 1000000000000))
    | 15 => (orderedInterval (67233272703 / 1000000000000) (67233272705 / 1000000000000), orderedInterval (16622126857 / 1000000000000) (16622126858 / 1000000000000))
    | 16 => (orderedInterval (-73710489654 / 1000000000000) (-73710489595 / 1000000000000), orderedInterval (2612641904 / 1000000000000) (2612641963 / 1000000000000))
    | 17 => (orderedInterval (42926869664 / 1000000000000) (42926869665 / 1000000000000), orderedInterval (43578199507 / 1000000000000) (43578199508 / 1000000000000))
    | 18 => (orderedInterval (30678693285 / 1000000000000) (30678693286 / 1000000000000), orderedInterval (76273423243 / 1000000000000) (76273423244 / 1000000000000))
    | 19 => (orderedInterval (-87160341903 / 1000000000000) (-87160341268 / 1000000000000), orderedInterval (20680224817 / 1000000000000) (20680225453 / 1000000000000))
    | 20 => (orderedInterval (33252755748 / 1000000000000) (33252755749 / 1000000000000), orderedInterval (107754803143 / 1000000000000) (107754803144 / 1000000000000))
    | 21 => (orderedInterval (101807751706 / 1000000000000) (101807807811 / 1000000000000), orderedInterval (-117722328216 / 1000000000000) (-117722272111 / 1000000000000))
    | 22 => (orderedInterval (-87862471206 / 1000000000000) (-87862471205 / 1000000000000), orderedInterval (-31609928827 / 1000000000000) (-31609928826 / 1000000000000))
    | 23 => (orderedInterval (-37808305210 / 1000000000000) (-37808300724 / 1000000000000), orderedInterval (70791788698 / 1000000000000) (70791793184 / 1000000000000))
    | 24 => (orderedInterval (-116113132889 / 1000000000000) (-116113130935 / 1000000000000), orderedInterval (42440847157 / 1000000000000) (42440849111 / 1000000000000))
    | 25 => (orderedInterval (60213859930 / 1000000000000) (60213860475 / 1000000000000), orderedInterval (-10467099228 / 1000000000000) (-10467098682 / 1000000000000))
    | _ => (orderedInterval (74560478141 / 1000000000000) (74560478241 / 1000000000000), orderedInterval (-5554811040 / 1000000000000) (-5554810939 / 1000000000000))
  chunkTarget := fun r b =>
    match r.val with
    | 0 =>
      match b.val with
      | 0 => orderedInterval (-33754420948 / 1000000000000) (-33754420370 / 1000000000000)
      | 1 => orderedInterval (-3780621272 / 1000000000000) (-3780621259 / 1000000000000)
      | 2 => orderedInterval (722612362 / 1000000000000) (722612606 / 1000000000000)
      | 3 => orderedInterval (5293546136 / 1000000000000) (5293546298 / 1000000000000)
      | 4 => orderedInterval (1836119092 / 1000000000000) (1836119940 / 1000000000000)
      | 5 => orderedInterval (6093691445 / 1000000000000) (6093691459 / 1000000000000)
      | 6 => orderedInterval (1110532757 / 1000000000000) (1110532817 / 1000000000000)
      | 7 => orderedInterval (3011016115 / 1000000000000) (3011017506 / 1000000000000)
      | _ => orderedInterval (-19591006890 / 1000000000000) (-19591006789 / 1000000000000)
    | 1 =>
      match b.val with
      | 0 => orderedInterval (-9338123852 / 1000000000000) (-9338123423 / 1000000000000)
      | 1 => orderedInterval (-9495837917 / 1000000000000) (-9495837903 / 1000000000000)
      | 2 => orderedInterval (-5622683849 / 1000000000000) (-5622683493 / 1000000000000)
      | 3 => orderedInterval (-12665731918 / 1000000000000) (-12665731566 / 1000000000000)
      | 4 => orderedInterval (-6739790013 / 1000000000000) (-6739788327 / 1000000000000)
      | 5 => orderedInterval (2149389394 / 1000000000000) (2149389412 / 1000000000000)
      | 6 => orderedInterval (-11585635205 / 1000000000000) (-11585635151 / 1000000000000)
      | 7 => orderedInterval (-4666732548 / 1000000000000) (-4666731863 / 1000000000000)
      | _ => orderedInterval (2995782182 / 1000000000000) (2995782330 / 1000000000000)
    | 2 =>
      match b.val with
      | 0 => orderedInterval (33766702453 / 1000000000000) (33766702777 / 1000000000000)
      | 1 => orderedInterval (1811210769 / 1000000000000) (1811210787 / 1000000000000)
      | 2 => orderedInterval (-1118447137 / 1000000000000) (-1118446612 / 1000000000000)
      | 3 => orderedInterval (-28080057245 / 1000000000000) (-28080056468 / 1000000000000)
      | 4 => orderedInterval (-2530406303 / 1000000000000) (-2530402877 / 1000000000000)
      | 5 => orderedInterval (-12265602931 / 1000000000000) (-12265602906 / 1000000000000)
      | 6 => orderedInterval (1230596230 / 1000000000000) (1230596279 / 1000000000000)
      | 7 => orderedInterval (-4431338330 / 1000000000000) (-4431337821 / 1000000000000)
      | _ => orderedInterval (38640300741 / 1000000000000) (38640300981 / 1000000000000)
    | 3 =>
      match b.val with
      | 0 => orderedInterval (11413288613 / 1000000000000) (11413288856 / 1000000000000)
      | 1 => orderedInterval (18820896919 / 1000000000000) (18820896946 / 1000000000000)
      | 2 => orderedInterval (18386225432 / 1000000000000) (18386226203 / 1000000000000)
      | 3 => orderedInterval (90694141104 / 1000000000000) (90694142827 / 1000000000000)
      | 4 => orderedInterval (11801888129 / 1000000000000) (11801895153 / 1000000000000)
      | 5 => orderedInterval (-7185730270 / 1000000000000) (-7185730233 / 1000000000000)
      | 6 => orderedInterval (13238257144 / 1000000000000) (13238257188 / 1000000000000)
      | 7 => orderedInterval (6505760164 / 1000000000000) (6505760642 / 1000000000000)
      | _ => orderedInterval (-7919661213 / 1000000000000) (-7919660806 / 1000000000000)
    | _ =>
      match b.val with
      | 0 => orderedInterval (-34029428595 / 1000000000000) (-34029428409 / 1000000000000)
      | 1 => orderedInterval (-3424159838 / 1000000000000) (-3424159797 / 1000000000000)
      | 2 => orderedInterval (714512722 / 1000000000000) (714513865 / 1000000000000)
      | 3 => orderedInterval (138770242956 / 1000000000000) (138770246808 / 1000000000000)
      | 4 => orderedInterval (-1712664142 / 1000000000000) (-1712649513 / 1000000000000)
      | 5 => orderedInterval (27550836224 / 1000000000000) (27550836281 / 1000000000000)
      | 6 => orderedInterval (-2775188357 / 1000000000000) (-2775188316 / 1000000000000)
      | 7 => orderedInterval (4597948556 / 1000000000000) (4597949055 / 1000000000000)
      | _ => orderedInterval (-91733674107 / 1000000000000) (-91733673393 / 1000000000000)
  coefficientTarget := fun i =>
    match i.val with
    | 0 => orderedInterval (-39058531203 / 1000000000000) (-39058527792 / 1000000000000)
    | 1 => orderedInterval (-54969363726 / 1000000000000) (-54969359984 / 1000000000000)
    | 2 => orderedInterval (27022958247 / 1000000000000) (27022964140 / 1000000000000)
    | 3 => orderedInterval (155755066022 / 1000000000000) (155755076776 / 1000000000000)
    | _ => orderedInterval (37958425419 / 1000000000000) (37958446581 / 1000000000000)

theorem compactCertificate200_stateChecks0 :
    compactCertificate200.stateChecks 0 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 29 12 (367 / 4)) (orderedInterval (-82448247165 / 1000000000000) (-82448247162 / 1000000000000), orderedInterval (-11417583665 / 1000000000000) (-11417583661 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 22 12 (540661077879667 / 8000000000000)) (orderedInterval (-66074907872 / 1000000000000) (-66074846775 / 1000000000000), orderedInterval (71580284501 / 1000000000000) (71580345598 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 35 12 (174838684003411 / 1600000000000)) (orderedInterval (-7824184704 / 1000000000000) (-7824184702 / 1000000000000), orderedInterval (-75890057346 / 1000000000000) (-75890057345 / 1000000000000))) = true
  norm_num [besselStateAtRationalPoint, besselIntervalStepZero,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, besselZeroTransition,
    besselInitial, besselGridStateAt, besselGridStateBlock00, besselGridStateBlock01,
    besselGridStateBlock02, besselGridStateBlock03, besselGridStateBlock04,
    besselGridStateBlock05, besselGridStateBlock06, besselGridStateBlock07,
    besselGridStateBlock08, besselGridStateBlock09, besselGridStateBlock10,
    besselGridStateBlock11, besselGridStateBlock12, besselGridStateBlock13,
    besselGridStateBlock14, besselGridState006, besselGridState009, besselGridState013, besselGridState016, besselGridState017, besselGridState022, besselGridState023, besselGridState025, besselGridState029, besselGridState030, besselGridState032, besselGridState034, besselGridState035, besselGridState036, besselGridState037, besselGridState038, besselGridState042, besselGridState043, besselGridState045, besselGridState046, besselGridState051, besselGridState054, besselGridState058, besselGridState063, besselGridState065, besselGridState067, besselStateSubset, linearInterval, widenInterval,
    rationalErrorInterval, rationalIntervalSubset, orderedInterval, Finset.sum_range_succ,
    IntervalRat.add, IntervalRat.mul, IntervalRat.scale, IntervalRat.singleton]

theorem compactCertificate200_stateChecks1 :
    compactCertificate200.stateChecks 3 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 6 12 (157763554097369 / 8000000000000)) (orderedInterval (179081231183 / 1000000000000) (179081231245 / 1000000000000), orderedInterval (-18747904734 / 1000000000000) (-18747904672 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 17 12 (423775097585093 / 8000000000000)) (orderedInterval (-37368612099 / 1000000000000) (-37368612098 / 1000000000000), orderedInterval (-102710718475 / 1000000000000) (-102710718474 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 46 12 (1150631825940081 / 8000000000000)) (orderedInterval (6658123401 / 1000000000000) (6658123402 / 1000000000000), orderedInterval (66172949779 / 1000000000000) (66172949780 / 1000000000000))) = true
  norm_num [besselStateAtRationalPoint, besselIntervalStepZero,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, besselZeroTransition,
    besselInitial, besselGridStateAt, besselGridStateBlock00, besselGridStateBlock01,
    besselGridStateBlock02, besselGridStateBlock03, besselGridStateBlock04,
    besselGridStateBlock05, besselGridStateBlock06, besselGridStateBlock07,
    besselGridStateBlock08, besselGridStateBlock09, besselGridStateBlock10,
    besselGridStateBlock11, besselGridStateBlock12, besselGridStateBlock13,
    besselGridStateBlock14, besselGridState006, besselGridState009, besselGridState013, besselGridState016, besselGridState017, besselGridState022, besselGridState023, besselGridState025, besselGridState029, besselGridState030, besselGridState032, besselGridState034, besselGridState035, besselGridState036, besselGridState037, besselGridState038, besselGridState042, besselGridState043, besselGridState045, besselGridState046, besselGridState051, besselGridState054, besselGridState058, besselGridState063, besselGridState065, besselGridState067, besselStateSubset, linearInterval, widenInterval,
    rationalErrorInterval, rationalIntervalSubset, orderedInterval, Finset.sum_range_succ,
    IntervalRat.add, IntervalRat.mul, IntervalRat.scale, IntervalRat.singleton]

theorem compactCertificate200_stateChecks2 :
    compactCertificate200.stateChecks 6 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 34 12 (847550195170553 / 8000000000000)) (orderedInterval (-6670455164 / 1000000000000) (-6670455140 / 1000000000000), orderedInterval (77262337128 / 1000000000000) (77262337152 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 58 12 (1452291705455069 / 8000000000000)) (orderedInterval (6430201591 / 1000000000000) (6430201592 / 1000000000000), orderedInterval (58850854496 / 1000000000000) (58850854497 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 43 12 (1069751497093271 / 8000000000000)) (orderedInterval (38105945087 / 1000000000000) (38105954920 / 1000000000000), orderedInterval (-57664911638 / 1000000000000) (-57664901805 / 1000000000000))) = true
  norm_num [besselStateAtRationalPoint, besselIntervalStepZero,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, besselZeroTransition,
    besselInitial, besselGridStateAt, besselGridStateBlock00, besselGridStateBlock01,
    besselGridStateBlock02, besselGridStateBlock03, besselGridStateBlock04,
    besselGridStateBlock05, besselGridStateBlock06, besselGridStateBlock07,
    besselGridStateBlock08, besselGridStateBlock09, besselGridStateBlock10,
    besselGridStateBlock11, besselGridStateBlock12, besselGridStateBlock13,
    besselGridStateBlock14, besselGridState006, besselGridState009, besselGridState013, besselGridState016, besselGridState017, besselGridState022, besselGridState023, besselGridState025, besselGridState029, besselGridState030, besselGridState032, besselGridState034, besselGridState035, besselGridState036, besselGridState037, besselGridState038, besselGridState042, besselGridState043, besselGridState045, besselGridState046, besselGridState051, besselGridState054, besselGridState058, besselGridState063, besselGridState065, besselGridState067, besselStateSubset, linearInterval, widenInterval,
    rationalErrorInterval, rationalIntervalSubset, orderedInterval, Finset.sum_range_succ,
    IntervalRat.add, IntervalRat.mul, IntervalRat.scale, IntervalRat.singleton]

theorem compactCertificate200_stateChecks3 :
    compactCertificate200.stateChecks 9 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 65 12 (1641273895484633 / 8000000000000)) (orderedInterval (-54904720742 / 1000000000000) (-54904720062 / 1000000000000), orderedInterval (9542047126 / 1000000000000) (9542047806 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 38 12 (947589925371857 / 8000000000000)) (orderedInterval (-10769749850 / 1000000000000) (-10769749796 / 1000000000000), orderedInterval (72562368877 / 1000000000000) (72562368932 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 67 12 (1681514951187013 / 8000000000000)) (orderedInterval (-25777403877 / 1000000000000) (-25777403876 / 1000000000000), orderedInterval (-48562972654 / 1000000000000) (-48562972653 / 1000000000000))) = true
  norm_num [besselStateAtRationalPoint, besselIntervalStepZero,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, besselZeroTransition,
    besselInitial, besselGridStateAt, besselGridStateBlock00, besselGridStateBlock01,
    besselGridStateBlock02, besselGridStateBlock03, besselGridStateBlock04,
    besselGridStateBlock05, besselGridStateBlock06, besselGridStateBlock07,
    besselGridStateBlock08, besselGridStateBlock09, besselGridStateBlock10,
    besselGridStateBlock11, besselGridStateBlock12, besselGridStateBlock13,
    besselGridStateBlock14, besselGridState006, besselGridState009, besselGridState013, besselGridState016, besselGridState017, besselGridState022, besselGridState023, besselGridState025, besselGridState029, besselGridState030, besselGridState032, besselGridState034, besselGridState035, besselGridState036, besselGridState037, besselGridState038, besselGridState042, besselGridState043, besselGridState045, besselGridState046, besselGridState051, besselGridState054, besselGridState058, besselGridState063, besselGridState065, besselGridState067, besselStateSubset, linearInterval, widenInterval,
    rationalErrorInterval, rationalIntervalSubset, orderedInterval, Finset.sum_range_succ,
    IntervalRat.add, IntervalRat.mul, IntervalRat.scale, IntervalRat.singleton]

theorem compactCertificate200_stateChecks4 :
    compactCertificate200.stateChecks 12 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 63 12 (1571089387781497 / 8000000000000)) (orderedInterval (38784576022 / 1000000000000) (38784610793 / 1000000000000), orderedInterval (-41781241331 / 1000000000000) (-41781206560 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 45 12 (1121203520032201 / 8000000000000)) (orderedInterval (28507129024 / 1000000000000) (28507130991 / 1000000000000), orderedInterval (-61173503955 / 1000000000000) (-61173501987 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 51 12 (1271325292755279 / 8000000000000)) (orderedInterval (31501312798 / 1000000000000) (31501317261 / 1000000000000), orderedInterval (-54996291124 / 1000000000000) (-54996286661 / 1000000000000))) = true
  norm_num [besselStateAtRationalPoint, besselIntervalStepZero,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, besselZeroTransition,
    besselInitial, besselGridStateAt, besselGridStateBlock00, besselGridStateBlock01,
    besselGridStateBlock02, besselGridStateBlock03, besselGridStateBlock04,
    besselGridStateBlock05, besselGridStateBlock06, besselGridStateBlock07,
    besselGridStateBlock08, besselGridStateBlock09, besselGridStateBlock10,
    besselGridStateBlock11, besselGridStateBlock12, besselGridStateBlock13,
    besselGridStateBlock14, besselGridState006, besselGridState009, besselGridState013, besselGridState016, besselGridState017, besselGridState022, besselGridState023, besselGridState025, besselGridState029, besselGridState030, besselGridState032, besselGridState034, besselGridState035, besselGridState036, besselGridState037, besselGridState038, besselGridState042, besselGridState043, besselGridState045, besselGridState046, besselGridState051, besselGridState054, besselGridState058, besselGridState063, besselGridState065, besselGridState067, besselStateSubset, linearInterval, widenInterval,
    rationalErrorInterval, rationalIntervalSubset, orderedInterval, Finset.sum_range_succ,
    IntervalRat.add, IntervalRat.mul, IntervalRat.scale, IntervalRat.singleton]

theorem compactCertificate200_stateChecks5 :
    compactCertificate200.stateChecks 15 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 42 12 (1059898486774751 / 8000000000000)) (orderedInterval (67233272703 / 1000000000000) (67233272705 / 1000000000000), orderedInterval (16622126857 / 1000000000000) (16622126858 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 37 12 (936452456561771 / 8000000000000)) (orderedInterval (-73710489654 / 1000000000000) (-73710489595 / 1000000000000), orderedInterval (2612641904 / 1000000000000) (2612641963 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 54 12 (271420421899329 / 1600000000000)) (orderedInterval (42926869664 / 1000000000000) (42926869665 / 1000000000000), orderedInterval (43578199507 / 1000000000000) (43578199508 / 1000000000000))) = true
  norm_num [besselStateAtRationalPoint, besselIntervalStepZero,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, besselZeroTransition,
    besselInitial, besselGridStateAt, besselGridStateBlock00, besselGridStateBlock01,
    besselGridStateBlock02, besselGridStateBlock03, besselGridStateBlock04,
    besselGridStateBlock05, besselGridStateBlock06, besselGridStateBlock07,
    besselGridStateBlock08, besselGridStateBlock09, besselGridStateBlock10,
    besselGridStateBlock11, besselGridStateBlock12, besselGridStateBlock13,
    besselGridStateBlock14, besselGridState006, besselGridState009, besselGridState013, besselGridState016, besselGridState017, besselGridState022, besselGridState023, besselGridState025, besselGridState029, besselGridState030, besselGridState032, besselGridState034, besselGridState035, besselGridState036, besselGridState037, besselGridState038, besselGridState042, besselGridState043, besselGridState045, besselGridState046, besselGridState051, besselGridState054, besselGridState058, besselGridState063, besselGridState065, besselGridState067, besselStateSubset, linearInterval, widenInterval,
    rationalErrorInterval, rationalIntervalSubset, orderedInterval, Finset.sum_range_succ,
    IntervalRat.add, IntervalRat.mul, IntervalRat.scale, IntervalRat.singleton]

theorem compactCertificate200_stateChecks6 :
    compactCertificate200.stateChecks 18 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 30 12 (750763171047763 / 8000000000000)) (orderedInterval (30678693285 / 1000000000000) (30678693286 / 1000000000000), orderedInterval (76273423243 / 1000000000000) (76273423244 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 25 12 (636430254571643 / 8000000000000)) (orderedInterval (-87160341903 / 1000000000000) (-87160341268 / 1000000000000), orderedInterval (20680224817 / 1000000000000) (20680225453 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 16 12 (398248502906729 / 8000000000000)) (orderedInterval (33252755748 / 1000000000000) (33252755749 / 1000000000000), orderedInterval (107754803143 / 1000000000000) (107754803144 / 1000000000000))) = true
  norm_num [besselStateAtRationalPoint, besselIntervalStepZero,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, besselZeroTransition,
    besselInitial, besselGridStateAt, besselGridStateBlock00, besselGridStateBlock01,
    besselGridStateBlock02, besselGridStateBlock03, besselGridStateBlock04,
    besselGridStateBlock05, besselGridStateBlock06, besselGridStateBlock07,
    besselGridStateBlock08, besselGridStateBlock09, besselGridStateBlock10,
    besselGridStateBlock11, besselGridStateBlock12, besselGridStateBlock13,
    besselGridStateBlock14, besselGridState006, besselGridState009, besselGridState013, besselGridState016, besselGridState017, besselGridState022, besselGridState023, besselGridState025, besselGridState029, besselGridState030, besselGridState032, besselGridState034, besselGridState035, besselGridState036, besselGridState037, besselGridState038, besselGridState042, besselGridState043, besselGridState045, besselGridState046, besselGridState051, besselGridState054, besselGridState058, besselGridState063, besselGridState065, besselGridState067, besselStateSubset, linearInterval, widenInterval,
    rationalErrorInterval, rationalIntervalSubset, orderedInterval, Finset.sum_range_succ,
    IntervalRat.add, IntervalRat.mul, IntervalRat.scale, IntervalRat.singleton]

theorem compactCertificate200_stateChecks7 :
    compactCertificate200.stateChecks 21 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 9 12 (214179369377943 / 8000000000000)) (orderedInterval (101807751706 / 1000000000000) (101807807811 / 1000000000000), orderedInterval (-117722328216 / 1000000000000) (-117722272111 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 23 12 (581538651682829 / 8000000000000)) (orderedInterval (-87862471206 / 1000000000000) (-87862471205 / 1000000000000), orderedInterval (-31609928827 / 1000000000000) (-31609928826 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 32 12 (794041311604333 / 8000000000000)) (orderedInterval (-37808305210 / 1000000000000) (-37808300724 / 1000000000000), orderedInterval (70791788698 / 1000000000000) (70791793184 / 1000000000000))) = true
  norm_num [besselStateAtRationalPoint, besselIntervalStepZero,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, besselZeroTransition,
    besselInitial, besselGridStateAt, besselGridStateBlock00, besselGridStateBlock01,
    besselGridStateBlock02, besselGridStateBlock03, besselGridStateBlock04,
    besselGridStateBlock05, besselGridStateBlock06, besselGridStateBlock07,
    besselGridStateBlock08, besselGridStateBlock09, besselGridStateBlock10,
    besselGridStateBlock11, besselGridStateBlock12, besselGridStateBlock13,
    besselGridStateBlock14, besselGridState006, besselGridState009, besselGridState013, besselGridState016, besselGridState017, besselGridState022, besselGridState023, besselGridState025, besselGridState029, besselGridState030, besselGridState032, besselGridState034, besselGridState035, besselGridState036, besselGridState037, besselGridState038, besselGridState042, besselGridState043, besselGridState045, besselGridState046, besselGridState051, besselGridState054, besselGridState058, besselGridState063, besselGridState065, besselGridState067, besselStateSubset, linearInterval, widenInterval,
    rationalErrorInterval, rationalIntervalSubset, orderedInterval, Finset.sum_range_succ,
    IntervalRat.add, IntervalRat.mul, IntervalRat.scale, IntervalRat.singleton]

theorem compactCertificate200_stateChecks8 :
    compactCertificate200.stateChecks 24 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 13 12 (335751497093271 / 8000000000000)) (orderedInterval (-116113132889 / 1000000000000) (-116113130935 / 1000000000000), orderedInterval (42440847157 / 1000000000000) (42440849111 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 54 12 (1364811195318391 / 8000000000000)) (orderedInterval (60213859930 / 1000000000000) (60213860475 / 1000000000000), orderedInterval (-10467099228 / 1000000000000) (-10467098682 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 36 12 (911630627575769 / 8000000000000)) (orderedInterval (74560478141 / 1000000000000) (74560478241 / 1000000000000), orderedInterval (-5554811040 / 1000000000000) (-5554810939 / 1000000000000))) = true
  norm_num [besselStateAtRationalPoint, besselIntervalStepZero,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, besselZeroTransition,
    besselInitial, besselGridStateAt, besselGridStateBlock00, besselGridStateBlock01,
    besselGridStateBlock02, besselGridStateBlock03, besselGridStateBlock04,
    besselGridStateBlock05, besselGridStateBlock06, besselGridStateBlock07,
    besselGridStateBlock08, besselGridStateBlock09, besselGridStateBlock10,
    besselGridStateBlock11, besselGridStateBlock12, besselGridStateBlock13,
    besselGridStateBlock14, besselGridState006, besselGridState009, besselGridState013, besselGridState016, besselGridState017, besselGridState022, besselGridState023, besselGridState025, besselGridState029, besselGridState030, besselGridState032, besselGridState034, besselGridState035, besselGridState036, besselGridState037, besselGridState038, besselGridState042, besselGridState043, besselGridState045, besselGridState046, besselGridState051, besselGridState054, besselGridState058, besselGridState063, besselGridState065, besselGridState067, besselStateSubset, linearInterval, widenInterval,
    rationalErrorInterval, rationalIntervalSubset, orderedInterval, Finset.sum_range_succ,
    IntervalRat.add, IntervalRat.mul, IntervalRat.scale, IntervalRat.singleton]

theorem compactCertificate200_states : ∀ j,
    BesselStateValid (compactCertificate200.point j) (compactCertificate200.state j) :=
  compactCertificate200.statesValid_of_checks3 compactCertificate200_stateChecks0
    compactCertificate200_stateChecks1 compactCertificate200_stateChecks2
    compactCertificate200_stateChecks3 compactCertificate200_stateChecks4
    compactCertificate200_stateChecks5 compactCertificate200_stateChecks6
    compactCertificate200_stateChecks7 compactCertificate200_stateChecks8

theorem compactCertificate200_chunkChecks0_0 :
    compactCertificate200.chunkChecks (0 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 0) <| besselDerivativeNearFromState (367 / 4) 0 (IntervalRat.scale (367 / 4) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-82448247165 / 1000000000000) (-82448247162 / 1000000000000), orderedInterval (-11417583665 / 1000000000000) (-11417583661 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 0) <| besselDerivativeNearFromState (540661077879667 / 8000000000000) 0 (IntervalRat.scale (367 / 4) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-66074907872 / 1000000000000) (-66074846775 / 1000000000000), orderedInterval (71580284501 / 1000000000000) (71580345598 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 0) <| besselDerivativeNearFromState (174838684003411 / 1600000000000) 0 (IntervalRat.scale (367 / 4) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-7824184704 / 1000000000000) (-7824184702 / 1000000000000), orderedInterval (-75890057346 / 1000000000000) (-75890057345 / 1000000000000)))) (orderedInterval (-33754420948 / 1000000000000) (-33754420370 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 0) <| besselDerivativeNearFromState (157763554097369 / 8000000000000) 0 (IntervalRat.scale (367 / 4) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (179081231183 / 1000000000000) (179081231245 / 1000000000000), orderedInterval (-18747904734 / 1000000000000) (-18747904672 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 0) <| besselDerivativeNearFromState (423775097585093 / 8000000000000) 0 (IntervalRat.scale (367 / 4) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-37368612099 / 1000000000000) (-37368612098 / 1000000000000), orderedInterval (-102710718475 / 1000000000000) (-102710718474 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 0) <| besselDerivativeNearFromState (1150631825940081 / 8000000000000) 0 (IntervalRat.scale (367 / 4) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (6658123401 / 1000000000000) (6658123402 / 1000000000000), orderedInterval (66172949779 / 1000000000000) (66172949780 / 1000000000000)))) (orderedInterval (-3780621272 / 1000000000000) (-3780621259 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 0) <| besselDerivativeNearFromState (847550195170553 / 8000000000000) 0 (IntervalRat.scale (367 / 4) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-6670455164 / 1000000000000) (-6670455140 / 1000000000000), orderedInterval (77262337128 / 1000000000000) (77262337152 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 0) <| besselDerivativeNearFromState (1452291705455069 / 8000000000000) 0 (IntervalRat.scale (367 / 4) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (6430201591 / 1000000000000) (6430201592 / 1000000000000), orderedInterval (58850854496 / 1000000000000) (58850854497 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 0) <| besselDerivativeNearFromState (1069751497093271 / 8000000000000) 0 (IntervalRat.scale (367 / 4) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (38105945087 / 1000000000000) (38105954920 / 1000000000000), orderedInterval (-57664911638 / 1000000000000) (-57664901805 / 1000000000000)))) (orderedInterval (722612362 / 1000000000000) (722612606 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate200_chunkChecks0_1 :
    compactCertificate200.chunkChecks (0 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 0) <| besselDerivativeNearFromState (1641273895484633 / 8000000000000) 0 (IntervalRat.scale (367 / 4) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-54904720742 / 1000000000000) (-54904720062 / 1000000000000), orderedInterval (9542047126 / 1000000000000) (9542047806 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 0) <| besselDerivativeNearFromState (947589925371857 / 8000000000000) 0 (IntervalRat.scale (367 / 4) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-10769749850 / 1000000000000) (-10769749796 / 1000000000000), orderedInterval (72562368877 / 1000000000000) (72562368932 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 0) <| besselDerivativeNearFromState (1681514951187013 / 8000000000000) 0 (IntervalRat.scale (367 / 4) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-25777403877 / 1000000000000) (-25777403876 / 1000000000000), orderedInterval (-48562972654 / 1000000000000) (-48562972653 / 1000000000000)))) (orderedInterval (5293546136 / 1000000000000) (5293546298 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 0) <| besselDerivativeNearFromState (1571089387781497 / 8000000000000) 0 (IntervalRat.scale (367 / 4) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (38784576022 / 1000000000000) (38784610793 / 1000000000000), orderedInterval (-41781241331 / 1000000000000) (-41781206560 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 0) <| besselDerivativeNearFromState (1121203520032201 / 8000000000000) 0 (IntervalRat.scale (367 / 4) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (28507129024 / 1000000000000) (28507130991 / 1000000000000), orderedInterval (-61173503955 / 1000000000000) (-61173501987 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 0) <| besselDerivativeNearFromState (1271325292755279 / 8000000000000) 0 (IntervalRat.scale (367 / 4) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (31501312798 / 1000000000000) (31501317261 / 1000000000000), orderedInterval (-54996291124 / 1000000000000) (-54996286661 / 1000000000000)))) (orderedInterval (1836119092 / 1000000000000) (1836119940 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 0) <| besselDerivativeNearFromState (1059898486774751 / 8000000000000) 0 (IntervalRat.scale (367 / 4) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (67233272703 / 1000000000000) (67233272705 / 1000000000000), orderedInterval (16622126857 / 1000000000000) (16622126858 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 0) <| besselDerivativeNearFromState (936452456561771 / 8000000000000) 0 (IntervalRat.scale (367 / 4) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-73710489654 / 1000000000000) (-73710489595 / 1000000000000), orderedInterval (2612641904 / 1000000000000) (2612641963 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 0) <| besselDerivativeNearFromState (271420421899329 / 1600000000000) 0 (IntervalRat.scale (367 / 4) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (42926869664 / 1000000000000) (42926869665 / 1000000000000), orderedInterval (43578199507 / 1000000000000) (43578199508 / 1000000000000)))) (orderedInterval (6093691445 / 1000000000000) (6093691459 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate200_chunkChecks0_2 :
    compactCertificate200.chunkChecks (0 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 0) <| besselDerivativeNearFromState (750763171047763 / 8000000000000) 0 (IntervalRat.scale (367 / 4) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (30678693285 / 1000000000000) (30678693286 / 1000000000000), orderedInterval (76273423243 / 1000000000000) (76273423244 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 0) <| besselDerivativeNearFromState (636430254571643 / 8000000000000) 0 (IntervalRat.scale (367 / 4) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-87160341903 / 1000000000000) (-87160341268 / 1000000000000), orderedInterval (20680224817 / 1000000000000) (20680225453 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 0) <| besselDerivativeNearFromState (398248502906729 / 8000000000000) 0 (IntervalRat.scale (367 / 4) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (33252755748 / 1000000000000) (33252755749 / 1000000000000), orderedInterval (107754803143 / 1000000000000) (107754803144 / 1000000000000)))) (orderedInterval (1110532757 / 1000000000000) (1110532817 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 0) <| besselDerivativeNearFromState (214179369377943 / 8000000000000) 0 (IntervalRat.scale (367 / 4) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (101807751706 / 1000000000000) (101807807811 / 1000000000000), orderedInterval (-117722328216 / 1000000000000) (-117722272111 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 0) <| besselDerivativeNearFromState (581538651682829 / 8000000000000) 0 (IntervalRat.scale (367 / 4) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-87862471206 / 1000000000000) (-87862471205 / 1000000000000), orderedInterval (-31609928827 / 1000000000000) (-31609928826 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 0) <| besselDerivativeNearFromState (794041311604333 / 8000000000000) 0 (IntervalRat.scale (367 / 4) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-37808305210 / 1000000000000) (-37808300724 / 1000000000000), orderedInterval (70791788698 / 1000000000000) (70791793184 / 1000000000000)))) (orderedInterval (3011016115 / 1000000000000) (3011017506 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 0) <| besselDerivativeNearFromState (335751497093271 / 8000000000000) 0 (IntervalRat.scale (367 / 4) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-116113132889 / 1000000000000) (-116113130935 / 1000000000000), orderedInterval (42440847157 / 1000000000000) (42440849111 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 0) <| besselDerivativeNearFromState (1364811195318391 / 8000000000000) 0 (IntervalRat.scale (367 / 4) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (60213859930 / 1000000000000) (60213860475 / 1000000000000), orderedInterval (-10467099228 / 1000000000000) (-10467098682 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 0) <| besselDerivativeNearFromState (911630627575769 / 8000000000000) 0 (IntervalRat.scale (367 / 4) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (74560478141 / 1000000000000) (74560478241 / 1000000000000), orderedInterval (-5554811040 / 1000000000000) (-5554810939 / 1000000000000)))) (orderedInterval (-19591006890 / 1000000000000) (-19591006789 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate200_chunkChecks0 :
    compactCertificate200.chunkChecks (0 : Fin 5) 0 9 = true :=
  compactCertificate200.chunkChecks_nine_of_three (0 : Fin 5) compactCertificate200_chunkChecks0_0
    compactCertificate200_chunkChecks0_1 compactCertificate200_chunkChecks0_2

theorem compactCertificate200_chunkChecks1_0 :
    compactCertificate200.chunkChecks (1 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 1) <| besselDerivativeNearFromState (367 / 4) 1 (IntervalRat.scale (367 / 4) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-82448247165 / 1000000000000) (-82448247162 / 1000000000000), orderedInterval (-11417583665 / 1000000000000) (-11417583661 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 1) <| besselDerivativeNearFromState (540661077879667 / 8000000000000) 1 (IntervalRat.scale (367 / 4) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-66074907872 / 1000000000000) (-66074846775 / 1000000000000), orderedInterval (71580284501 / 1000000000000) (71580345598 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 1) <| besselDerivativeNearFromState (174838684003411 / 1600000000000) 1 (IntervalRat.scale (367 / 4) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-7824184704 / 1000000000000) (-7824184702 / 1000000000000), orderedInterval (-75890057346 / 1000000000000) (-75890057345 / 1000000000000)))) (orderedInterval (-9338123852 / 1000000000000) (-9338123423 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 1) <| besselDerivativeNearFromState (157763554097369 / 8000000000000) 1 (IntervalRat.scale (367 / 4) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (179081231183 / 1000000000000) (179081231245 / 1000000000000), orderedInterval (-18747904734 / 1000000000000) (-18747904672 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 1) <| besselDerivativeNearFromState (423775097585093 / 8000000000000) 1 (IntervalRat.scale (367 / 4) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-37368612099 / 1000000000000) (-37368612098 / 1000000000000), orderedInterval (-102710718475 / 1000000000000) (-102710718474 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 1) <| besselDerivativeNearFromState (1150631825940081 / 8000000000000) 1 (IntervalRat.scale (367 / 4) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (6658123401 / 1000000000000) (6658123402 / 1000000000000), orderedInterval (66172949779 / 1000000000000) (66172949780 / 1000000000000)))) (orderedInterval (-9495837917 / 1000000000000) (-9495837903 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 1) <| besselDerivativeNearFromState (847550195170553 / 8000000000000) 1 (IntervalRat.scale (367 / 4) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-6670455164 / 1000000000000) (-6670455140 / 1000000000000), orderedInterval (77262337128 / 1000000000000) (77262337152 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 1) <| besselDerivativeNearFromState (1452291705455069 / 8000000000000) 1 (IntervalRat.scale (367 / 4) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (6430201591 / 1000000000000) (6430201592 / 1000000000000), orderedInterval (58850854496 / 1000000000000) (58850854497 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 1) <| besselDerivativeNearFromState (1069751497093271 / 8000000000000) 1 (IntervalRat.scale (367 / 4) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (38105945087 / 1000000000000) (38105954920 / 1000000000000), orderedInterval (-57664911638 / 1000000000000) (-57664901805 / 1000000000000)))) (orderedInterval (-5622683849 / 1000000000000) (-5622683493 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate200_chunkChecks1_1 :
    compactCertificate200.chunkChecks (1 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 1) <| besselDerivativeNearFromState (1641273895484633 / 8000000000000) 1 (IntervalRat.scale (367 / 4) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-54904720742 / 1000000000000) (-54904720062 / 1000000000000), orderedInterval (9542047126 / 1000000000000) (9542047806 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 1) <| besselDerivativeNearFromState (947589925371857 / 8000000000000) 1 (IntervalRat.scale (367 / 4) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-10769749850 / 1000000000000) (-10769749796 / 1000000000000), orderedInterval (72562368877 / 1000000000000) (72562368932 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 1) <| besselDerivativeNearFromState (1681514951187013 / 8000000000000) 1 (IntervalRat.scale (367 / 4) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-25777403877 / 1000000000000) (-25777403876 / 1000000000000), orderedInterval (-48562972654 / 1000000000000) (-48562972653 / 1000000000000)))) (orderedInterval (-12665731918 / 1000000000000) (-12665731566 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 1) <| besselDerivativeNearFromState (1571089387781497 / 8000000000000) 1 (IntervalRat.scale (367 / 4) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (38784576022 / 1000000000000) (38784610793 / 1000000000000), orderedInterval (-41781241331 / 1000000000000) (-41781206560 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 1) <| besselDerivativeNearFromState (1121203520032201 / 8000000000000) 1 (IntervalRat.scale (367 / 4) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (28507129024 / 1000000000000) (28507130991 / 1000000000000), orderedInterval (-61173503955 / 1000000000000) (-61173501987 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 1) <| besselDerivativeNearFromState (1271325292755279 / 8000000000000) 1 (IntervalRat.scale (367 / 4) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (31501312798 / 1000000000000) (31501317261 / 1000000000000), orderedInterval (-54996291124 / 1000000000000) (-54996286661 / 1000000000000)))) (orderedInterval (-6739790013 / 1000000000000) (-6739788327 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 1) <| besselDerivativeNearFromState (1059898486774751 / 8000000000000) 1 (IntervalRat.scale (367 / 4) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (67233272703 / 1000000000000) (67233272705 / 1000000000000), orderedInterval (16622126857 / 1000000000000) (16622126858 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 1) <| besselDerivativeNearFromState (936452456561771 / 8000000000000) 1 (IntervalRat.scale (367 / 4) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-73710489654 / 1000000000000) (-73710489595 / 1000000000000), orderedInterval (2612641904 / 1000000000000) (2612641963 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 1) <| besselDerivativeNearFromState (271420421899329 / 1600000000000) 1 (IntervalRat.scale (367 / 4) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (42926869664 / 1000000000000) (42926869665 / 1000000000000), orderedInterval (43578199507 / 1000000000000) (43578199508 / 1000000000000)))) (orderedInterval (2149389394 / 1000000000000) (2149389412 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate200_chunkChecks1_2 :
    compactCertificate200.chunkChecks (1 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 1) <| besselDerivativeNearFromState (750763171047763 / 8000000000000) 1 (IntervalRat.scale (367 / 4) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (30678693285 / 1000000000000) (30678693286 / 1000000000000), orderedInterval (76273423243 / 1000000000000) (76273423244 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 1) <| besselDerivativeNearFromState (636430254571643 / 8000000000000) 1 (IntervalRat.scale (367 / 4) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-87160341903 / 1000000000000) (-87160341268 / 1000000000000), orderedInterval (20680224817 / 1000000000000) (20680225453 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 1) <| besselDerivativeNearFromState (398248502906729 / 8000000000000) 1 (IntervalRat.scale (367 / 4) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (33252755748 / 1000000000000) (33252755749 / 1000000000000), orderedInterval (107754803143 / 1000000000000) (107754803144 / 1000000000000)))) (orderedInterval (-11585635205 / 1000000000000) (-11585635151 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 1) <| besselDerivativeNearFromState (214179369377943 / 8000000000000) 1 (IntervalRat.scale (367 / 4) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (101807751706 / 1000000000000) (101807807811 / 1000000000000), orderedInterval (-117722328216 / 1000000000000) (-117722272111 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 1) <| besselDerivativeNearFromState (581538651682829 / 8000000000000) 1 (IntervalRat.scale (367 / 4) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-87862471206 / 1000000000000) (-87862471205 / 1000000000000), orderedInterval (-31609928827 / 1000000000000) (-31609928826 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 1) <| besselDerivativeNearFromState (794041311604333 / 8000000000000) 1 (IntervalRat.scale (367 / 4) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-37808305210 / 1000000000000) (-37808300724 / 1000000000000), orderedInterval (70791788698 / 1000000000000) (70791793184 / 1000000000000)))) (orderedInterval (-4666732548 / 1000000000000) (-4666731863 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 1) <| besselDerivativeNearFromState (335751497093271 / 8000000000000) 1 (IntervalRat.scale (367 / 4) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-116113132889 / 1000000000000) (-116113130935 / 1000000000000), orderedInterval (42440847157 / 1000000000000) (42440849111 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 1) <| besselDerivativeNearFromState (1364811195318391 / 8000000000000) 1 (IntervalRat.scale (367 / 4) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (60213859930 / 1000000000000) (60213860475 / 1000000000000), orderedInterval (-10467099228 / 1000000000000) (-10467098682 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 1) <| besselDerivativeNearFromState (911630627575769 / 8000000000000) 1 (IntervalRat.scale (367 / 4) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (74560478141 / 1000000000000) (74560478241 / 1000000000000), orderedInterval (-5554811040 / 1000000000000) (-5554810939 / 1000000000000)))) (orderedInterval (2995782182 / 1000000000000) (2995782330 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate200_chunkChecks1 :
    compactCertificate200.chunkChecks (1 : Fin 5) 0 9 = true :=
  compactCertificate200.chunkChecks_nine_of_three (1 : Fin 5) compactCertificate200_chunkChecks1_0
    compactCertificate200_chunkChecks1_1 compactCertificate200_chunkChecks1_2

theorem compactCertificate200_chunkChecks2_0 :
    compactCertificate200.chunkChecks (2 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 2) <| besselDerivativeNearFromState (367 / 4) 2 (IntervalRat.scale (367 / 4) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-82448247165 / 1000000000000) (-82448247162 / 1000000000000), orderedInterval (-11417583665 / 1000000000000) (-11417583661 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 2) <| besselDerivativeNearFromState (540661077879667 / 8000000000000) 2 (IntervalRat.scale (367 / 4) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-66074907872 / 1000000000000) (-66074846775 / 1000000000000), orderedInterval (71580284501 / 1000000000000) (71580345598 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 2) <| besselDerivativeNearFromState (174838684003411 / 1600000000000) 2 (IntervalRat.scale (367 / 4) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-7824184704 / 1000000000000) (-7824184702 / 1000000000000), orderedInterval (-75890057346 / 1000000000000) (-75890057345 / 1000000000000)))) (orderedInterval (33766702453 / 1000000000000) (33766702777 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 2) <| besselDerivativeNearFromState (157763554097369 / 8000000000000) 2 (IntervalRat.scale (367 / 4) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (179081231183 / 1000000000000) (179081231245 / 1000000000000), orderedInterval (-18747904734 / 1000000000000) (-18747904672 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 2) <| besselDerivativeNearFromState (423775097585093 / 8000000000000) 2 (IntervalRat.scale (367 / 4) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-37368612099 / 1000000000000) (-37368612098 / 1000000000000), orderedInterval (-102710718475 / 1000000000000) (-102710718474 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 2) <| besselDerivativeNearFromState (1150631825940081 / 8000000000000) 2 (IntervalRat.scale (367 / 4) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (6658123401 / 1000000000000) (6658123402 / 1000000000000), orderedInterval (66172949779 / 1000000000000) (66172949780 / 1000000000000)))) (orderedInterval (1811210769 / 1000000000000) (1811210787 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 2) <| besselDerivativeNearFromState (847550195170553 / 8000000000000) 2 (IntervalRat.scale (367 / 4) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-6670455164 / 1000000000000) (-6670455140 / 1000000000000), orderedInterval (77262337128 / 1000000000000) (77262337152 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 2) <| besselDerivativeNearFromState (1452291705455069 / 8000000000000) 2 (IntervalRat.scale (367 / 4) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (6430201591 / 1000000000000) (6430201592 / 1000000000000), orderedInterval (58850854496 / 1000000000000) (58850854497 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 2) <| besselDerivativeNearFromState (1069751497093271 / 8000000000000) 2 (IntervalRat.scale (367 / 4) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (38105945087 / 1000000000000) (38105954920 / 1000000000000), orderedInterval (-57664911638 / 1000000000000) (-57664901805 / 1000000000000)))) (orderedInterval (-1118447137 / 1000000000000) (-1118446612 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate200_chunkChecks2_1 :
    compactCertificate200.chunkChecks (2 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 2) <| besselDerivativeNearFromState (1641273895484633 / 8000000000000) 2 (IntervalRat.scale (367 / 4) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-54904720742 / 1000000000000) (-54904720062 / 1000000000000), orderedInterval (9542047126 / 1000000000000) (9542047806 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 2) <| besselDerivativeNearFromState (947589925371857 / 8000000000000) 2 (IntervalRat.scale (367 / 4) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-10769749850 / 1000000000000) (-10769749796 / 1000000000000), orderedInterval (72562368877 / 1000000000000) (72562368932 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 2) <| besselDerivativeNearFromState (1681514951187013 / 8000000000000) 2 (IntervalRat.scale (367 / 4) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-25777403877 / 1000000000000) (-25777403876 / 1000000000000), orderedInterval (-48562972654 / 1000000000000) (-48562972653 / 1000000000000)))) (orderedInterval (-28080057245 / 1000000000000) (-28080056468 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 2) <| besselDerivativeNearFromState (1571089387781497 / 8000000000000) 2 (IntervalRat.scale (367 / 4) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (38784576022 / 1000000000000) (38784610793 / 1000000000000), orderedInterval (-41781241331 / 1000000000000) (-41781206560 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 2) <| besselDerivativeNearFromState (1121203520032201 / 8000000000000) 2 (IntervalRat.scale (367 / 4) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (28507129024 / 1000000000000) (28507130991 / 1000000000000), orderedInterval (-61173503955 / 1000000000000) (-61173501987 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 2) <| besselDerivativeNearFromState (1271325292755279 / 8000000000000) 2 (IntervalRat.scale (367 / 4) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (31501312798 / 1000000000000) (31501317261 / 1000000000000), orderedInterval (-54996291124 / 1000000000000) (-54996286661 / 1000000000000)))) (orderedInterval (-2530406303 / 1000000000000) (-2530402877 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 2) <| besselDerivativeNearFromState (1059898486774751 / 8000000000000) 2 (IntervalRat.scale (367 / 4) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (67233272703 / 1000000000000) (67233272705 / 1000000000000), orderedInterval (16622126857 / 1000000000000) (16622126858 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 2) <| besselDerivativeNearFromState (936452456561771 / 8000000000000) 2 (IntervalRat.scale (367 / 4) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-73710489654 / 1000000000000) (-73710489595 / 1000000000000), orderedInterval (2612641904 / 1000000000000) (2612641963 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 2) <| besselDerivativeNearFromState (271420421899329 / 1600000000000) 2 (IntervalRat.scale (367 / 4) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (42926869664 / 1000000000000) (42926869665 / 1000000000000), orderedInterval (43578199507 / 1000000000000) (43578199508 / 1000000000000)))) (orderedInterval (-12265602931 / 1000000000000) (-12265602906 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate200_chunkChecks2_2 :
    compactCertificate200.chunkChecks (2 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 2) <| besselDerivativeNearFromState (750763171047763 / 8000000000000) 2 (IntervalRat.scale (367 / 4) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (30678693285 / 1000000000000) (30678693286 / 1000000000000), orderedInterval (76273423243 / 1000000000000) (76273423244 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 2) <| besselDerivativeNearFromState (636430254571643 / 8000000000000) 2 (IntervalRat.scale (367 / 4) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-87160341903 / 1000000000000) (-87160341268 / 1000000000000), orderedInterval (20680224817 / 1000000000000) (20680225453 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 2) <| besselDerivativeNearFromState (398248502906729 / 8000000000000) 2 (IntervalRat.scale (367 / 4) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (33252755748 / 1000000000000) (33252755749 / 1000000000000), orderedInterval (107754803143 / 1000000000000) (107754803144 / 1000000000000)))) (orderedInterval (1230596230 / 1000000000000) (1230596279 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 2) <| besselDerivativeNearFromState (214179369377943 / 8000000000000) 2 (IntervalRat.scale (367 / 4) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (101807751706 / 1000000000000) (101807807811 / 1000000000000), orderedInterval (-117722328216 / 1000000000000) (-117722272111 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 2) <| besselDerivativeNearFromState (581538651682829 / 8000000000000) 2 (IntervalRat.scale (367 / 4) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-87862471206 / 1000000000000) (-87862471205 / 1000000000000), orderedInterval (-31609928827 / 1000000000000) (-31609928826 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 2) <| besselDerivativeNearFromState (794041311604333 / 8000000000000) 2 (IntervalRat.scale (367 / 4) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-37808305210 / 1000000000000) (-37808300724 / 1000000000000), orderedInterval (70791788698 / 1000000000000) (70791793184 / 1000000000000)))) (orderedInterval (-4431338330 / 1000000000000) (-4431337821 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 2) <| besselDerivativeNearFromState (335751497093271 / 8000000000000) 2 (IntervalRat.scale (367 / 4) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-116113132889 / 1000000000000) (-116113130935 / 1000000000000), orderedInterval (42440847157 / 1000000000000) (42440849111 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 2) <| besselDerivativeNearFromState (1364811195318391 / 8000000000000) 2 (IntervalRat.scale (367 / 4) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (60213859930 / 1000000000000) (60213860475 / 1000000000000), orderedInterval (-10467099228 / 1000000000000) (-10467098682 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 2) <| besselDerivativeNearFromState (911630627575769 / 8000000000000) 2 (IntervalRat.scale (367 / 4) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (74560478141 / 1000000000000) (74560478241 / 1000000000000), orderedInterval (-5554811040 / 1000000000000) (-5554810939 / 1000000000000)))) (orderedInterval (38640300741 / 1000000000000) (38640300981 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate200_chunkChecks2 :
    compactCertificate200.chunkChecks (2 : Fin 5) 0 9 = true :=
  compactCertificate200.chunkChecks_nine_of_three (2 : Fin 5) compactCertificate200_chunkChecks2_0
    compactCertificate200_chunkChecks2_1 compactCertificate200_chunkChecks2_2

theorem compactCertificate200_chunkChecks3_0 :
    compactCertificate200.chunkChecks (3 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 3) <| besselDerivativeNearFromState (367 / 4) 3 (IntervalRat.scale (367 / 4) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-82448247165 / 1000000000000) (-82448247162 / 1000000000000), orderedInterval (-11417583665 / 1000000000000) (-11417583661 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 3) <| besselDerivativeNearFromState (540661077879667 / 8000000000000) 3 (IntervalRat.scale (367 / 4) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-66074907872 / 1000000000000) (-66074846775 / 1000000000000), orderedInterval (71580284501 / 1000000000000) (71580345598 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 3) <| besselDerivativeNearFromState (174838684003411 / 1600000000000) 3 (IntervalRat.scale (367 / 4) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-7824184704 / 1000000000000) (-7824184702 / 1000000000000), orderedInterval (-75890057346 / 1000000000000) (-75890057345 / 1000000000000)))) (orderedInterval (11413288613 / 1000000000000) (11413288856 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 3) <| besselDerivativeNearFromState (157763554097369 / 8000000000000) 3 (IntervalRat.scale (367 / 4) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (179081231183 / 1000000000000) (179081231245 / 1000000000000), orderedInterval (-18747904734 / 1000000000000) (-18747904672 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 3) <| besselDerivativeNearFromState (423775097585093 / 8000000000000) 3 (IntervalRat.scale (367 / 4) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-37368612099 / 1000000000000) (-37368612098 / 1000000000000), orderedInterval (-102710718475 / 1000000000000) (-102710718474 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 3) <| besselDerivativeNearFromState (1150631825940081 / 8000000000000) 3 (IntervalRat.scale (367 / 4) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (6658123401 / 1000000000000) (6658123402 / 1000000000000), orderedInterval (66172949779 / 1000000000000) (66172949780 / 1000000000000)))) (orderedInterval (18820896919 / 1000000000000) (18820896946 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 3) <| besselDerivativeNearFromState (847550195170553 / 8000000000000) 3 (IntervalRat.scale (367 / 4) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-6670455164 / 1000000000000) (-6670455140 / 1000000000000), orderedInterval (77262337128 / 1000000000000) (77262337152 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 3) <| besselDerivativeNearFromState (1452291705455069 / 8000000000000) 3 (IntervalRat.scale (367 / 4) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (6430201591 / 1000000000000) (6430201592 / 1000000000000), orderedInterval (58850854496 / 1000000000000) (58850854497 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 3) <| besselDerivativeNearFromState (1069751497093271 / 8000000000000) 3 (IntervalRat.scale (367 / 4) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (38105945087 / 1000000000000) (38105954920 / 1000000000000), orderedInterval (-57664911638 / 1000000000000) (-57664901805 / 1000000000000)))) (orderedInterval (18386225432 / 1000000000000) (18386226203 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate200_chunkChecks3_1 :
    compactCertificate200.chunkChecks (3 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 3) <| besselDerivativeNearFromState (1641273895484633 / 8000000000000) 3 (IntervalRat.scale (367 / 4) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-54904720742 / 1000000000000) (-54904720062 / 1000000000000), orderedInterval (9542047126 / 1000000000000) (9542047806 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 3) <| besselDerivativeNearFromState (947589925371857 / 8000000000000) 3 (IntervalRat.scale (367 / 4) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-10769749850 / 1000000000000) (-10769749796 / 1000000000000), orderedInterval (72562368877 / 1000000000000) (72562368932 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 3) <| besselDerivativeNearFromState (1681514951187013 / 8000000000000) 3 (IntervalRat.scale (367 / 4) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-25777403877 / 1000000000000) (-25777403876 / 1000000000000), orderedInterval (-48562972654 / 1000000000000) (-48562972653 / 1000000000000)))) (orderedInterval (90694141104 / 1000000000000) (90694142827 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 3) <| besselDerivativeNearFromState (1571089387781497 / 8000000000000) 3 (IntervalRat.scale (367 / 4) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (38784576022 / 1000000000000) (38784610793 / 1000000000000), orderedInterval (-41781241331 / 1000000000000) (-41781206560 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 3) <| besselDerivativeNearFromState (1121203520032201 / 8000000000000) 3 (IntervalRat.scale (367 / 4) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (28507129024 / 1000000000000) (28507130991 / 1000000000000), orderedInterval (-61173503955 / 1000000000000) (-61173501987 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 3) <| besselDerivativeNearFromState (1271325292755279 / 8000000000000) 3 (IntervalRat.scale (367 / 4) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (31501312798 / 1000000000000) (31501317261 / 1000000000000), orderedInterval (-54996291124 / 1000000000000) (-54996286661 / 1000000000000)))) (orderedInterval (11801888129 / 1000000000000) (11801895153 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 3) <| besselDerivativeNearFromState (1059898486774751 / 8000000000000) 3 (IntervalRat.scale (367 / 4) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (67233272703 / 1000000000000) (67233272705 / 1000000000000), orderedInterval (16622126857 / 1000000000000) (16622126858 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 3) <| besselDerivativeNearFromState (936452456561771 / 8000000000000) 3 (IntervalRat.scale (367 / 4) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-73710489654 / 1000000000000) (-73710489595 / 1000000000000), orderedInterval (2612641904 / 1000000000000) (2612641963 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 3) <| besselDerivativeNearFromState (271420421899329 / 1600000000000) 3 (IntervalRat.scale (367 / 4) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (42926869664 / 1000000000000) (42926869665 / 1000000000000), orderedInterval (43578199507 / 1000000000000) (43578199508 / 1000000000000)))) (orderedInterval (-7185730270 / 1000000000000) (-7185730233 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate200_chunkChecks3_2 :
    compactCertificate200.chunkChecks (3 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 3) <| besselDerivativeNearFromState (750763171047763 / 8000000000000) 3 (IntervalRat.scale (367 / 4) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (30678693285 / 1000000000000) (30678693286 / 1000000000000), orderedInterval (76273423243 / 1000000000000) (76273423244 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 3) <| besselDerivativeNearFromState (636430254571643 / 8000000000000) 3 (IntervalRat.scale (367 / 4) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-87160341903 / 1000000000000) (-87160341268 / 1000000000000), orderedInterval (20680224817 / 1000000000000) (20680225453 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 3) <| besselDerivativeNearFromState (398248502906729 / 8000000000000) 3 (IntervalRat.scale (367 / 4) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (33252755748 / 1000000000000) (33252755749 / 1000000000000), orderedInterval (107754803143 / 1000000000000) (107754803144 / 1000000000000)))) (orderedInterval (13238257144 / 1000000000000) (13238257188 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 3) <| besselDerivativeNearFromState (214179369377943 / 8000000000000) 3 (IntervalRat.scale (367 / 4) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (101807751706 / 1000000000000) (101807807811 / 1000000000000), orderedInterval (-117722328216 / 1000000000000) (-117722272111 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 3) <| besselDerivativeNearFromState (581538651682829 / 8000000000000) 3 (IntervalRat.scale (367 / 4) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-87862471206 / 1000000000000) (-87862471205 / 1000000000000), orderedInterval (-31609928827 / 1000000000000) (-31609928826 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 3) <| besselDerivativeNearFromState (794041311604333 / 8000000000000) 3 (IntervalRat.scale (367 / 4) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-37808305210 / 1000000000000) (-37808300724 / 1000000000000), orderedInterval (70791788698 / 1000000000000) (70791793184 / 1000000000000)))) (orderedInterval (6505760164 / 1000000000000) (6505760642 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 3) <| besselDerivativeNearFromState (335751497093271 / 8000000000000) 3 (IntervalRat.scale (367 / 4) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-116113132889 / 1000000000000) (-116113130935 / 1000000000000), orderedInterval (42440847157 / 1000000000000) (42440849111 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 3) <| besselDerivativeNearFromState (1364811195318391 / 8000000000000) 3 (IntervalRat.scale (367 / 4) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (60213859930 / 1000000000000) (60213860475 / 1000000000000), orderedInterval (-10467099228 / 1000000000000) (-10467098682 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 3) <| besselDerivativeNearFromState (911630627575769 / 8000000000000) 3 (IntervalRat.scale (367 / 4) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (74560478141 / 1000000000000) (74560478241 / 1000000000000), orderedInterval (-5554811040 / 1000000000000) (-5554810939 / 1000000000000)))) (orderedInterval (-7919661213 / 1000000000000) (-7919660806 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate200_chunkChecks3 :
    compactCertificate200.chunkChecks (3 : Fin 5) 0 9 = true :=
  compactCertificate200.chunkChecks_nine_of_three (3 : Fin 5) compactCertificate200_chunkChecks3_0
    compactCertificate200_chunkChecks3_1 compactCertificate200_chunkChecks3_2

theorem compactCertificate200_chunkChecks4_0 :
    compactCertificate200.chunkChecks (4 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 4) <| besselDerivativeNearFromState (367 / 4) 4 (IntervalRat.scale (367 / 4) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-82448247165 / 1000000000000) (-82448247162 / 1000000000000), orderedInterval (-11417583665 / 1000000000000) (-11417583661 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 4) <| besselDerivativeNearFromState (540661077879667 / 8000000000000) 4 (IntervalRat.scale (367 / 4) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-66074907872 / 1000000000000) (-66074846775 / 1000000000000), orderedInterval (71580284501 / 1000000000000) (71580345598 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 4) <| besselDerivativeNearFromState (174838684003411 / 1600000000000) 4 (IntervalRat.scale (367 / 4) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-7824184704 / 1000000000000) (-7824184702 / 1000000000000), orderedInterval (-75890057346 / 1000000000000) (-75890057345 / 1000000000000)))) (orderedInterval (-34029428595 / 1000000000000) (-34029428409 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 4) <| besselDerivativeNearFromState (157763554097369 / 8000000000000) 4 (IntervalRat.scale (367 / 4) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (179081231183 / 1000000000000) (179081231245 / 1000000000000), orderedInterval (-18747904734 / 1000000000000) (-18747904672 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 4) <| besselDerivativeNearFromState (423775097585093 / 8000000000000) 4 (IntervalRat.scale (367 / 4) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-37368612099 / 1000000000000) (-37368612098 / 1000000000000), orderedInterval (-102710718475 / 1000000000000) (-102710718474 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 4) <| besselDerivativeNearFromState (1150631825940081 / 8000000000000) 4 (IntervalRat.scale (367 / 4) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (6658123401 / 1000000000000) (6658123402 / 1000000000000), orderedInterval (66172949779 / 1000000000000) (66172949780 / 1000000000000)))) (orderedInterval (-3424159838 / 1000000000000) (-3424159797 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 4) <| besselDerivativeNearFromState (847550195170553 / 8000000000000) 4 (IntervalRat.scale (367 / 4) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-6670455164 / 1000000000000) (-6670455140 / 1000000000000), orderedInterval (77262337128 / 1000000000000) (77262337152 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 4) <| besselDerivativeNearFromState (1452291705455069 / 8000000000000) 4 (IntervalRat.scale (367 / 4) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (6430201591 / 1000000000000) (6430201592 / 1000000000000), orderedInterval (58850854496 / 1000000000000) (58850854497 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 4) <| besselDerivativeNearFromState (1069751497093271 / 8000000000000) 4 (IntervalRat.scale (367 / 4) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (38105945087 / 1000000000000) (38105954920 / 1000000000000), orderedInterval (-57664911638 / 1000000000000) (-57664901805 / 1000000000000)))) (orderedInterval (714512722 / 1000000000000) (714513865 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate200_chunkChecks4_1 :
    compactCertificate200.chunkChecks (4 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 4) <| besselDerivativeNearFromState (1641273895484633 / 8000000000000) 4 (IntervalRat.scale (367 / 4) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-54904720742 / 1000000000000) (-54904720062 / 1000000000000), orderedInterval (9542047126 / 1000000000000) (9542047806 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 4) <| besselDerivativeNearFromState (947589925371857 / 8000000000000) 4 (IntervalRat.scale (367 / 4) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-10769749850 / 1000000000000) (-10769749796 / 1000000000000), orderedInterval (72562368877 / 1000000000000) (72562368932 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 4) <| besselDerivativeNearFromState (1681514951187013 / 8000000000000) 4 (IntervalRat.scale (367 / 4) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-25777403877 / 1000000000000) (-25777403876 / 1000000000000), orderedInterval (-48562972654 / 1000000000000) (-48562972653 / 1000000000000)))) (orderedInterval (138770242956 / 1000000000000) (138770246808 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 4) <| besselDerivativeNearFromState (1571089387781497 / 8000000000000) 4 (IntervalRat.scale (367 / 4) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (38784576022 / 1000000000000) (38784610793 / 1000000000000), orderedInterval (-41781241331 / 1000000000000) (-41781206560 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 4) <| besselDerivativeNearFromState (1121203520032201 / 8000000000000) 4 (IntervalRat.scale (367 / 4) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (28507129024 / 1000000000000) (28507130991 / 1000000000000), orderedInterval (-61173503955 / 1000000000000) (-61173501987 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 4) <| besselDerivativeNearFromState (1271325292755279 / 8000000000000) 4 (IntervalRat.scale (367 / 4) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (31501312798 / 1000000000000) (31501317261 / 1000000000000), orderedInterval (-54996291124 / 1000000000000) (-54996286661 / 1000000000000)))) (orderedInterval (-1712664142 / 1000000000000) (-1712649513 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 4) <| besselDerivativeNearFromState (1059898486774751 / 8000000000000) 4 (IntervalRat.scale (367 / 4) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (67233272703 / 1000000000000) (67233272705 / 1000000000000), orderedInterval (16622126857 / 1000000000000) (16622126858 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 4) <| besselDerivativeNearFromState (936452456561771 / 8000000000000) 4 (IntervalRat.scale (367 / 4) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-73710489654 / 1000000000000) (-73710489595 / 1000000000000), orderedInterval (2612641904 / 1000000000000) (2612641963 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 4) <| besselDerivativeNearFromState (271420421899329 / 1600000000000) 4 (IntervalRat.scale (367 / 4) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (42926869664 / 1000000000000) (42926869665 / 1000000000000), orderedInterval (43578199507 / 1000000000000) (43578199508 / 1000000000000)))) (orderedInterval (27550836224 / 1000000000000) (27550836281 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate200_chunkChecks4_2 :
    compactCertificate200.chunkChecks (4 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 4) <| besselDerivativeNearFromState (750763171047763 / 8000000000000) 4 (IntervalRat.scale (367 / 4) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (30678693285 / 1000000000000) (30678693286 / 1000000000000), orderedInterval (76273423243 / 1000000000000) (76273423244 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 4) <| besselDerivativeNearFromState (636430254571643 / 8000000000000) 4 (IntervalRat.scale (367 / 4) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-87160341903 / 1000000000000) (-87160341268 / 1000000000000), orderedInterval (20680224817 / 1000000000000) (20680225453 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 4) <| besselDerivativeNearFromState (398248502906729 / 8000000000000) 4 (IntervalRat.scale (367 / 4) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (33252755748 / 1000000000000) (33252755749 / 1000000000000), orderedInterval (107754803143 / 1000000000000) (107754803144 / 1000000000000)))) (orderedInterval (-2775188357 / 1000000000000) (-2775188316 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 4) <| besselDerivativeNearFromState (214179369377943 / 8000000000000) 4 (IntervalRat.scale (367 / 4) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (101807751706 / 1000000000000) (101807807811 / 1000000000000), orderedInterval (-117722328216 / 1000000000000) (-117722272111 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 4) <| besselDerivativeNearFromState (581538651682829 / 8000000000000) 4 (IntervalRat.scale (367 / 4) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-87862471206 / 1000000000000) (-87862471205 / 1000000000000), orderedInterval (-31609928827 / 1000000000000) (-31609928826 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 4) <| besselDerivativeNearFromState (794041311604333 / 8000000000000) 4 (IntervalRat.scale (367 / 4) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-37808305210 / 1000000000000) (-37808300724 / 1000000000000), orderedInterval (70791788698 / 1000000000000) (70791793184 / 1000000000000)))) (orderedInterval (4597948556 / 1000000000000) (4597949055 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 4) <| besselDerivativeNearFromState (335751497093271 / 8000000000000) 4 (IntervalRat.scale (367 / 4) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-116113132889 / 1000000000000) (-116113130935 / 1000000000000), orderedInterval (42440847157 / 1000000000000) (42440849111 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 4) <| besselDerivativeNearFromState (1364811195318391 / 8000000000000) 4 (IntervalRat.scale (367 / 4) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (60213859930 / 1000000000000) (60213860475 / 1000000000000), orderedInterval (-10467099228 / 1000000000000) (-10467098682 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 4) <| besselDerivativeNearFromState (911630627575769 / 8000000000000) 4 (IntervalRat.scale (367 / 4) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (74560478141 / 1000000000000) (74560478241 / 1000000000000), orderedInterval (-5554811040 / 1000000000000) (-5554810939 / 1000000000000)))) (orderedInterval (-91733674107 / 1000000000000) (-91733673393 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate200_chunkChecks4 :
    compactCertificate200.chunkChecks (4 : Fin 5) 0 9 = true :=
  compactCertificate200.chunkChecks_nine_of_three (4 : Fin 5) compactCertificate200_chunkChecks4_0
    compactCertificate200_chunkChecks4_1 compactCertificate200_chunkChecks4_2

theorem compactCertificate200_chunks :
    ∀ r : Fin 5, ∀ b, compactCertificate200.chunkCheck r b = true :=
  compactCertificate200.chunkChecks_all (by
    intro r
    fin_cases r
    · exact compactCertificate200_chunkChecks0
    · exact compactCertificate200_chunkChecks1
    · exact compactCertificate200_chunkChecks2
    · exact compactCertificate200_chunkChecks3
    · exact compactCertificate200_chunkChecks4)

theorem compactCertificate200_coefficient0 :
    compactCertificate200.coefficientCheck (0 : Fin 5) = true := by
  norm_num [CompactCertificate.coefficientCheck, intervalFinSumHull,
    compactCertificate200, rationalIntervalSubset, orderedInterval, Fin.sum_univ_succ]

theorem compactCertificate200_coefficient1 :
    compactCertificate200.coefficientCheck (1 : Fin 5) = true := by
  norm_num [CompactCertificate.coefficientCheck, intervalFinSumHull,
    compactCertificate200, rationalIntervalSubset, orderedInterval, Fin.sum_univ_succ]

theorem compactCertificate200_coefficient2 :
    compactCertificate200.coefficientCheck (2 : Fin 5) = true := by
  norm_num [CompactCertificate.coefficientCheck, intervalFinSumHull,
    compactCertificate200, rationalIntervalSubset, orderedInterval, Fin.sum_univ_succ]

theorem compactCertificate200_coefficient3 :
    compactCertificate200.coefficientCheck (3 : Fin 5) = true := by
  norm_num [CompactCertificate.coefficientCheck, intervalFinSumHull,
    compactCertificate200, rationalIntervalSubset, orderedInterval, Fin.sum_univ_succ]

theorem compactCertificate200_coefficient4 :
    compactCertificate200.coefficientCheck (4 : Fin 5) = true := by
  norm_num [CompactCertificate.coefficientCheck, intervalFinSumHull,
    compactCertificate200, rationalIntervalSubset, orderedInterval, Fin.sum_univ_succ]

theorem compactCertificate200_coefficients : ∀ r : Fin 5,
    compactCertificate200.coefficientCheck r = true := by
  intro r
  fin_cases r
  · exact compactCertificate200_coefficient0
  · exact compactCertificate200_coefficient1
  · exact compactCertificate200_coefficient2
  · exact compactCertificate200_coefficient3
  · exact compactCertificate200_coefficient4

theorem compactCertificate200_lower : (1 : ℚ) ≤ compactCertificate200.output.lo := by
  norm_num [CompactCertificate.output, CompactCertificate.interval,
    CompactCertificate.coefficientTargetNat, compactCertificate200, dualConstant,
    intervalTaylorSum, intervalPow, intervalSub, intervalMaxAbs, widenInterval,
    rationalErrorInterval, orderedInterval, IntervalRat.add, IntervalRat.mul, IntervalRat.scale,
    IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4]

theorem compactCertificate200_proves {t : ℝ} (ht : t ∈ compactCertificate200.interval) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t :=
  compactCertificate200.proves compactCertificate200_states compactCertificate200_chunks
    compactCertificate200_coefficients compactCertificate200_lower ht

end Erdos232
