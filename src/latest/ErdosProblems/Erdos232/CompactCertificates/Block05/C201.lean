/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, OpenAI Codex
-/
import ErdosProblems.Erdos232.CompactBase

open LeanCert.Core
namespace Erdos232

def compactCertificate201 : CompactCertificate where
  left := 92
  right := 369 / 4
  center := 737 / 8
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
    | 9 => 66
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
    | 25 => 55
    | _ => 36
  point := fun i =>
    match i.val with
    | 0 => 737 / 8
    | 1 => 1085741728603037 / 16000000000000
    | 2 => 351106567058621 / 3200000000000
    | 3 => 316816728527959 / 16000000000000
    | 4 => 851014296785323 / 16000000000000
    | 5 => 2310669361628991 / 16000000000000
    | 6 => 1702028593571383 / 16000000000000
    | 7 => 2916455005232659 / 16000000000000
    | 8 => 2148247556833081 / 16000000000000
    | 9 => 3295964198834263 / 16000000000000
    | 10 => 1902925817436127 / 16000000000000
    | 11 => 3376775256198443 / 16000000000000
    | 12 => 3155021468106167 / 16000000000000
    | 13 => 2251572191454311 / 16000000000000
    | 14 => 2553042890355969 / 16000000000000
    | 15 => 2128460993877361 / 16000000000000
    | 16 => 1880559837836581 / 16000000000000
    | 17 => 545059539345519 / 3200000000000
    | 18 => 1507663370741693 / 16000000000000
    | 19 => 1278062936292373 / 16000000000000
    | 20 => 799752443166919 / 16000000000000
    | 21 => 430109523791673 / 16000000000000
    | 22 => 1167831025314019 / 16000000000000
    | 23 => 1594573424120963 / 16000000000000
    | 24 => 674247556833081 / 16000000000000
    | 25 => 2740778885421401 / 16000000000000
    | _ => 1830713276630359 / 16000000000000
  state := fun i =>
    match i.val with
    | 0 => (orderedInterval (-80899910674 / 1000000000000) (-80899909945 / 1000000000000), orderedInterval (19557236326 / 1000000000000) (19557237055 / 1000000000000))
    | 1 => (orderedInterval (-44091642721 / 1000000000000) (-44091638408 / 1000000000000), orderedInterval (86566403446 / 1000000000000) (86566407759 / 1000000000000))
    | 2 => (orderedInterval (-39769666281 / 1000000000000) (-39769666280 / 1000000000000), orderedInterval (-64784766637 / 1000000000000) (-64784766636 / 1000000000000))
    | 3 => (orderedInterval (176994236190 / 1000000000000) (176994236383 / 1000000000000), orderedInterval (-33000095510 / 1000000000000) (-33000095317 / 1000000000000))
    | 4 => (orderedInterval (-58516616175 / 1000000000000) (-58516616174 / 1000000000000), orderedInterval (-91890103694 / 1000000000000) (-91890103693 / 1000000000000))
    | 5 => (orderedInterval (42165271212 / 1000000000000) (42165271213 / 1000000000000), orderedInterval (51140518862 / 1000000000000) (51140518863 / 1000000000000))
    | 6 => (orderedInterval (26298127236 / 1000000000000) (26298127237 / 1000000000000), orderedInterval (72629631345 / 1000000000000) (72629631346 / 1000000000000))
    | 7 => (orderedInterval (44429314145 / 1000000000000) (44429314146 / 1000000000000), orderedInterval (38847372653 / 1000000000000) (38847372654 / 1000000000000))
    | 8 => (orderedInterval (2653459246 / 1000000000000) (2653459255 / 1000000000000), orderedInterval (-68817527599 / 1000000000000) (-68817527590 / 1000000000000))
    | 9 => (orderedInterval (-29649967588 / 1000000000000) (-29649962199 / 1000000000000), orderedInterval (47096471072 / 1000000000000) (47096476461 / 1000000000000))
    | 10 => (orderedInterval (24170233118 / 1000000000000) (24170233119 / 1000000000000), orderedInterval (68953458691 / 1000000000000) (68953458692 / 1000000000000))
    | 11 => (orderedInterval (-53547130726 / 1000000000000) (-53547130724 / 1000000000000), orderedInterval (-12086240009 / 1000000000000) (-12086240006 / 1000000000000))
    | 12 => (orderedInterval (-3025283258 / 1000000000000) (-3025283256 / 1000000000000), orderedInterval (-56731518744 / 1000000000000) (-56731518742 / 1000000000000))
    | 13 => (orderedInterval (-9125992932 / 1000000000000) (-9125992931 / 1000000000000), orderedInterval (-66605826869 / 1000000000000) (-66605826868 / 1000000000000))
    | 14 => (orderedInterval (-8098653190 / 1000000000000) (-8098653188 / 1000000000000), orderedInterval (-62617634352 / 1000000000000) (-62617634350 / 1000000000000))
    | 15 => (orderedInterval (66177567737 / 1000000000000) (66177569688 / 1000000000000), orderedInterval (-20400144435 / 1000000000000) (-20400142484 / 1000000000000))
    | 16 => (orderedInterval (-64244921345 / 1000000000000) (-64244904675 / 1000000000000), orderedInterval (36175837529 / 1000000000000) (36175854200 / 1000000000000))
    | 17 => (orderedInterval (60823577276 / 1000000000000) (60823577287 / 1000000000000), orderedInterval (5987436920 / 1000000000000) (5987436932 / 1000000000000))
    | 18 => (orderedInterval (56937985232 / 1000000000000) (56937985233 / 1000000000000), orderedInterval (58978269665 / 1000000000000) (58978269666 / 1000000000000))
    | 19 => (orderedInterval (-76006653864 / 1000000000000) (-76006632931 / 1000000000000), orderedInterval (47302305155 / 1000000000000) (47302326089 / 1000000000000))
    | 20 => (orderedInterval (54296740858 / 1000000000000) (54296740859 / 1000000000000), orderedInterval (98393982542 / 1000000000000) (98393982543 / 1000000000000))
    | 21 => (orderedInterval (88369941018 / 1000000000000) (88369961798 / 1000000000000), orderedInterval (-127636325594 / 1000000000000) (-127636304814 / 1000000000000))
    | 22 => (orderedInterval (-93253324637 / 1000000000000) (-93253324626 / 1000000000000), orderedInterval (-4430209138 / 1000000000000) (-4430209126 / 1000000000000))
    | 23 => (orderedInterval (-6863521729 / 1000000000000) (-6863521704 / 1000000000000), orderedInterval (79663788198 / 1000000000000) (79663788223 / 1000000000000))
    | 24 => (orderedInterval (-107181677123 / 1000000000000) (-107181665204 / 1000000000000), orderedInterval (61426521963 / 1000000000000) (61426533882 / 1000000000000))
    | 25 => (orderedInterval (39470724830 / 1000000000000) (39470750638 / 1000000000000), orderedInterval (-46574824007 / 1000000000000) (-46574798199 / 1000000000000))
    | _ => (orderedInterval (64139810846 / 1000000000000) (64139831907 / 1000000000000), orderedInterval (-38358676796 / 1000000000000) (-38358655735 / 1000000000000))
  chunkTarget := fun r b =>
    match r.val with
    | 0 =>
      match b.val with
      | 0 => orderedInterval (-34810470459 / 1000000000000) (-34810470122 / 1000000000000)
      | 1 => orderedInterval (-7054319802 / 1000000000000) (-7054319787 / 1000000000000)
      | 2 => orderedInterval (-1306248938 / 1000000000000) (-1306248932 / 1000000000000)
      | 3 => orderedInterval (-552784485 / 1000000000000) (-552783490 / 1000000000000)
      | 4 => orderedInterval (-767380504 / 1000000000000) (-767380492 / 1000000000000)
      | 5 => orderedInterval (5998042949 / 1000000000000) (5998043935 / 1000000000000)
      | 6 => orderedInterval (-3034336321 / 1000000000000) (-3034335112 / 1000000000000)
      | 7 => orderedInterval (1009876165 / 1000000000000) (1009876562 / 1000000000000)
      | _ => orderedInterval (-15893449463 / 1000000000000) (-15893443312 / 1000000000000)
    | 1 =>
      match b.val with
      | 0 => orderedInterval (3818209582 / 1000000000000) (3818209909 / 1000000000000)
      | 1 => orderedInterval (-7559268327 / 1000000000000) (-7559268313 / 1000000000000)
      | 2 => orderedInterval (-4794743263 / 1000000000000) (-4794743253 / 1000000000000)
      | 3 => orderedInterval (-16052990111 / 1000000000000) (-16052987892 / 1000000000000)
      | 4 => orderedInterval (-6879965646 / 1000000000000) (-6879965627 / 1000000000000)
      | 5 => orderedInterval (-2697962450 / 1000000000000) (-2697961186 / 1000000000000)
      | 6 => orderedInterval (-10228972341 / 1000000000000) (-10228971291 / 1000000000000)
      | 7 => orderedInterval (-5837415863 / 1000000000000) (-5837415738 / 1000000000000)
      | _ => orderedInterval (16157760348 / 1000000000000) (16157769232 / 1000000000000)
    | 2 =>
      match b.val with
      | 0 => orderedInterval (35557707898 / 1000000000000) (35557708222 / 1000000000000)
      | 1 => orderedInterval (8249119750 / 1000000000000) (8249119769 / 1000000000000)
      | 2 => orderedInterval (5280659653 / 1000000000000) (5280659671 / 1000000000000)
      | 3 => orderedInterval (10796767876 / 1000000000000) (10796772851 / 1000000000000)
      | 4 => orderedInterval (1715126346 / 1000000000000) (1715126377 / 1000000000000)
      | 5 => orderedInterval (-12872200479 / 1000000000000) (-12872198845 / 1000000000000)
      | 6 => orderedInterval (5880923796 / 1000000000000) (5880924719 / 1000000000000)
      | 7 => orderedInterval (-1741303901 / 1000000000000) (-1741303854 / 1000000000000)
      | _ => orderedInterval (29632305512 / 1000000000000) (29632319036 / 1000000000000)
    | 3 =>
      match b.val with
      | 0 => orderedInterval (-2037176308 / 1000000000000) (-2037175989 / 1000000000000)
      | 1 => orderedInterval (14556994769 / 1000000000000) (14556994797 / 1000000000000)
      | 2 => orderedInterval (14372087055 / 1000000000000) (14372087086 / 1000000000000)
      | 3 => orderedInterval (103107865659 / 1000000000000) (103107876778 / 1000000000000)
      | 4 => orderedInterval (10739439414 / 1000000000000) (10739439466 / 1000000000000)
      | 5 => orderedInterval (4178955235 / 1000000000000) (4178957333 / 1000000000000)
      | 6 => orderedInterval (11259739009 / 1000000000000) (11259739811 / 1000000000000)
      | 7 => orderedInterval (7639167740 / 1000000000000) (7639167764 / 1000000000000)
      | _ => orderedInterval (-38517307484 / 1000000000000) (-38517286175 / 1000000000000)
    | _ =>
      match b.val with
      | 0 => orderedInterval (-36834086391 / 1000000000000) (-36834086071 / 1000000000000)
      | 1 => orderedInterval (-18658368562 / 1000000000000) (-18658368520 / 1000000000000)
      | 2 => orderedInterval (-21024574204 / 1000000000000) (-21024574148 / 1000000000000)
      | 3 => orderedInterval (-75213665971 / 1000000000000) (-75213641003 / 1000000000000)
      | 4 => orderedInterval (-3416128986 / 1000000000000) (-3416128897 / 1000000000000)
      | 5 => orderedInterval (31170077036 / 1000000000000) (31170079756 / 1000000000000)
      | 6 => orderedInterval (-7623529407 / 1000000000000) (-7623528700 / 1000000000000)
      | 7 => orderedInterval (1376167704 / 1000000000000) (1376167722 / 1000000000000)
      | _ => orderedInterval (-66232131254 / 1000000000000) (-66232096150 / 1000000000000)
  coefficientTarget := fun i =>
    match i.val with
    | 0 => orderedInterval (-56411070858 / 1000000000000) (-56411060750 / 1000000000000)
    | 1 => orderedInterval (-34075348071 / 1000000000000) (-34075334159 / 1000000000000)
    | 2 => orderedInterval (82499106451 / 1000000000000) (82499127946 / 1000000000000)
    | 3 => orderedInterval (125299765089 / 1000000000000) (125299800871 / 1000000000000)
    | _ => orderedInterval (-196456240035 / 1000000000000) (-196456176011 / 1000000000000)

theorem compactCertificate201_stateChecks0 :
    compactCertificate201.stateChecks 0 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 29 12 (737 / 8)) (orderedInterval (-80899910674 / 1000000000000) (-80899909945 / 1000000000000), orderedInterval (19557236326 / 1000000000000) (19557237055 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 22 12 (1085741728603037 / 16000000000000)) (orderedInterval (-44091642721 / 1000000000000) (-44091638408 / 1000000000000), orderedInterval (86566403446 / 1000000000000) (86566407759 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 35 12 (351106567058621 / 3200000000000)) (orderedInterval (-39769666281 / 1000000000000) (-39769666280 / 1000000000000), orderedInterval (-64784766637 / 1000000000000) (-64784766636 / 1000000000000))) = true
  norm_num [besselStateAtRationalPoint, besselIntervalStepZero,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, besselZeroTransition,
    besselInitial, besselGridStateAt, besselGridStateBlock00, besselGridStateBlock01,
    besselGridStateBlock02, besselGridStateBlock03, besselGridStateBlock04,
    besselGridStateBlock05, besselGridStateBlock06, besselGridStateBlock07,
    besselGridStateBlock08, besselGridStateBlock09, besselGridStateBlock10,
    besselGridStateBlock11, besselGridStateBlock12, besselGridStateBlock13,
    besselGridStateBlock14, besselGridState006, besselGridState009, besselGridState013, besselGridState016, besselGridState017, besselGridState022, besselGridState023, besselGridState025, besselGridState029, besselGridState030, besselGridState032, besselGridState034, besselGridState035, besselGridState036, besselGridState037, besselGridState038, besselGridState042, besselGridState043, besselGridState045, besselGridState046, besselGridState051, besselGridState054, besselGridState055, besselGridState058, besselGridState063, besselGridState066, besselGridState067, besselStateSubset, linearInterval, widenInterval,
    rationalErrorInterval, rationalIntervalSubset, orderedInterval, Finset.sum_range_succ,
    IntervalRat.add, IntervalRat.mul, IntervalRat.scale, IntervalRat.singleton]

theorem compactCertificate201_stateChecks1 :
    compactCertificate201.stateChecks 3 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 6 12 (316816728527959 / 16000000000000)) (orderedInterval (176994236190 / 1000000000000) (176994236383 / 1000000000000), orderedInterval (-33000095510 / 1000000000000) (-33000095317 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 17 12 (851014296785323 / 16000000000000)) (orderedInterval (-58516616175 / 1000000000000) (-58516616174 / 1000000000000), orderedInterval (-91890103694 / 1000000000000) (-91890103693 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 46 12 (2310669361628991 / 16000000000000)) (orderedInterval (42165271212 / 1000000000000) (42165271213 / 1000000000000), orderedInterval (51140518862 / 1000000000000) (51140518863 / 1000000000000))) = true
  norm_num [besselStateAtRationalPoint, besselIntervalStepZero,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, besselZeroTransition,
    besselInitial, besselGridStateAt, besselGridStateBlock00, besselGridStateBlock01,
    besselGridStateBlock02, besselGridStateBlock03, besselGridStateBlock04,
    besselGridStateBlock05, besselGridStateBlock06, besselGridStateBlock07,
    besselGridStateBlock08, besselGridStateBlock09, besselGridStateBlock10,
    besselGridStateBlock11, besselGridStateBlock12, besselGridStateBlock13,
    besselGridStateBlock14, besselGridState006, besselGridState009, besselGridState013, besselGridState016, besselGridState017, besselGridState022, besselGridState023, besselGridState025, besselGridState029, besselGridState030, besselGridState032, besselGridState034, besselGridState035, besselGridState036, besselGridState037, besselGridState038, besselGridState042, besselGridState043, besselGridState045, besselGridState046, besselGridState051, besselGridState054, besselGridState055, besselGridState058, besselGridState063, besselGridState066, besselGridState067, besselStateSubset, linearInterval, widenInterval,
    rationalErrorInterval, rationalIntervalSubset, orderedInterval, Finset.sum_range_succ,
    IntervalRat.add, IntervalRat.mul, IntervalRat.scale, IntervalRat.singleton]

theorem compactCertificate201_stateChecks2 :
    compactCertificate201.stateChecks 6 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 34 12 (1702028593571383 / 16000000000000)) (orderedInterval (26298127236 / 1000000000000) (26298127237 / 1000000000000), orderedInterval (72629631345 / 1000000000000) (72629631346 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 58 12 (2916455005232659 / 16000000000000)) (orderedInterval (44429314145 / 1000000000000) (44429314146 / 1000000000000), orderedInterval (38847372653 / 1000000000000) (38847372654 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 43 12 (2148247556833081 / 16000000000000)) (orderedInterval (2653459246 / 1000000000000) (2653459255 / 1000000000000), orderedInterval (-68817527599 / 1000000000000) (-68817527590 / 1000000000000))) = true
  norm_num [besselStateAtRationalPoint, besselIntervalStepZero,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, besselZeroTransition,
    besselInitial, besselGridStateAt, besselGridStateBlock00, besselGridStateBlock01,
    besselGridStateBlock02, besselGridStateBlock03, besselGridStateBlock04,
    besselGridStateBlock05, besselGridStateBlock06, besselGridStateBlock07,
    besselGridStateBlock08, besselGridStateBlock09, besselGridStateBlock10,
    besselGridStateBlock11, besselGridStateBlock12, besselGridStateBlock13,
    besselGridStateBlock14, besselGridState006, besselGridState009, besselGridState013, besselGridState016, besselGridState017, besselGridState022, besselGridState023, besselGridState025, besselGridState029, besselGridState030, besselGridState032, besselGridState034, besselGridState035, besselGridState036, besselGridState037, besselGridState038, besselGridState042, besselGridState043, besselGridState045, besselGridState046, besselGridState051, besselGridState054, besselGridState055, besselGridState058, besselGridState063, besselGridState066, besselGridState067, besselStateSubset, linearInterval, widenInterval,
    rationalErrorInterval, rationalIntervalSubset, orderedInterval, Finset.sum_range_succ,
    IntervalRat.add, IntervalRat.mul, IntervalRat.scale, IntervalRat.singleton]

theorem compactCertificate201_stateChecks3 :
    compactCertificate201.stateChecks 9 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 66 12 (3295964198834263 / 16000000000000)) (orderedInterval (-29649967588 / 1000000000000) (-29649962199 / 1000000000000), orderedInterval (47096471072 / 1000000000000) (47096476461 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 38 12 (1902925817436127 / 16000000000000)) (orderedInterval (24170233118 / 1000000000000) (24170233119 / 1000000000000), orderedInterval (68953458691 / 1000000000000) (68953458692 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 67 12 (3376775256198443 / 16000000000000)) (orderedInterval (-53547130726 / 1000000000000) (-53547130724 / 1000000000000), orderedInterval (-12086240009 / 1000000000000) (-12086240006 / 1000000000000))) = true
  norm_num [besselStateAtRationalPoint, besselIntervalStepZero,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, besselZeroTransition,
    besselInitial, besselGridStateAt, besselGridStateBlock00, besselGridStateBlock01,
    besselGridStateBlock02, besselGridStateBlock03, besselGridStateBlock04,
    besselGridStateBlock05, besselGridStateBlock06, besselGridStateBlock07,
    besselGridStateBlock08, besselGridStateBlock09, besselGridStateBlock10,
    besselGridStateBlock11, besselGridStateBlock12, besselGridStateBlock13,
    besselGridStateBlock14, besselGridState006, besselGridState009, besselGridState013, besselGridState016, besselGridState017, besselGridState022, besselGridState023, besselGridState025, besselGridState029, besselGridState030, besselGridState032, besselGridState034, besselGridState035, besselGridState036, besselGridState037, besselGridState038, besselGridState042, besselGridState043, besselGridState045, besselGridState046, besselGridState051, besselGridState054, besselGridState055, besselGridState058, besselGridState063, besselGridState066, besselGridState067, besselStateSubset, linearInterval, widenInterval,
    rationalErrorInterval, rationalIntervalSubset, orderedInterval, Finset.sum_range_succ,
    IntervalRat.add, IntervalRat.mul, IntervalRat.scale, IntervalRat.singleton]

theorem compactCertificate201_stateChecks4 :
    compactCertificate201.stateChecks 12 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 63 12 (3155021468106167 / 16000000000000)) (orderedInterval (-3025283258 / 1000000000000) (-3025283256 / 1000000000000), orderedInterval (-56731518744 / 1000000000000) (-56731518742 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 45 12 (2251572191454311 / 16000000000000)) (orderedInterval (-9125992932 / 1000000000000) (-9125992931 / 1000000000000), orderedInterval (-66605826869 / 1000000000000) (-66605826868 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 51 12 (2553042890355969 / 16000000000000)) (orderedInterval (-8098653190 / 1000000000000) (-8098653188 / 1000000000000), orderedInterval (-62617634352 / 1000000000000) (-62617634350 / 1000000000000))) = true
  norm_num [besselStateAtRationalPoint, besselIntervalStepZero,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, besselZeroTransition,
    besselInitial, besselGridStateAt, besselGridStateBlock00, besselGridStateBlock01,
    besselGridStateBlock02, besselGridStateBlock03, besselGridStateBlock04,
    besselGridStateBlock05, besselGridStateBlock06, besselGridStateBlock07,
    besselGridStateBlock08, besselGridStateBlock09, besselGridStateBlock10,
    besselGridStateBlock11, besselGridStateBlock12, besselGridStateBlock13,
    besselGridStateBlock14, besselGridState006, besselGridState009, besselGridState013, besselGridState016, besselGridState017, besselGridState022, besselGridState023, besselGridState025, besselGridState029, besselGridState030, besselGridState032, besselGridState034, besselGridState035, besselGridState036, besselGridState037, besselGridState038, besselGridState042, besselGridState043, besselGridState045, besselGridState046, besselGridState051, besselGridState054, besselGridState055, besselGridState058, besselGridState063, besselGridState066, besselGridState067, besselStateSubset, linearInterval, widenInterval,
    rationalErrorInterval, rationalIntervalSubset, orderedInterval, Finset.sum_range_succ,
    IntervalRat.add, IntervalRat.mul, IntervalRat.scale, IntervalRat.singleton]

theorem compactCertificate201_stateChecks5 :
    compactCertificate201.stateChecks 15 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 42 12 (2128460993877361 / 16000000000000)) (orderedInterval (66177567737 / 1000000000000) (66177569688 / 1000000000000), orderedInterval (-20400144435 / 1000000000000) (-20400142484 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 37 12 (1880559837836581 / 16000000000000)) (orderedInterval (-64244921345 / 1000000000000) (-64244904675 / 1000000000000), orderedInterval (36175837529 / 1000000000000) (36175854200 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 54 12 (545059539345519 / 3200000000000)) (orderedInterval (60823577276 / 1000000000000) (60823577287 / 1000000000000), orderedInterval (5987436920 / 1000000000000) (5987436932 / 1000000000000))) = true
  norm_num [besselStateAtRationalPoint, besselIntervalStepZero,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, besselZeroTransition,
    besselInitial, besselGridStateAt, besselGridStateBlock00, besselGridStateBlock01,
    besselGridStateBlock02, besselGridStateBlock03, besselGridStateBlock04,
    besselGridStateBlock05, besselGridStateBlock06, besselGridStateBlock07,
    besselGridStateBlock08, besselGridStateBlock09, besselGridStateBlock10,
    besselGridStateBlock11, besselGridStateBlock12, besselGridStateBlock13,
    besselGridStateBlock14, besselGridState006, besselGridState009, besselGridState013, besselGridState016, besselGridState017, besselGridState022, besselGridState023, besselGridState025, besselGridState029, besselGridState030, besselGridState032, besselGridState034, besselGridState035, besselGridState036, besselGridState037, besselGridState038, besselGridState042, besselGridState043, besselGridState045, besselGridState046, besselGridState051, besselGridState054, besselGridState055, besselGridState058, besselGridState063, besselGridState066, besselGridState067, besselStateSubset, linearInterval, widenInterval,
    rationalErrorInterval, rationalIntervalSubset, orderedInterval, Finset.sum_range_succ,
    IntervalRat.add, IntervalRat.mul, IntervalRat.scale, IntervalRat.singleton]

theorem compactCertificate201_stateChecks6 :
    compactCertificate201.stateChecks 18 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 30 12 (1507663370741693 / 16000000000000)) (orderedInterval (56937985232 / 1000000000000) (56937985233 / 1000000000000), orderedInterval (58978269665 / 1000000000000) (58978269666 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 25 12 (1278062936292373 / 16000000000000)) (orderedInterval (-76006653864 / 1000000000000) (-76006632931 / 1000000000000), orderedInterval (47302305155 / 1000000000000) (47302326089 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 16 12 (799752443166919 / 16000000000000)) (orderedInterval (54296740858 / 1000000000000) (54296740859 / 1000000000000), orderedInterval (98393982542 / 1000000000000) (98393982543 / 1000000000000))) = true
  norm_num [besselStateAtRationalPoint, besselIntervalStepZero,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, besselZeroTransition,
    besselInitial, besselGridStateAt, besselGridStateBlock00, besselGridStateBlock01,
    besselGridStateBlock02, besselGridStateBlock03, besselGridStateBlock04,
    besselGridStateBlock05, besselGridStateBlock06, besselGridStateBlock07,
    besselGridStateBlock08, besselGridStateBlock09, besselGridStateBlock10,
    besselGridStateBlock11, besselGridStateBlock12, besselGridStateBlock13,
    besselGridStateBlock14, besselGridState006, besselGridState009, besselGridState013, besselGridState016, besselGridState017, besselGridState022, besselGridState023, besselGridState025, besselGridState029, besselGridState030, besselGridState032, besselGridState034, besselGridState035, besselGridState036, besselGridState037, besselGridState038, besselGridState042, besselGridState043, besselGridState045, besselGridState046, besselGridState051, besselGridState054, besselGridState055, besselGridState058, besselGridState063, besselGridState066, besselGridState067, besselStateSubset, linearInterval, widenInterval,
    rationalErrorInterval, rationalIntervalSubset, orderedInterval, Finset.sum_range_succ,
    IntervalRat.add, IntervalRat.mul, IntervalRat.scale, IntervalRat.singleton]

theorem compactCertificate201_stateChecks7 :
    compactCertificate201.stateChecks 21 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 9 12 (430109523791673 / 16000000000000)) (orderedInterval (88369941018 / 1000000000000) (88369961798 / 1000000000000), orderedInterval (-127636325594 / 1000000000000) (-127636304814 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 23 12 (1167831025314019 / 16000000000000)) (orderedInterval (-93253324637 / 1000000000000) (-93253324626 / 1000000000000), orderedInterval (-4430209138 / 1000000000000) (-4430209126 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 32 12 (1594573424120963 / 16000000000000)) (orderedInterval (-6863521729 / 1000000000000) (-6863521704 / 1000000000000), orderedInterval (79663788198 / 1000000000000) (79663788223 / 1000000000000))) = true
  norm_num [besselStateAtRationalPoint, besselIntervalStepZero,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, besselZeroTransition,
    besselInitial, besselGridStateAt, besselGridStateBlock00, besselGridStateBlock01,
    besselGridStateBlock02, besselGridStateBlock03, besselGridStateBlock04,
    besselGridStateBlock05, besselGridStateBlock06, besselGridStateBlock07,
    besselGridStateBlock08, besselGridStateBlock09, besselGridStateBlock10,
    besselGridStateBlock11, besselGridStateBlock12, besselGridStateBlock13,
    besselGridStateBlock14, besselGridState006, besselGridState009, besselGridState013, besselGridState016, besselGridState017, besselGridState022, besselGridState023, besselGridState025, besselGridState029, besselGridState030, besselGridState032, besselGridState034, besselGridState035, besselGridState036, besselGridState037, besselGridState038, besselGridState042, besselGridState043, besselGridState045, besselGridState046, besselGridState051, besselGridState054, besselGridState055, besselGridState058, besselGridState063, besselGridState066, besselGridState067, besselStateSubset, linearInterval, widenInterval,
    rationalErrorInterval, rationalIntervalSubset, orderedInterval, Finset.sum_range_succ,
    IntervalRat.add, IntervalRat.mul, IntervalRat.scale, IntervalRat.singleton]

theorem compactCertificate201_stateChecks8 :
    compactCertificate201.stateChecks 24 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 13 12 (674247556833081 / 16000000000000)) (orderedInterval (-107181677123 / 1000000000000) (-107181665204 / 1000000000000), orderedInterval (61426521963 / 1000000000000) (61426533882 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 55 12 (2740778885421401 / 16000000000000)) (orderedInterval (39470724830 / 1000000000000) (39470750638 / 1000000000000), orderedInterval (-46574824007 / 1000000000000) (-46574798199 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 36 12 (1830713276630359 / 16000000000000)) (orderedInterval (64139810846 / 1000000000000) (64139831907 / 1000000000000), orderedInterval (-38358676796 / 1000000000000) (-38358655735 / 1000000000000))) = true
  norm_num [besselStateAtRationalPoint, besselIntervalStepZero,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, besselZeroTransition,
    besselInitial, besselGridStateAt, besselGridStateBlock00, besselGridStateBlock01,
    besselGridStateBlock02, besselGridStateBlock03, besselGridStateBlock04,
    besselGridStateBlock05, besselGridStateBlock06, besselGridStateBlock07,
    besselGridStateBlock08, besselGridStateBlock09, besselGridStateBlock10,
    besselGridStateBlock11, besselGridStateBlock12, besselGridStateBlock13,
    besselGridStateBlock14, besselGridState006, besselGridState009, besselGridState013, besselGridState016, besselGridState017, besselGridState022, besselGridState023, besselGridState025, besselGridState029, besselGridState030, besselGridState032, besselGridState034, besselGridState035, besselGridState036, besselGridState037, besselGridState038, besselGridState042, besselGridState043, besselGridState045, besselGridState046, besselGridState051, besselGridState054, besselGridState055, besselGridState058, besselGridState063, besselGridState066, besselGridState067, besselStateSubset, linearInterval, widenInterval,
    rationalErrorInterval, rationalIntervalSubset, orderedInterval, Finset.sum_range_succ,
    IntervalRat.add, IntervalRat.mul, IntervalRat.scale, IntervalRat.singleton]

theorem compactCertificate201_states : ∀ j,
    BesselStateValid (compactCertificate201.point j) (compactCertificate201.state j) :=
  compactCertificate201.statesValid_of_checks3 compactCertificate201_stateChecks0
    compactCertificate201_stateChecks1 compactCertificate201_stateChecks2
    compactCertificate201_stateChecks3 compactCertificate201_stateChecks4
    compactCertificate201_stateChecks5 compactCertificate201_stateChecks6
    compactCertificate201_stateChecks7 compactCertificate201_stateChecks8

theorem compactCertificate201_chunkChecks0_0 :
    compactCertificate201.chunkChecks (0 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 0) <| besselDerivativeNearFromState (737 / 8) 0 (IntervalRat.scale (737 / 8) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-80899910674 / 1000000000000) (-80899909945 / 1000000000000), orderedInterval (19557236326 / 1000000000000) (19557237055 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 0) <| besselDerivativeNearFromState (1085741728603037 / 16000000000000) 0 (IntervalRat.scale (737 / 8) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-44091642721 / 1000000000000) (-44091638408 / 1000000000000), orderedInterval (86566403446 / 1000000000000) (86566407759 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 0) <| besselDerivativeNearFromState (351106567058621 / 3200000000000) 0 (IntervalRat.scale (737 / 8) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-39769666281 / 1000000000000) (-39769666280 / 1000000000000), orderedInterval (-64784766637 / 1000000000000) (-64784766636 / 1000000000000)))) (orderedInterval (-34810470459 / 1000000000000) (-34810470122 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 0) <| besselDerivativeNearFromState (316816728527959 / 16000000000000) 0 (IntervalRat.scale (737 / 8) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (176994236190 / 1000000000000) (176994236383 / 1000000000000), orderedInterval (-33000095510 / 1000000000000) (-33000095317 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 0) <| besselDerivativeNearFromState (851014296785323 / 16000000000000) 0 (IntervalRat.scale (737 / 8) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-58516616175 / 1000000000000) (-58516616174 / 1000000000000), orderedInterval (-91890103694 / 1000000000000) (-91890103693 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 0) <| besselDerivativeNearFromState (2310669361628991 / 16000000000000) 0 (IntervalRat.scale (737 / 8) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (42165271212 / 1000000000000) (42165271213 / 1000000000000), orderedInterval (51140518862 / 1000000000000) (51140518863 / 1000000000000)))) (orderedInterval (-7054319802 / 1000000000000) (-7054319787 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 0) <| besselDerivativeNearFromState (1702028593571383 / 16000000000000) 0 (IntervalRat.scale (737 / 8) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (26298127236 / 1000000000000) (26298127237 / 1000000000000), orderedInterval (72629631345 / 1000000000000) (72629631346 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 0) <| besselDerivativeNearFromState (2916455005232659 / 16000000000000) 0 (IntervalRat.scale (737 / 8) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (44429314145 / 1000000000000) (44429314146 / 1000000000000), orderedInterval (38847372653 / 1000000000000) (38847372654 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 0) <| besselDerivativeNearFromState (2148247556833081 / 16000000000000) 0 (IntervalRat.scale (737 / 8) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (2653459246 / 1000000000000) (2653459255 / 1000000000000), orderedInterval (-68817527599 / 1000000000000) (-68817527590 / 1000000000000)))) (orderedInterval (-1306248938 / 1000000000000) (-1306248932 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate201_chunkChecks0_1 :
    compactCertificate201.chunkChecks (0 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 0) <| besselDerivativeNearFromState (3295964198834263 / 16000000000000) 0 (IntervalRat.scale (737 / 8) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-29649967588 / 1000000000000) (-29649962199 / 1000000000000), orderedInterval (47096471072 / 1000000000000) (47096476461 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 0) <| besselDerivativeNearFromState (1902925817436127 / 16000000000000) 0 (IntervalRat.scale (737 / 8) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (24170233118 / 1000000000000) (24170233119 / 1000000000000), orderedInterval (68953458691 / 1000000000000) (68953458692 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 0) <| besselDerivativeNearFromState (3376775256198443 / 16000000000000) 0 (IntervalRat.scale (737 / 8) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-53547130726 / 1000000000000) (-53547130724 / 1000000000000), orderedInterval (-12086240009 / 1000000000000) (-12086240006 / 1000000000000)))) (orderedInterval (-552784485 / 1000000000000) (-552783490 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 0) <| besselDerivativeNearFromState (3155021468106167 / 16000000000000) 0 (IntervalRat.scale (737 / 8) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-3025283258 / 1000000000000) (-3025283256 / 1000000000000), orderedInterval (-56731518744 / 1000000000000) (-56731518742 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 0) <| besselDerivativeNearFromState (2251572191454311 / 16000000000000) 0 (IntervalRat.scale (737 / 8) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-9125992932 / 1000000000000) (-9125992931 / 1000000000000), orderedInterval (-66605826869 / 1000000000000) (-66605826868 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 0) <| besselDerivativeNearFromState (2553042890355969 / 16000000000000) 0 (IntervalRat.scale (737 / 8) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-8098653190 / 1000000000000) (-8098653188 / 1000000000000), orderedInterval (-62617634352 / 1000000000000) (-62617634350 / 1000000000000)))) (orderedInterval (-767380504 / 1000000000000) (-767380492 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 0) <| besselDerivativeNearFromState (2128460993877361 / 16000000000000) 0 (IntervalRat.scale (737 / 8) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (66177567737 / 1000000000000) (66177569688 / 1000000000000), orderedInterval (-20400144435 / 1000000000000) (-20400142484 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 0) <| besselDerivativeNearFromState (1880559837836581 / 16000000000000) 0 (IntervalRat.scale (737 / 8) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-64244921345 / 1000000000000) (-64244904675 / 1000000000000), orderedInterval (36175837529 / 1000000000000) (36175854200 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 0) <| besselDerivativeNearFromState (545059539345519 / 3200000000000) 0 (IntervalRat.scale (737 / 8) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (60823577276 / 1000000000000) (60823577287 / 1000000000000), orderedInterval (5987436920 / 1000000000000) (5987436932 / 1000000000000)))) (orderedInterval (5998042949 / 1000000000000) (5998043935 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate201_chunkChecks0_2 :
    compactCertificate201.chunkChecks (0 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 0) <| besselDerivativeNearFromState (1507663370741693 / 16000000000000) 0 (IntervalRat.scale (737 / 8) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (56937985232 / 1000000000000) (56937985233 / 1000000000000), orderedInterval (58978269665 / 1000000000000) (58978269666 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 0) <| besselDerivativeNearFromState (1278062936292373 / 16000000000000) 0 (IntervalRat.scale (737 / 8) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-76006653864 / 1000000000000) (-76006632931 / 1000000000000), orderedInterval (47302305155 / 1000000000000) (47302326089 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 0) <| besselDerivativeNearFromState (799752443166919 / 16000000000000) 0 (IntervalRat.scale (737 / 8) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (54296740858 / 1000000000000) (54296740859 / 1000000000000), orderedInterval (98393982542 / 1000000000000) (98393982543 / 1000000000000)))) (orderedInterval (-3034336321 / 1000000000000) (-3034335112 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 0) <| besselDerivativeNearFromState (430109523791673 / 16000000000000) 0 (IntervalRat.scale (737 / 8) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (88369941018 / 1000000000000) (88369961798 / 1000000000000), orderedInterval (-127636325594 / 1000000000000) (-127636304814 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 0) <| besselDerivativeNearFromState (1167831025314019 / 16000000000000) 0 (IntervalRat.scale (737 / 8) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-93253324637 / 1000000000000) (-93253324626 / 1000000000000), orderedInterval (-4430209138 / 1000000000000) (-4430209126 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 0) <| besselDerivativeNearFromState (1594573424120963 / 16000000000000) 0 (IntervalRat.scale (737 / 8) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-6863521729 / 1000000000000) (-6863521704 / 1000000000000), orderedInterval (79663788198 / 1000000000000) (79663788223 / 1000000000000)))) (orderedInterval (1009876165 / 1000000000000) (1009876562 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 0) <| besselDerivativeNearFromState (674247556833081 / 16000000000000) 0 (IntervalRat.scale (737 / 8) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-107181677123 / 1000000000000) (-107181665204 / 1000000000000), orderedInterval (61426521963 / 1000000000000) (61426533882 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 0) <| besselDerivativeNearFromState (2740778885421401 / 16000000000000) 0 (IntervalRat.scale (737 / 8) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (39470724830 / 1000000000000) (39470750638 / 1000000000000), orderedInterval (-46574824007 / 1000000000000) (-46574798199 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 0) <| besselDerivativeNearFromState (1830713276630359 / 16000000000000) 0 (IntervalRat.scale (737 / 8) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (64139810846 / 1000000000000) (64139831907 / 1000000000000), orderedInterval (-38358676796 / 1000000000000) (-38358655735 / 1000000000000)))) (orderedInterval (-15893449463 / 1000000000000) (-15893443312 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate201_chunkChecks0 :
    compactCertificate201.chunkChecks (0 : Fin 5) 0 9 = true :=
  compactCertificate201.chunkChecks_nine_of_three (0 : Fin 5) compactCertificate201_chunkChecks0_0
    compactCertificate201_chunkChecks0_1 compactCertificate201_chunkChecks0_2

theorem compactCertificate201_chunkChecks1_0 :
    compactCertificate201.chunkChecks (1 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 1) <| besselDerivativeNearFromState (737 / 8) 1 (IntervalRat.scale (737 / 8) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-80899910674 / 1000000000000) (-80899909945 / 1000000000000), orderedInterval (19557236326 / 1000000000000) (19557237055 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 1) <| besselDerivativeNearFromState (1085741728603037 / 16000000000000) 1 (IntervalRat.scale (737 / 8) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-44091642721 / 1000000000000) (-44091638408 / 1000000000000), orderedInterval (86566403446 / 1000000000000) (86566407759 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 1) <| besselDerivativeNearFromState (351106567058621 / 3200000000000) 1 (IntervalRat.scale (737 / 8) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-39769666281 / 1000000000000) (-39769666280 / 1000000000000), orderedInterval (-64784766637 / 1000000000000) (-64784766636 / 1000000000000)))) (orderedInterval (3818209582 / 1000000000000) (3818209909 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 1) <| besselDerivativeNearFromState (316816728527959 / 16000000000000) 1 (IntervalRat.scale (737 / 8) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (176994236190 / 1000000000000) (176994236383 / 1000000000000), orderedInterval (-33000095510 / 1000000000000) (-33000095317 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 1) <| besselDerivativeNearFromState (851014296785323 / 16000000000000) 1 (IntervalRat.scale (737 / 8) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-58516616175 / 1000000000000) (-58516616174 / 1000000000000), orderedInterval (-91890103694 / 1000000000000) (-91890103693 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 1) <| besselDerivativeNearFromState (2310669361628991 / 16000000000000) 1 (IntervalRat.scale (737 / 8) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (42165271212 / 1000000000000) (42165271213 / 1000000000000), orderedInterval (51140518862 / 1000000000000) (51140518863 / 1000000000000)))) (orderedInterval (-7559268327 / 1000000000000) (-7559268313 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 1) <| besselDerivativeNearFromState (1702028593571383 / 16000000000000) 1 (IntervalRat.scale (737 / 8) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (26298127236 / 1000000000000) (26298127237 / 1000000000000), orderedInterval (72629631345 / 1000000000000) (72629631346 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 1) <| besselDerivativeNearFromState (2916455005232659 / 16000000000000) 1 (IntervalRat.scale (737 / 8) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (44429314145 / 1000000000000) (44429314146 / 1000000000000), orderedInterval (38847372653 / 1000000000000) (38847372654 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 1) <| besselDerivativeNearFromState (2148247556833081 / 16000000000000) 1 (IntervalRat.scale (737 / 8) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (2653459246 / 1000000000000) (2653459255 / 1000000000000), orderedInterval (-68817527599 / 1000000000000) (-68817527590 / 1000000000000)))) (orderedInterval (-4794743263 / 1000000000000) (-4794743253 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate201_chunkChecks1_1 :
    compactCertificate201.chunkChecks (1 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 1) <| besselDerivativeNearFromState (3295964198834263 / 16000000000000) 1 (IntervalRat.scale (737 / 8) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-29649967588 / 1000000000000) (-29649962199 / 1000000000000), orderedInterval (47096471072 / 1000000000000) (47096476461 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 1) <| besselDerivativeNearFromState (1902925817436127 / 16000000000000) 1 (IntervalRat.scale (737 / 8) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (24170233118 / 1000000000000) (24170233119 / 1000000000000), orderedInterval (68953458691 / 1000000000000) (68953458692 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 1) <| besselDerivativeNearFromState (3376775256198443 / 16000000000000) 1 (IntervalRat.scale (737 / 8) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-53547130726 / 1000000000000) (-53547130724 / 1000000000000), orderedInterval (-12086240009 / 1000000000000) (-12086240006 / 1000000000000)))) (orderedInterval (-16052990111 / 1000000000000) (-16052987892 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 1) <| besselDerivativeNearFromState (3155021468106167 / 16000000000000) 1 (IntervalRat.scale (737 / 8) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-3025283258 / 1000000000000) (-3025283256 / 1000000000000), orderedInterval (-56731518744 / 1000000000000) (-56731518742 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 1) <| besselDerivativeNearFromState (2251572191454311 / 16000000000000) 1 (IntervalRat.scale (737 / 8) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-9125992932 / 1000000000000) (-9125992931 / 1000000000000), orderedInterval (-66605826869 / 1000000000000) (-66605826868 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 1) <| besselDerivativeNearFromState (2553042890355969 / 16000000000000) 1 (IntervalRat.scale (737 / 8) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-8098653190 / 1000000000000) (-8098653188 / 1000000000000), orderedInterval (-62617634352 / 1000000000000) (-62617634350 / 1000000000000)))) (orderedInterval (-6879965646 / 1000000000000) (-6879965627 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 1) <| besselDerivativeNearFromState (2128460993877361 / 16000000000000) 1 (IntervalRat.scale (737 / 8) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (66177567737 / 1000000000000) (66177569688 / 1000000000000), orderedInterval (-20400144435 / 1000000000000) (-20400142484 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 1) <| besselDerivativeNearFromState (1880559837836581 / 16000000000000) 1 (IntervalRat.scale (737 / 8) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-64244921345 / 1000000000000) (-64244904675 / 1000000000000), orderedInterval (36175837529 / 1000000000000) (36175854200 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 1) <| besselDerivativeNearFromState (545059539345519 / 3200000000000) 1 (IntervalRat.scale (737 / 8) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (60823577276 / 1000000000000) (60823577287 / 1000000000000), orderedInterval (5987436920 / 1000000000000) (5987436932 / 1000000000000)))) (orderedInterval (-2697962450 / 1000000000000) (-2697961186 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate201_chunkChecks1_2 :
    compactCertificate201.chunkChecks (1 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 1) <| besselDerivativeNearFromState (1507663370741693 / 16000000000000) 1 (IntervalRat.scale (737 / 8) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (56937985232 / 1000000000000) (56937985233 / 1000000000000), orderedInterval (58978269665 / 1000000000000) (58978269666 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 1) <| besselDerivativeNearFromState (1278062936292373 / 16000000000000) 1 (IntervalRat.scale (737 / 8) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-76006653864 / 1000000000000) (-76006632931 / 1000000000000), orderedInterval (47302305155 / 1000000000000) (47302326089 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 1) <| besselDerivativeNearFromState (799752443166919 / 16000000000000) 1 (IntervalRat.scale (737 / 8) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (54296740858 / 1000000000000) (54296740859 / 1000000000000), orderedInterval (98393982542 / 1000000000000) (98393982543 / 1000000000000)))) (orderedInterval (-10228972341 / 1000000000000) (-10228971291 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 1) <| besselDerivativeNearFromState (430109523791673 / 16000000000000) 1 (IntervalRat.scale (737 / 8) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (88369941018 / 1000000000000) (88369961798 / 1000000000000), orderedInterval (-127636325594 / 1000000000000) (-127636304814 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 1) <| besselDerivativeNearFromState (1167831025314019 / 16000000000000) 1 (IntervalRat.scale (737 / 8) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-93253324637 / 1000000000000) (-93253324626 / 1000000000000), orderedInterval (-4430209138 / 1000000000000) (-4430209126 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 1) <| besselDerivativeNearFromState (1594573424120963 / 16000000000000) 1 (IntervalRat.scale (737 / 8) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-6863521729 / 1000000000000) (-6863521704 / 1000000000000), orderedInterval (79663788198 / 1000000000000) (79663788223 / 1000000000000)))) (orderedInterval (-5837415863 / 1000000000000) (-5837415738 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 1) <| besselDerivativeNearFromState (674247556833081 / 16000000000000) 1 (IntervalRat.scale (737 / 8) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-107181677123 / 1000000000000) (-107181665204 / 1000000000000), orderedInterval (61426521963 / 1000000000000) (61426533882 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 1) <| besselDerivativeNearFromState (2740778885421401 / 16000000000000) 1 (IntervalRat.scale (737 / 8) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (39470724830 / 1000000000000) (39470750638 / 1000000000000), orderedInterval (-46574824007 / 1000000000000) (-46574798199 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 1) <| besselDerivativeNearFromState (1830713276630359 / 16000000000000) 1 (IntervalRat.scale (737 / 8) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (64139810846 / 1000000000000) (64139831907 / 1000000000000), orderedInterval (-38358676796 / 1000000000000) (-38358655735 / 1000000000000)))) (orderedInterval (16157760348 / 1000000000000) (16157769232 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate201_chunkChecks1 :
    compactCertificate201.chunkChecks (1 : Fin 5) 0 9 = true :=
  compactCertificate201.chunkChecks_nine_of_three (1 : Fin 5) compactCertificate201_chunkChecks1_0
    compactCertificate201_chunkChecks1_1 compactCertificate201_chunkChecks1_2

theorem compactCertificate201_chunkChecks2_0 :
    compactCertificate201.chunkChecks (2 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 2) <| besselDerivativeNearFromState (737 / 8) 2 (IntervalRat.scale (737 / 8) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-80899910674 / 1000000000000) (-80899909945 / 1000000000000), orderedInterval (19557236326 / 1000000000000) (19557237055 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 2) <| besselDerivativeNearFromState (1085741728603037 / 16000000000000) 2 (IntervalRat.scale (737 / 8) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-44091642721 / 1000000000000) (-44091638408 / 1000000000000), orderedInterval (86566403446 / 1000000000000) (86566407759 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 2) <| besselDerivativeNearFromState (351106567058621 / 3200000000000) 2 (IntervalRat.scale (737 / 8) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-39769666281 / 1000000000000) (-39769666280 / 1000000000000), orderedInterval (-64784766637 / 1000000000000) (-64784766636 / 1000000000000)))) (orderedInterval (35557707898 / 1000000000000) (35557708222 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 2) <| besselDerivativeNearFromState (316816728527959 / 16000000000000) 2 (IntervalRat.scale (737 / 8) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (176994236190 / 1000000000000) (176994236383 / 1000000000000), orderedInterval (-33000095510 / 1000000000000) (-33000095317 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 2) <| besselDerivativeNearFromState (851014296785323 / 16000000000000) 2 (IntervalRat.scale (737 / 8) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-58516616175 / 1000000000000) (-58516616174 / 1000000000000), orderedInterval (-91890103694 / 1000000000000) (-91890103693 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 2) <| besselDerivativeNearFromState (2310669361628991 / 16000000000000) 2 (IntervalRat.scale (737 / 8) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (42165271212 / 1000000000000) (42165271213 / 1000000000000), orderedInterval (51140518862 / 1000000000000) (51140518863 / 1000000000000)))) (orderedInterval (8249119750 / 1000000000000) (8249119769 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 2) <| besselDerivativeNearFromState (1702028593571383 / 16000000000000) 2 (IntervalRat.scale (737 / 8) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (26298127236 / 1000000000000) (26298127237 / 1000000000000), orderedInterval (72629631345 / 1000000000000) (72629631346 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 2) <| besselDerivativeNearFromState (2916455005232659 / 16000000000000) 2 (IntervalRat.scale (737 / 8) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (44429314145 / 1000000000000) (44429314146 / 1000000000000), orderedInterval (38847372653 / 1000000000000) (38847372654 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 2) <| besselDerivativeNearFromState (2148247556833081 / 16000000000000) 2 (IntervalRat.scale (737 / 8) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (2653459246 / 1000000000000) (2653459255 / 1000000000000), orderedInterval (-68817527599 / 1000000000000) (-68817527590 / 1000000000000)))) (orderedInterval (5280659653 / 1000000000000) (5280659671 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate201_chunkChecks2_1 :
    compactCertificate201.chunkChecks (2 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 2) <| besselDerivativeNearFromState (3295964198834263 / 16000000000000) 2 (IntervalRat.scale (737 / 8) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-29649967588 / 1000000000000) (-29649962199 / 1000000000000), orderedInterval (47096471072 / 1000000000000) (47096476461 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 2) <| besselDerivativeNearFromState (1902925817436127 / 16000000000000) 2 (IntervalRat.scale (737 / 8) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (24170233118 / 1000000000000) (24170233119 / 1000000000000), orderedInterval (68953458691 / 1000000000000) (68953458692 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 2) <| besselDerivativeNearFromState (3376775256198443 / 16000000000000) 2 (IntervalRat.scale (737 / 8) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-53547130726 / 1000000000000) (-53547130724 / 1000000000000), orderedInterval (-12086240009 / 1000000000000) (-12086240006 / 1000000000000)))) (orderedInterval (10796767876 / 1000000000000) (10796772851 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 2) <| besselDerivativeNearFromState (3155021468106167 / 16000000000000) 2 (IntervalRat.scale (737 / 8) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-3025283258 / 1000000000000) (-3025283256 / 1000000000000), orderedInterval (-56731518744 / 1000000000000) (-56731518742 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 2) <| besselDerivativeNearFromState (2251572191454311 / 16000000000000) 2 (IntervalRat.scale (737 / 8) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-9125992932 / 1000000000000) (-9125992931 / 1000000000000), orderedInterval (-66605826869 / 1000000000000) (-66605826868 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 2) <| besselDerivativeNearFromState (2553042890355969 / 16000000000000) 2 (IntervalRat.scale (737 / 8) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-8098653190 / 1000000000000) (-8098653188 / 1000000000000), orderedInterval (-62617634352 / 1000000000000) (-62617634350 / 1000000000000)))) (orderedInterval (1715126346 / 1000000000000) (1715126377 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 2) <| besselDerivativeNearFromState (2128460993877361 / 16000000000000) 2 (IntervalRat.scale (737 / 8) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (66177567737 / 1000000000000) (66177569688 / 1000000000000), orderedInterval (-20400144435 / 1000000000000) (-20400142484 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 2) <| besselDerivativeNearFromState (1880559837836581 / 16000000000000) 2 (IntervalRat.scale (737 / 8) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-64244921345 / 1000000000000) (-64244904675 / 1000000000000), orderedInterval (36175837529 / 1000000000000) (36175854200 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 2) <| besselDerivativeNearFromState (545059539345519 / 3200000000000) 2 (IntervalRat.scale (737 / 8) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (60823577276 / 1000000000000) (60823577287 / 1000000000000), orderedInterval (5987436920 / 1000000000000) (5987436932 / 1000000000000)))) (orderedInterval (-12872200479 / 1000000000000) (-12872198845 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate201_chunkChecks2_2 :
    compactCertificate201.chunkChecks (2 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 2) <| besselDerivativeNearFromState (1507663370741693 / 16000000000000) 2 (IntervalRat.scale (737 / 8) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (56937985232 / 1000000000000) (56937985233 / 1000000000000), orderedInterval (58978269665 / 1000000000000) (58978269666 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 2) <| besselDerivativeNearFromState (1278062936292373 / 16000000000000) 2 (IntervalRat.scale (737 / 8) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-76006653864 / 1000000000000) (-76006632931 / 1000000000000), orderedInterval (47302305155 / 1000000000000) (47302326089 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 2) <| besselDerivativeNearFromState (799752443166919 / 16000000000000) 2 (IntervalRat.scale (737 / 8) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (54296740858 / 1000000000000) (54296740859 / 1000000000000), orderedInterval (98393982542 / 1000000000000) (98393982543 / 1000000000000)))) (orderedInterval (5880923796 / 1000000000000) (5880924719 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 2) <| besselDerivativeNearFromState (430109523791673 / 16000000000000) 2 (IntervalRat.scale (737 / 8) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (88369941018 / 1000000000000) (88369961798 / 1000000000000), orderedInterval (-127636325594 / 1000000000000) (-127636304814 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 2) <| besselDerivativeNearFromState (1167831025314019 / 16000000000000) 2 (IntervalRat.scale (737 / 8) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-93253324637 / 1000000000000) (-93253324626 / 1000000000000), orderedInterval (-4430209138 / 1000000000000) (-4430209126 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 2) <| besselDerivativeNearFromState (1594573424120963 / 16000000000000) 2 (IntervalRat.scale (737 / 8) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-6863521729 / 1000000000000) (-6863521704 / 1000000000000), orderedInterval (79663788198 / 1000000000000) (79663788223 / 1000000000000)))) (orderedInterval (-1741303901 / 1000000000000) (-1741303854 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 2) <| besselDerivativeNearFromState (674247556833081 / 16000000000000) 2 (IntervalRat.scale (737 / 8) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-107181677123 / 1000000000000) (-107181665204 / 1000000000000), orderedInterval (61426521963 / 1000000000000) (61426533882 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 2) <| besselDerivativeNearFromState (2740778885421401 / 16000000000000) 2 (IntervalRat.scale (737 / 8) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (39470724830 / 1000000000000) (39470750638 / 1000000000000), orderedInterval (-46574824007 / 1000000000000) (-46574798199 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 2) <| besselDerivativeNearFromState (1830713276630359 / 16000000000000) 2 (IntervalRat.scale (737 / 8) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (64139810846 / 1000000000000) (64139831907 / 1000000000000), orderedInterval (-38358676796 / 1000000000000) (-38358655735 / 1000000000000)))) (orderedInterval (29632305512 / 1000000000000) (29632319036 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate201_chunkChecks2 :
    compactCertificate201.chunkChecks (2 : Fin 5) 0 9 = true :=
  compactCertificate201.chunkChecks_nine_of_three (2 : Fin 5) compactCertificate201_chunkChecks2_0
    compactCertificate201_chunkChecks2_1 compactCertificate201_chunkChecks2_2

theorem compactCertificate201_chunkChecks3_0 :
    compactCertificate201.chunkChecks (3 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 3) <| besselDerivativeNearFromState (737 / 8) 3 (IntervalRat.scale (737 / 8) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-80899910674 / 1000000000000) (-80899909945 / 1000000000000), orderedInterval (19557236326 / 1000000000000) (19557237055 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 3) <| besselDerivativeNearFromState (1085741728603037 / 16000000000000) 3 (IntervalRat.scale (737 / 8) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-44091642721 / 1000000000000) (-44091638408 / 1000000000000), orderedInterval (86566403446 / 1000000000000) (86566407759 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 3) <| besselDerivativeNearFromState (351106567058621 / 3200000000000) 3 (IntervalRat.scale (737 / 8) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-39769666281 / 1000000000000) (-39769666280 / 1000000000000), orderedInterval (-64784766637 / 1000000000000) (-64784766636 / 1000000000000)))) (orderedInterval (-2037176308 / 1000000000000) (-2037175989 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 3) <| besselDerivativeNearFromState (316816728527959 / 16000000000000) 3 (IntervalRat.scale (737 / 8) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (176994236190 / 1000000000000) (176994236383 / 1000000000000), orderedInterval (-33000095510 / 1000000000000) (-33000095317 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 3) <| besselDerivativeNearFromState (851014296785323 / 16000000000000) 3 (IntervalRat.scale (737 / 8) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-58516616175 / 1000000000000) (-58516616174 / 1000000000000), orderedInterval (-91890103694 / 1000000000000) (-91890103693 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 3) <| besselDerivativeNearFromState (2310669361628991 / 16000000000000) 3 (IntervalRat.scale (737 / 8) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (42165271212 / 1000000000000) (42165271213 / 1000000000000), orderedInterval (51140518862 / 1000000000000) (51140518863 / 1000000000000)))) (orderedInterval (14556994769 / 1000000000000) (14556994797 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 3) <| besselDerivativeNearFromState (1702028593571383 / 16000000000000) 3 (IntervalRat.scale (737 / 8) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (26298127236 / 1000000000000) (26298127237 / 1000000000000), orderedInterval (72629631345 / 1000000000000) (72629631346 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 3) <| besselDerivativeNearFromState (2916455005232659 / 16000000000000) 3 (IntervalRat.scale (737 / 8) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (44429314145 / 1000000000000) (44429314146 / 1000000000000), orderedInterval (38847372653 / 1000000000000) (38847372654 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 3) <| besselDerivativeNearFromState (2148247556833081 / 16000000000000) 3 (IntervalRat.scale (737 / 8) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (2653459246 / 1000000000000) (2653459255 / 1000000000000), orderedInterval (-68817527599 / 1000000000000) (-68817527590 / 1000000000000)))) (orderedInterval (14372087055 / 1000000000000) (14372087086 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate201_chunkChecks3_1 :
    compactCertificate201.chunkChecks (3 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 3) <| besselDerivativeNearFromState (3295964198834263 / 16000000000000) 3 (IntervalRat.scale (737 / 8) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-29649967588 / 1000000000000) (-29649962199 / 1000000000000), orderedInterval (47096471072 / 1000000000000) (47096476461 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 3) <| besselDerivativeNearFromState (1902925817436127 / 16000000000000) 3 (IntervalRat.scale (737 / 8) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (24170233118 / 1000000000000) (24170233119 / 1000000000000), orderedInterval (68953458691 / 1000000000000) (68953458692 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 3) <| besselDerivativeNearFromState (3376775256198443 / 16000000000000) 3 (IntervalRat.scale (737 / 8) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-53547130726 / 1000000000000) (-53547130724 / 1000000000000), orderedInterval (-12086240009 / 1000000000000) (-12086240006 / 1000000000000)))) (orderedInterval (103107865659 / 1000000000000) (103107876778 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 3) <| besselDerivativeNearFromState (3155021468106167 / 16000000000000) 3 (IntervalRat.scale (737 / 8) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-3025283258 / 1000000000000) (-3025283256 / 1000000000000), orderedInterval (-56731518744 / 1000000000000) (-56731518742 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 3) <| besselDerivativeNearFromState (2251572191454311 / 16000000000000) 3 (IntervalRat.scale (737 / 8) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-9125992932 / 1000000000000) (-9125992931 / 1000000000000), orderedInterval (-66605826869 / 1000000000000) (-66605826868 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 3) <| besselDerivativeNearFromState (2553042890355969 / 16000000000000) 3 (IntervalRat.scale (737 / 8) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-8098653190 / 1000000000000) (-8098653188 / 1000000000000), orderedInterval (-62617634352 / 1000000000000) (-62617634350 / 1000000000000)))) (orderedInterval (10739439414 / 1000000000000) (10739439466 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 3) <| besselDerivativeNearFromState (2128460993877361 / 16000000000000) 3 (IntervalRat.scale (737 / 8) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (66177567737 / 1000000000000) (66177569688 / 1000000000000), orderedInterval (-20400144435 / 1000000000000) (-20400142484 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 3) <| besselDerivativeNearFromState (1880559837836581 / 16000000000000) 3 (IntervalRat.scale (737 / 8) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-64244921345 / 1000000000000) (-64244904675 / 1000000000000), orderedInterval (36175837529 / 1000000000000) (36175854200 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 3) <| besselDerivativeNearFromState (545059539345519 / 3200000000000) 3 (IntervalRat.scale (737 / 8) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (60823577276 / 1000000000000) (60823577287 / 1000000000000), orderedInterval (5987436920 / 1000000000000) (5987436932 / 1000000000000)))) (orderedInterval (4178955235 / 1000000000000) (4178957333 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate201_chunkChecks3_2 :
    compactCertificate201.chunkChecks (3 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 3) <| besselDerivativeNearFromState (1507663370741693 / 16000000000000) 3 (IntervalRat.scale (737 / 8) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (56937985232 / 1000000000000) (56937985233 / 1000000000000), orderedInterval (58978269665 / 1000000000000) (58978269666 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 3) <| besselDerivativeNearFromState (1278062936292373 / 16000000000000) 3 (IntervalRat.scale (737 / 8) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-76006653864 / 1000000000000) (-76006632931 / 1000000000000), orderedInterval (47302305155 / 1000000000000) (47302326089 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 3) <| besselDerivativeNearFromState (799752443166919 / 16000000000000) 3 (IntervalRat.scale (737 / 8) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (54296740858 / 1000000000000) (54296740859 / 1000000000000), orderedInterval (98393982542 / 1000000000000) (98393982543 / 1000000000000)))) (orderedInterval (11259739009 / 1000000000000) (11259739811 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 3) <| besselDerivativeNearFromState (430109523791673 / 16000000000000) 3 (IntervalRat.scale (737 / 8) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (88369941018 / 1000000000000) (88369961798 / 1000000000000), orderedInterval (-127636325594 / 1000000000000) (-127636304814 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 3) <| besselDerivativeNearFromState (1167831025314019 / 16000000000000) 3 (IntervalRat.scale (737 / 8) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-93253324637 / 1000000000000) (-93253324626 / 1000000000000), orderedInterval (-4430209138 / 1000000000000) (-4430209126 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 3) <| besselDerivativeNearFromState (1594573424120963 / 16000000000000) 3 (IntervalRat.scale (737 / 8) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-6863521729 / 1000000000000) (-6863521704 / 1000000000000), orderedInterval (79663788198 / 1000000000000) (79663788223 / 1000000000000)))) (orderedInterval (7639167740 / 1000000000000) (7639167764 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 3) <| besselDerivativeNearFromState (674247556833081 / 16000000000000) 3 (IntervalRat.scale (737 / 8) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-107181677123 / 1000000000000) (-107181665204 / 1000000000000), orderedInterval (61426521963 / 1000000000000) (61426533882 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 3) <| besselDerivativeNearFromState (2740778885421401 / 16000000000000) 3 (IntervalRat.scale (737 / 8) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (39470724830 / 1000000000000) (39470750638 / 1000000000000), orderedInterval (-46574824007 / 1000000000000) (-46574798199 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 3) <| besselDerivativeNearFromState (1830713276630359 / 16000000000000) 3 (IntervalRat.scale (737 / 8) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (64139810846 / 1000000000000) (64139831907 / 1000000000000), orderedInterval (-38358676796 / 1000000000000) (-38358655735 / 1000000000000)))) (orderedInterval (-38517307484 / 1000000000000) (-38517286175 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate201_chunkChecks3 :
    compactCertificate201.chunkChecks (3 : Fin 5) 0 9 = true :=
  compactCertificate201.chunkChecks_nine_of_three (3 : Fin 5) compactCertificate201_chunkChecks3_0
    compactCertificate201_chunkChecks3_1 compactCertificate201_chunkChecks3_2

theorem compactCertificate201_chunkChecks4_0 :
    compactCertificate201.chunkChecks (4 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 4) <| besselDerivativeNearFromState (737 / 8) 4 (IntervalRat.scale (737 / 8) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-80899910674 / 1000000000000) (-80899909945 / 1000000000000), orderedInterval (19557236326 / 1000000000000) (19557237055 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 4) <| besselDerivativeNearFromState (1085741728603037 / 16000000000000) 4 (IntervalRat.scale (737 / 8) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-44091642721 / 1000000000000) (-44091638408 / 1000000000000), orderedInterval (86566403446 / 1000000000000) (86566407759 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 4) <| besselDerivativeNearFromState (351106567058621 / 3200000000000) 4 (IntervalRat.scale (737 / 8) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-39769666281 / 1000000000000) (-39769666280 / 1000000000000), orderedInterval (-64784766637 / 1000000000000) (-64784766636 / 1000000000000)))) (orderedInterval (-36834086391 / 1000000000000) (-36834086071 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 4) <| besselDerivativeNearFromState (316816728527959 / 16000000000000) 4 (IntervalRat.scale (737 / 8) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (176994236190 / 1000000000000) (176994236383 / 1000000000000), orderedInterval (-33000095510 / 1000000000000) (-33000095317 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 4) <| besselDerivativeNearFromState (851014296785323 / 16000000000000) 4 (IntervalRat.scale (737 / 8) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-58516616175 / 1000000000000) (-58516616174 / 1000000000000), orderedInterval (-91890103694 / 1000000000000) (-91890103693 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 4) <| besselDerivativeNearFromState (2310669361628991 / 16000000000000) 4 (IntervalRat.scale (737 / 8) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (42165271212 / 1000000000000) (42165271213 / 1000000000000), orderedInterval (51140518862 / 1000000000000) (51140518863 / 1000000000000)))) (orderedInterval (-18658368562 / 1000000000000) (-18658368520 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 4) <| besselDerivativeNearFromState (1702028593571383 / 16000000000000) 4 (IntervalRat.scale (737 / 8) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (26298127236 / 1000000000000) (26298127237 / 1000000000000), orderedInterval (72629631345 / 1000000000000) (72629631346 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 4) <| besselDerivativeNearFromState (2916455005232659 / 16000000000000) 4 (IntervalRat.scale (737 / 8) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (44429314145 / 1000000000000) (44429314146 / 1000000000000), orderedInterval (38847372653 / 1000000000000) (38847372654 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 4) <| besselDerivativeNearFromState (2148247556833081 / 16000000000000) 4 (IntervalRat.scale (737 / 8) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (2653459246 / 1000000000000) (2653459255 / 1000000000000), orderedInterval (-68817527599 / 1000000000000) (-68817527590 / 1000000000000)))) (orderedInterval (-21024574204 / 1000000000000) (-21024574148 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate201_chunkChecks4_1 :
    compactCertificate201.chunkChecks (4 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 4) <| besselDerivativeNearFromState (3295964198834263 / 16000000000000) 4 (IntervalRat.scale (737 / 8) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-29649967588 / 1000000000000) (-29649962199 / 1000000000000), orderedInterval (47096471072 / 1000000000000) (47096476461 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 4) <| besselDerivativeNearFromState (1902925817436127 / 16000000000000) 4 (IntervalRat.scale (737 / 8) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (24170233118 / 1000000000000) (24170233119 / 1000000000000), orderedInterval (68953458691 / 1000000000000) (68953458692 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 4) <| besselDerivativeNearFromState (3376775256198443 / 16000000000000) 4 (IntervalRat.scale (737 / 8) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-53547130726 / 1000000000000) (-53547130724 / 1000000000000), orderedInterval (-12086240009 / 1000000000000) (-12086240006 / 1000000000000)))) (orderedInterval (-75213665971 / 1000000000000) (-75213641003 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 4) <| besselDerivativeNearFromState (3155021468106167 / 16000000000000) 4 (IntervalRat.scale (737 / 8) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-3025283258 / 1000000000000) (-3025283256 / 1000000000000), orderedInterval (-56731518744 / 1000000000000) (-56731518742 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 4) <| besselDerivativeNearFromState (2251572191454311 / 16000000000000) 4 (IntervalRat.scale (737 / 8) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-9125992932 / 1000000000000) (-9125992931 / 1000000000000), orderedInterval (-66605826869 / 1000000000000) (-66605826868 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 4) <| besselDerivativeNearFromState (2553042890355969 / 16000000000000) 4 (IntervalRat.scale (737 / 8) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-8098653190 / 1000000000000) (-8098653188 / 1000000000000), orderedInterval (-62617634352 / 1000000000000) (-62617634350 / 1000000000000)))) (orderedInterval (-3416128986 / 1000000000000) (-3416128897 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 4) <| besselDerivativeNearFromState (2128460993877361 / 16000000000000) 4 (IntervalRat.scale (737 / 8) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (66177567737 / 1000000000000) (66177569688 / 1000000000000), orderedInterval (-20400144435 / 1000000000000) (-20400142484 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 4) <| besselDerivativeNearFromState (1880559837836581 / 16000000000000) 4 (IntervalRat.scale (737 / 8) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-64244921345 / 1000000000000) (-64244904675 / 1000000000000), orderedInterval (36175837529 / 1000000000000) (36175854200 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 4) <| besselDerivativeNearFromState (545059539345519 / 3200000000000) 4 (IntervalRat.scale (737 / 8) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (60823577276 / 1000000000000) (60823577287 / 1000000000000), orderedInterval (5987436920 / 1000000000000) (5987436932 / 1000000000000)))) (orderedInterval (31170077036 / 1000000000000) (31170079756 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate201_chunkChecks4_2 :
    compactCertificate201.chunkChecks (4 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 4) <| besselDerivativeNearFromState (1507663370741693 / 16000000000000) 4 (IntervalRat.scale (737 / 8) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (56937985232 / 1000000000000) (56937985233 / 1000000000000), orderedInterval (58978269665 / 1000000000000) (58978269666 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 4) <| besselDerivativeNearFromState (1278062936292373 / 16000000000000) 4 (IntervalRat.scale (737 / 8) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-76006653864 / 1000000000000) (-76006632931 / 1000000000000), orderedInterval (47302305155 / 1000000000000) (47302326089 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 4) <| besselDerivativeNearFromState (799752443166919 / 16000000000000) 4 (IntervalRat.scale (737 / 8) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (54296740858 / 1000000000000) (54296740859 / 1000000000000), orderedInterval (98393982542 / 1000000000000) (98393982543 / 1000000000000)))) (orderedInterval (-7623529407 / 1000000000000) (-7623528700 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 4) <| besselDerivativeNearFromState (430109523791673 / 16000000000000) 4 (IntervalRat.scale (737 / 8) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (88369941018 / 1000000000000) (88369961798 / 1000000000000), orderedInterval (-127636325594 / 1000000000000) (-127636304814 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 4) <| besselDerivativeNearFromState (1167831025314019 / 16000000000000) 4 (IntervalRat.scale (737 / 8) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-93253324637 / 1000000000000) (-93253324626 / 1000000000000), orderedInterval (-4430209138 / 1000000000000) (-4430209126 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 4) <| besselDerivativeNearFromState (1594573424120963 / 16000000000000) 4 (IntervalRat.scale (737 / 8) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-6863521729 / 1000000000000) (-6863521704 / 1000000000000), orderedInterval (79663788198 / 1000000000000) (79663788223 / 1000000000000)))) (orderedInterval (1376167704 / 1000000000000) (1376167722 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 4) <| besselDerivativeNearFromState (674247556833081 / 16000000000000) 4 (IntervalRat.scale (737 / 8) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-107181677123 / 1000000000000) (-107181665204 / 1000000000000), orderedInterval (61426521963 / 1000000000000) (61426533882 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 4) <| besselDerivativeNearFromState (2740778885421401 / 16000000000000) 4 (IntervalRat.scale (737 / 8) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (39470724830 / 1000000000000) (39470750638 / 1000000000000), orderedInterval (-46574824007 / 1000000000000) (-46574798199 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 4) <| besselDerivativeNearFromState (1830713276630359 / 16000000000000) 4 (IntervalRat.scale (737 / 8) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (64139810846 / 1000000000000) (64139831907 / 1000000000000), orderedInterval (-38358676796 / 1000000000000) (-38358655735 / 1000000000000)))) (orderedInterval (-66232131254 / 1000000000000) (-66232096150 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate201_chunkChecks4 :
    compactCertificate201.chunkChecks (4 : Fin 5) 0 9 = true :=
  compactCertificate201.chunkChecks_nine_of_three (4 : Fin 5) compactCertificate201_chunkChecks4_0
    compactCertificate201_chunkChecks4_1 compactCertificate201_chunkChecks4_2

theorem compactCertificate201_chunks :
    ∀ r : Fin 5, ∀ b, compactCertificate201.chunkCheck r b = true :=
  compactCertificate201.chunkChecks_all (by
    intro r
    fin_cases r
    · exact compactCertificate201_chunkChecks0
    · exact compactCertificate201_chunkChecks1
    · exact compactCertificate201_chunkChecks2
    · exact compactCertificate201_chunkChecks3
    · exact compactCertificate201_chunkChecks4)

theorem compactCertificate201_coefficient0 :
    compactCertificate201.coefficientCheck (0 : Fin 5) = true := by
  norm_num [CompactCertificate.coefficientCheck, intervalFinSumHull,
    compactCertificate201, rationalIntervalSubset, orderedInterval, Fin.sum_univ_succ]

theorem compactCertificate201_coefficient1 :
    compactCertificate201.coefficientCheck (1 : Fin 5) = true := by
  norm_num [CompactCertificate.coefficientCheck, intervalFinSumHull,
    compactCertificate201, rationalIntervalSubset, orderedInterval, Fin.sum_univ_succ]

theorem compactCertificate201_coefficient2 :
    compactCertificate201.coefficientCheck (2 : Fin 5) = true := by
  norm_num [CompactCertificate.coefficientCheck, intervalFinSumHull,
    compactCertificate201, rationalIntervalSubset, orderedInterval, Fin.sum_univ_succ]

theorem compactCertificate201_coefficient3 :
    compactCertificate201.coefficientCheck (3 : Fin 5) = true := by
  norm_num [CompactCertificate.coefficientCheck, intervalFinSumHull,
    compactCertificate201, rationalIntervalSubset, orderedInterval, Fin.sum_univ_succ]

theorem compactCertificate201_coefficient4 :
    compactCertificate201.coefficientCheck (4 : Fin 5) = true := by
  norm_num [CompactCertificate.coefficientCheck, intervalFinSumHull,
    compactCertificate201, rationalIntervalSubset, orderedInterval, Fin.sum_univ_succ]

theorem compactCertificate201_coefficients : ∀ r : Fin 5,
    compactCertificate201.coefficientCheck r = true := by
  intro r
  fin_cases r
  · exact compactCertificate201_coefficient0
  · exact compactCertificate201_coefficient1
  · exact compactCertificate201_coefficient2
  · exact compactCertificate201_coefficient3
  · exact compactCertificate201_coefficient4

theorem compactCertificate201_lower : (1 : ℚ) ≤ compactCertificate201.output.lo := by
  norm_num [CompactCertificate.output, CompactCertificate.interval,
    CompactCertificate.coefficientTargetNat, compactCertificate201, dualConstant,
    intervalTaylorSum, intervalPow, intervalSub, intervalMaxAbs, widenInterval,
    rationalErrorInterval, orderedInterval, IntervalRat.add, IntervalRat.mul, IntervalRat.scale,
    IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4]

theorem compactCertificate201_proves {t : ℝ} (ht : t ∈ compactCertificate201.interval) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t :=
  compactCertificate201.proves compactCertificate201_states compactCertificate201_chunks
    compactCertificate201_coefficients compactCertificate201_lower ht

end Erdos232
