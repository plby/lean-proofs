/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, OpenAI Codex
-/
import ErdosProblems.Erdos232.CompactBase

open LeanCert.Core
namespace Erdos232

def compactCertificate213 : CompactCertificate where
  left := 94
  right := 95
  center := 189 / 2
  grid := fun i =>
    match i.val with
    | 0 => 30
    | 1 => 22
    | 2 => 36
    | 3 => 6
    | 4 => 17
    | 5 => 47
    | 6 => 35
    | 7 => 60
    | 8 => 44
    | 9 => 67
    | 10 => 39
    | 11 => 69
    | 12 => 64
    | 13 => 46
    | 14 => 52
    | 15 => 43
    | 16 => 38
    | 17 => 56
    | 18 => 31
    | 19 => 26
    | 20 => 16
    | 21 => 9
    | 22 => 24
    | 23 => 33
    | 24 => 14
    | 25 => 56
    | _ => 37
  point := fun i =>
    match i.val with
    | 0 => 189 / 2
    | 1 => 278433089153289 / 4000000000000
    | 2 => 90039540263337 / 800000000000
    | 3 => 81246080992923 / 4000000000000
    | 4 => 218238401753631 / 4000000000000
    | 5 => 592559714176227 / 4000000000000
    | 6 => 436476803507451 / 4000000000000
    | 7 => 747910442318823 / 4000000000000
    | 8 => 550907446731957 / 4000000000000
    | 9 => 845233695494811 / 4000000000000
    | 10 => 487995901622019 / 4000000000000
    | 11 => 865957290938271 / 4000000000000
    | 12 => 809089630219899 / 4000000000000
    | 13 => 577404537564267 / 4000000000000
    | 14 => 654715205260893 / 4000000000000
    | 15 => 545833280655117 / 4000000000000
    | 16 => 482260256921457 / 4000000000000
    | 17 => 139777819452243 / 800000000000
    | 18 => 386632804708521 / 4000000000000
    | 19 => 327752910392481 / 4000000000000
    | 20 => 205092553268043 / 4000000000000
    | 21 => 110299457254581 / 4000000000000
    | 22 => 299484482746743 / 4000000000000
    | 23 => 408920457474711 / 4000000000000
    | 24 => 172907446731957 / 4000000000000
    | 25 => 702859171430997 / 4000000000000
    | _ => 469477353165723 / 4000000000000
  state := fun i =>
    match i.val with
    | 0 => (orderedInterval (70629106079 / 1000000000000) (70629106080 / 1000000000000), orderedInterval (41437807446 / 1000000000000) (41437807447 / 1000000000000))
    | 1 => (orderedInterval (91529941720 / 1000000000000) (91529941721 / 1000000000000), orderedInterval (27052176074 / 1000000000000) (27052176075 / 1000000000000))
    | 2 => (orderedInterval (17612472567 / 1000000000000) (17612472568 / 1000000000000), orderedInterval (73039525435 / 1000000000000) (73039525436 / 1000000000000))
    | 3 => (orderedInterval (138699856782 / 1000000000000) (138699905503 / 1000000000000), orderedInterval (-113425831048 / 1000000000000) (-113425782326 / 1000000000000))
    | 4 => (orderedInterval (-100908304802 / 1000000000000) (-100908302051 / 1000000000000), orderedInterval (39466672748 / 1000000000000) (39466675499 / 1000000000000))
    | 5 => (orderedInterval (-62603969683 / 1000000000000) (-62603969682 / 1000000000000), orderedInterval (-19234645459 / 1000000000000) (-19234645458 / 1000000000000))
    | 6 => (orderedInterval (3992107943 / 1000000000000) (3992107957 / 1000000000000), orderedInterval (-76296022632 / 1000000000000) (-76296022618 / 1000000000000))
    | 7 => (orderedInterval (-39051946713 / 1000000000000) (-39051915380 / 1000000000000), orderedInterval (43460373506 / 1000000000000) (43460404839 / 1000000000000))
    | 8 => (orderedInterval (18872066636 / 1000000000000) (18872066637 / 1000000000000), orderedInterval (65247691747 / 1000000000000) (65247691748 / 1000000000000))
    | 9 => (orderedInterval (-54853434976 / 1000000000000) (-54853434852 / 1000000000000), orderedInterval (2090347967 / 1000000000000) (2090348090 / 1000000000000))
    | 10 => (orderedInterval (-18656983018 / 1000000000000) (-18656983017 / 1000000000000), orderedInterval (-69710310261 / 1000000000000) (-69710310260 / 1000000000000))
    | 11 => (orderedInterval (-26200186266 / 1000000000000) (-26200186265 / 1000000000000), orderedInterval (-47417973200 / 1000000000000) (-47417973199 / 1000000000000))
    | 12 => (orderedInterval (51122680845 / 1000000000000) (51122691853 / 1000000000000), orderedInterval (-23230557826 / 1000000000000) (-23230546819 / 1000000000000))
    | 13 => (orderedInterval (38715969523 / 1000000000000) (38715969524 / 1000000000000), orderedInterval (53822350956 / 1000000000000) (53822350957 / 1000000000000))
    | 14 => (orderedInterval (55597857219 / 1000000000000) (55597857220 / 1000000000000), orderedInterval (28084597379 / 1000000000000) (28084597380 / 1000000000000))
    | 15 => (orderedInterval (-57000585728 / 1000000000000) (-57000549513 / 1000000000000), orderedInterval (37841647349 / 1000000000000) (37841683564 / 1000000000000))
    | 16 => (orderedInterval (66982634415 / 1000000000000) (66982639965 / 1000000000000), orderedInterval (-28448603607 / 1000000000000) (-28448598057 / 1000000000000))
    | 17 => (orderedInterval (-24736249082 / 1000000000000) (-24736247716 / 1000000000000), orderedInterval (55132003024 / 1000000000000) (55132004390 / 1000000000000))
    | 18 => (orderedInterval (-4293872500 / 1000000000000) (-4293872497 / 1000000000000), orderedInterval (-81020671704 / 1000000000000) (-81020671701 / 1000000000000))
    | 19 => (orderedInterval (76046584944 / 1000000000000) (76046584945 / 1000000000000), orderedInterval (44104511139 / 1000000000000) (44104511140 / 1000000000000))
    | 20 => (orderedInterval (108744280340 / 1000000000000) (108744280832 / 1000000000000), orderedInterval (-25358305389 / 1000000000000) (-25358304898 / 1000000000000))
    | 21 => (orderedInterval (-12353352851 / 1000000000000) (-12353352848 / 1000000000000), orderedInterval (-151229342009 / 1000000000000) (-151229342006 / 1000000000000))
    | 22 => (orderedInterval (23404585820 / 1000000000000) (23404585821 / 1000000000000), orderedInterval (89036002235 / 1000000000000) (89036002236 / 1000000000000))
    | 23 => (orderedInterval (48274756039 / 1000000000000) (48274779240 / 1000000000000), orderedInterval (-62661163270 / 1000000000000) (-62661140069 / 1000000000000))
    | 24 => (orderedInterval (3284826701 / 1000000000000) (3284826708 / 1000000000000), orderedInterval (121278143119 / 1000000000000) (121278143125 / 1000000000000))
    | 25 => (orderedInterval (32495999283 / 1000000000000) (32495999284 / 1000000000000), orderedInterval (50573547428 / 1000000000000) (50573547429 / 1000000000000))
    | _ => (orderedInterval (-69334485261 / 1000000000000) (-69334482200 / 1000000000000), orderedInterval (25130087488 / 1000000000000) (25130090549 / 1000000000000))
  chunkTarget := fun r b =>
    match r.val with
    | 0 =>
      match b.val with
      | 0 => orderedInterval (29881306590 / 1000000000000) (29881306598 / 1000000000000)
      | 1 => orderedInterval (-738640307 / 1000000000000) (-738639666 / 1000000000000)
      | 2 => orderedInterval (1660617930 / 1000000000000) (1660618903 / 1000000000000)
      | 3 => orderedInterval (4639953291 / 1000000000000) (4639953352 / 1000000000000)
      | 4 => orderedInterval (2456813498 / 1000000000000) (2456813708 / 1000000000000)
      | 5 => orderedInterval (-5124763545 / 1000000000000) (-5124762765 / 1000000000000)
      | 6 => orderedInterval (-77476099 / 1000000000000) (-77476058 / 1000000000000)
      | 7 => orderedInterval (-4002595040 / 1000000000000) (-4002593249 / 1000000000000)
      | _ => orderedInterval (10383558009 / 1000000000000) (10383558610 / 1000000000000)
    | 1 =>
      match b.val with
      | 0 => orderedInterval (21714846045 / 1000000000000) (21714846054 / 1000000000000)
      | 1 => orderedInterval (3239995142 / 1000000000000) (3239995328 / 1000000000000)
      | 2 => orderedInterval (-354069302 / 1000000000000) (-354067379 / 1000000000000)
      | 3 => orderedInterval (-22940796231 / 1000000000000) (-22940796104 / 1000000000000)
      | 4 => orderedInterval (8425987480 / 1000000000000) (8425987924 / 1000000000000)
      | 5 => orderedInterval (5317984927 / 1000000000000) (5317986015 / 1000000000000)
      | 6 => orderedInterval (10638050851 / 1000000000000) (10638050883 / 1000000000000)
      | 7 => orderedInterval (4409563038 / 1000000000000) (4409564973 / 1000000000000)
      | _ => orderedInterval (-13176508358 / 1000000000000) (-13176507607 / 1000000000000)
    | 2 =>
      match b.val with
      | 0 => orderedInterval (-30153468742 / 1000000000000) (-30153468732 / 1000000000000)
      | 1 => orderedInterval (-9673418629 / 1000000000000) (-9673418551 / 1000000000000)
      | 2 => orderedInterval (-5680567223 / 1000000000000) (-5680563402 / 1000000000000)
      | 3 => orderedInterval (-26640392825 / 1000000000000) (-26640392546 / 1000000000000)
      | 4 => orderedInterval (-3559255665 / 1000000000000) (-3559254719 / 1000000000000)
      | 5 => orderedInterval (9720656703 / 1000000000000) (9720658243 / 1000000000000)
      | 6 => orderedInterval (1362946187 / 1000000000000) (1362946214 / 1000000000000)
      | 7 => orderedInterval (4596973937 / 1000000000000) (4596976049 / 1000000000000)
      | _ => orderedInterval (-10786325604 / 1000000000000) (-10786324655 / 1000000000000)
    | 3 =>
      match b.val with
      | 0 => orderedInterval (-23444595905 / 1000000000000) (-23444595894 / 1000000000000)
      | 1 => orderedInterval (-5454396346 / 1000000000000) (-5454396293 / 1000000000000)
      | 2 => orderedInterval (5561770869 / 1000000000000) (5561778425 / 1000000000000)
      | 3 => orderedInterval (96589461469 / 1000000000000) (96589462082 / 1000000000000)
      | 4 => orderedInterval (-21476046814 / 1000000000000) (-21476044804 / 1000000000000)
      | 5 => orderedInterval (-13720834445 / 1000000000000) (-13720832259 / 1000000000000)
      | 6 => orderedInterval (-12116679643 / 1000000000000) (-12116679618 / 1000000000000)
      | 7 => orderedInterval (-5192735148 / 1000000000000) (-5192732864 / 1000000000000)
      | _ => orderedInterval (35542116682 / 1000000000000) (35542117877 / 1000000000000)
    | _ =>
      match b.val with
      | 0 => orderedInterval (30818288546 / 1000000000000) (30818288559 / 1000000000000)
      | 1 => orderedInterval (26578067522 / 1000000000000) (26578067577 / 1000000000000)
      | 2 => orderedInterval (20400010772 / 1000000000000) (20400025797 / 1000000000000)
      | 3 => orderedInterval (135196884154 / 1000000000000) (135196885525 / 1000000000000)
      | 4 => orderedInterval (-1517934171 / 1000000000000) (-1517929868 / 1000000000000)
      | 5 => orderedInterval (-20127579891 / 1000000000000) (-20127576729 / 1000000000000)
      | 6 => orderedInterval (-1118008255 / 1000000000000) (-1118008232 / 1000000000000)
      | 7 => orderedInterval (-5164236178 / 1000000000000) (-5164233684 / 1000000000000)
      | _ => orderedInterval (-1417828512 / 1000000000000) (-1417826986 / 1000000000000)
  coefficientTarget := fun i =>
    match i.val with
    | 0 => orderedInterval (39078774327 / 1000000000000) (39078779433 / 1000000000000)
    | 1 => orderedInterval (17275053592 / 1000000000000) (17275060087 / 1000000000000)
    | 2 => orderedInterval (-70812851861 / 1000000000000) (-70812842099 / 1000000000000)
    | 3 => orderedInterval (56288060719 / 1000000000000) (56288076652 / 1000000000000)
    | _ => orderedInterval (183647663987 / 1000000000000) (183647691959 / 1000000000000)

theorem compactCertificate213_stateChecks0 :
    compactCertificate213.stateChecks 0 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 30 12 (189 / 2)) (orderedInterval (70629106079 / 1000000000000) (70629106080 / 1000000000000), orderedInterval (41437807446 / 1000000000000) (41437807447 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 22 12 (278433089153289 / 4000000000000)) (orderedInterval (91529941720 / 1000000000000) (91529941721 / 1000000000000), orderedInterval (27052176074 / 1000000000000) (27052176075 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 36 12 (90039540263337 / 800000000000)) (orderedInterval (17612472567 / 1000000000000) (17612472568 / 1000000000000), orderedInterval (73039525435 / 1000000000000) (73039525436 / 1000000000000))) = true
  norm_num [besselStateAtRationalPoint, besselIntervalStepZero,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, besselZeroTransition,
    besselInitial, besselGridStateAt, besselGridStateBlock00, besselGridStateBlock01,
    besselGridStateBlock02, besselGridStateBlock03, besselGridStateBlock04,
    besselGridStateBlock05, besselGridStateBlock06, besselGridStateBlock07,
    besselGridStateBlock08, besselGridStateBlock09, besselGridStateBlock10,
    besselGridStateBlock11, besselGridStateBlock12, besselGridStateBlock13,
    besselGridStateBlock14, besselGridState006, besselGridState009, besselGridState014, besselGridState016, besselGridState017, besselGridState022, besselGridState024, besselGridState026, besselGridState030, besselGridState031, besselGridState033, besselGridState035, besselGridState036, besselGridState037, besselGridState038, besselGridState039, besselGridState043, besselGridState044, besselGridState046, besselGridState047, besselGridState052, besselGridState056, besselGridState060, besselGridState064, besselGridState067, besselGridState069, besselStateSubset, linearInterval, widenInterval,
    rationalErrorInterval, rationalIntervalSubset, orderedInterval, Finset.sum_range_succ,
    IntervalRat.add, IntervalRat.mul, IntervalRat.scale, IntervalRat.singleton]

theorem compactCertificate213_stateChecks1 :
    compactCertificate213.stateChecks 3 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 6 12 (81246080992923 / 4000000000000)) (orderedInterval (138699856782 / 1000000000000) (138699905503 / 1000000000000), orderedInterval (-113425831048 / 1000000000000) (-113425782326 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 17 12 (218238401753631 / 4000000000000)) (orderedInterval (-100908304802 / 1000000000000) (-100908302051 / 1000000000000), orderedInterval (39466672748 / 1000000000000) (39466675499 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 47 12 (592559714176227 / 4000000000000)) (orderedInterval (-62603969683 / 1000000000000) (-62603969682 / 1000000000000), orderedInterval (-19234645459 / 1000000000000) (-19234645458 / 1000000000000))) = true
  norm_num [besselStateAtRationalPoint, besselIntervalStepZero,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, besselZeroTransition,
    besselInitial, besselGridStateAt, besselGridStateBlock00, besselGridStateBlock01,
    besselGridStateBlock02, besselGridStateBlock03, besselGridStateBlock04,
    besselGridStateBlock05, besselGridStateBlock06, besselGridStateBlock07,
    besselGridStateBlock08, besselGridStateBlock09, besselGridStateBlock10,
    besselGridStateBlock11, besselGridStateBlock12, besselGridStateBlock13,
    besselGridStateBlock14, besselGridState006, besselGridState009, besselGridState014, besselGridState016, besselGridState017, besselGridState022, besselGridState024, besselGridState026, besselGridState030, besselGridState031, besselGridState033, besselGridState035, besselGridState036, besselGridState037, besselGridState038, besselGridState039, besselGridState043, besselGridState044, besselGridState046, besselGridState047, besselGridState052, besselGridState056, besselGridState060, besselGridState064, besselGridState067, besselGridState069, besselStateSubset, linearInterval, widenInterval,
    rationalErrorInterval, rationalIntervalSubset, orderedInterval, Finset.sum_range_succ,
    IntervalRat.add, IntervalRat.mul, IntervalRat.scale, IntervalRat.singleton]

theorem compactCertificate213_stateChecks2 :
    compactCertificate213.stateChecks 6 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 35 12 (436476803507451 / 4000000000000)) (orderedInterval (3992107943 / 1000000000000) (3992107957 / 1000000000000), orderedInterval (-76296022632 / 1000000000000) (-76296022618 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 60 12 (747910442318823 / 4000000000000)) (orderedInterval (-39051946713 / 1000000000000) (-39051915380 / 1000000000000), orderedInterval (43460373506 / 1000000000000) (43460404839 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 44 12 (550907446731957 / 4000000000000)) (orderedInterval (18872066636 / 1000000000000) (18872066637 / 1000000000000), orderedInterval (65247691747 / 1000000000000) (65247691748 / 1000000000000))) = true
  norm_num [besselStateAtRationalPoint, besselIntervalStepZero,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, besselZeroTransition,
    besselInitial, besselGridStateAt, besselGridStateBlock00, besselGridStateBlock01,
    besselGridStateBlock02, besselGridStateBlock03, besselGridStateBlock04,
    besselGridStateBlock05, besselGridStateBlock06, besselGridStateBlock07,
    besselGridStateBlock08, besselGridStateBlock09, besselGridStateBlock10,
    besselGridStateBlock11, besselGridStateBlock12, besselGridStateBlock13,
    besselGridStateBlock14, besselGridState006, besselGridState009, besselGridState014, besselGridState016, besselGridState017, besselGridState022, besselGridState024, besselGridState026, besselGridState030, besselGridState031, besselGridState033, besselGridState035, besselGridState036, besselGridState037, besselGridState038, besselGridState039, besselGridState043, besselGridState044, besselGridState046, besselGridState047, besselGridState052, besselGridState056, besselGridState060, besselGridState064, besselGridState067, besselGridState069, besselStateSubset, linearInterval, widenInterval,
    rationalErrorInterval, rationalIntervalSubset, orderedInterval, Finset.sum_range_succ,
    IntervalRat.add, IntervalRat.mul, IntervalRat.scale, IntervalRat.singleton]

theorem compactCertificate213_stateChecks3 :
    compactCertificate213.stateChecks 9 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 67 12 (845233695494811 / 4000000000000)) (orderedInterval (-54853434976 / 1000000000000) (-54853434852 / 1000000000000), orderedInterval (2090347967 / 1000000000000) (2090348090 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 39 12 (487995901622019 / 4000000000000)) (orderedInterval (-18656983018 / 1000000000000) (-18656983017 / 1000000000000), orderedInterval (-69710310261 / 1000000000000) (-69710310260 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 69 12 (865957290938271 / 4000000000000)) (orderedInterval (-26200186266 / 1000000000000) (-26200186265 / 1000000000000), orderedInterval (-47417973200 / 1000000000000) (-47417973199 / 1000000000000))) = true
  norm_num [besselStateAtRationalPoint, besselIntervalStepZero,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, besselZeroTransition,
    besselInitial, besselGridStateAt, besselGridStateBlock00, besselGridStateBlock01,
    besselGridStateBlock02, besselGridStateBlock03, besselGridStateBlock04,
    besselGridStateBlock05, besselGridStateBlock06, besselGridStateBlock07,
    besselGridStateBlock08, besselGridStateBlock09, besselGridStateBlock10,
    besselGridStateBlock11, besselGridStateBlock12, besselGridStateBlock13,
    besselGridStateBlock14, besselGridState006, besselGridState009, besselGridState014, besselGridState016, besselGridState017, besselGridState022, besselGridState024, besselGridState026, besselGridState030, besselGridState031, besselGridState033, besselGridState035, besselGridState036, besselGridState037, besselGridState038, besselGridState039, besselGridState043, besselGridState044, besselGridState046, besselGridState047, besselGridState052, besselGridState056, besselGridState060, besselGridState064, besselGridState067, besselGridState069, besselStateSubset, linearInterval, widenInterval,
    rationalErrorInterval, rationalIntervalSubset, orderedInterval, Finset.sum_range_succ,
    IntervalRat.add, IntervalRat.mul, IntervalRat.scale, IntervalRat.singleton]

theorem compactCertificate213_stateChecks4 :
    compactCertificate213.stateChecks 12 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 64 12 (809089630219899 / 4000000000000)) (orderedInterval (51122680845 / 1000000000000) (51122691853 / 1000000000000), orderedInterval (-23230557826 / 1000000000000) (-23230546819 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 46 12 (577404537564267 / 4000000000000)) (orderedInterval (38715969523 / 1000000000000) (38715969524 / 1000000000000), orderedInterval (53822350956 / 1000000000000) (53822350957 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 52 12 (654715205260893 / 4000000000000)) (orderedInterval (55597857219 / 1000000000000) (55597857220 / 1000000000000), orderedInterval (28084597379 / 1000000000000) (28084597380 / 1000000000000))) = true
  norm_num [besselStateAtRationalPoint, besselIntervalStepZero,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, besselZeroTransition,
    besselInitial, besselGridStateAt, besselGridStateBlock00, besselGridStateBlock01,
    besselGridStateBlock02, besselGridStateBlock03, besselGridStateBlock04,
    besselGridStateBlock05, besselGridStateBlock06, besselGridStateBlock07,
    besselGridStateBlock08, besselGridStateBlock09, besselGridStateBlock10,
    besselGridStateBlock11, besselGridStateBlock12, besselGridStateBlock13,
    besselGridStateBlock14, besselGridState006, besselGridState009, besselGridState014, besselGridState016, besselGridState017, besselGridState022, besselGridState024, besselGridState026, besselGridState030, besselGridState031, besselGridState033, besselGridState035, besselGridState036, besselGridState037, besselGridState038, besselGridState039, besselGridState043, besselGridState044, besselGridState046, besselGridState047, besselGridState052, besselGridState056, besselGridState060, besselGridState064, besselGridState067, besselGridState069, besselStateSubset, linearInterval, widenInterval,
    rationalErrorInterval, rationalIntervalSubset, orderedInterval, Finset.sum_range_succ,
    IntervalRat.add, IntervalRat.mul, IntervalRat.scale, IntervalRat.singleton]

theorem compactCertificate213_stateChecks5 :
    compactCertificate213.stateChecks 15 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 43 12 (545833280655117 / 4000000000000)) (orderedInterval (-57000585728 / 1000000000000) (-57000549513 / 1000000000000), orderedInterval (37841647349 / 1000000000000) (37841683564 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 38 12 (482260256921457 / 4000000000000)) (orderedInterval (66982634415 / 1000000000000) (66982639965 / 1000000000000), orderedInterval (-28448603607 / 1000000000000) (-28448598057 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 56 12 (139777819452243 / 800000000000)) (orderedInterval (-24736249082 / 1000000000000) (-24736247716 / 1000000000000), orderedInterval (55132003024 / 1000000000000) (55132004390 / 1000000000000))) = true
  norm_num [besselStateAtRationalPoint, besselIntervalStepZero,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, besselZeroTransition,
    besselInitial, besselGridStateAt, besselGridStateBlock00, besselGridStateBlock01,
    besselGridStateBlock02, besselGridStateBlock03, besselGridStateBlock04,
    besselGridStateBlock05, besselGridStateBlock06, besselGridStateBlock07,
    besselGridStateBlock08, besselGridStateBlock09, besselGridStateBlock10,
    besselGridStateBlock11, besselGridStateBlock12, besselGridStateBlock13,
    besselGridStateBlock14, besselGridState006, besselGridState009, besselGridState014, besselGridState016, besselGridState017, besselGridState022, besselGridState024, besselGridState026, besselGridState030, besselGridState031, besselGridState033, besselGridState035, besselGridState036, besselGridState037, besselGridState038, besselGridState039, besselGridState043, besselGridState044, besselGridState046, besselGridState047, besselGridState052, besselGridState056, besselGridState060, besselGridState064, besselGridState067, besselGridState069, besselStateSubset, linearInterval, widenInterval,
    rationalErrorInterval, rationalIntervalSubset, orderedInterval, Finset.sum_range_succ,
    IntervalRat.add, IntervalRat.mul, IntervalRat.scale, IntervalRat.singleton]

theorem compactCertificate213_stateChecks6 :
    compactCertificate213.stateChecks 18 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 31 12 (386632804708521 / 4000000000000)) (orderedInterval (-4293872500 / 1000000000000) (-4293872497 / 1000000000000), orderedInterval (-81020671704 / 1000000000000) (-81020671701 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 26 12 (327752910392481 / 4000000000000)) (orderedInterval (76046584944 / 1000000000000) (76046584945 / 1000000000000), orderedInterval (44104511139 / 1000000000000) (44104511140 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 16 12 (205092553268043 / 4000000000000)) (orderedInterval (108744280340 / 1000000000000) (108744280832 / 1000000000000), orderedInterval (-25358305389 / 1000000000000) (-25358304898 / 1000000000000))) = true
  norm_num [besselStateAtRationalPoint, besselIntervalStepZero,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, besselZeroTransition,
    besselInitial, besselGridStateAt, besselGridStateBlock00, besselGridStateBlock01,
    besselGridStateBlock02, besselGridStateBlock03, besselGridStateBlock04,
    besselGridStateBlock05, besselGridStateBlock06, besselGridStateBlock07,
    besselGridStateBlock08, besselGridStateBlock09, besselGridStateBlock10,
    besselGridStateBlock11, besselGridStateBlock12, besselGridStateBlock13,
    besselGridStateBlock14, besselGridState006, besselGridState009, besselGridState014, besselGridState016, besselGridState017, besselGridState022, besselGridState024, besselGridState026, besselGridState030, besselGridState031, besselGridState033, besselGridState035, besselGridState036, besselGridState037, besselGridState038, besselGridState039, besselGridState043, besselGridState044, besselGridState046, besselGridState047, besselGridState052, besselGridState056, besselGridState060, besselGridState064, besselGridState067, besselGridState069, besselStateSubset, linearInterval, widenInterval,
    rationalErrorInterval, rationalIntervalSubset, orderedInterval, Finset.sum_range_succ,
    IntervalRat.add, IntervalRat.mul, IntervalRat.scale, IntervalRat.singleton]

theorem compactCertificate213_stateChecks7 :
    compactCertificate213.stateChecks 21 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 9 12 (110299457254581 / 4000000000000)) (orderedInterval (-12353352851 / 1000000000000) (-12353352848 / 1000000000000), orderedInterval (-151229342009 / 1000000000000) (-151229342006 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 24 12 (299484482746743 / 4000000000000)) (orderedInterval (23404585820 / 1000000000000) (23404585821 / 1000000000000), orderedInterval (89036002235 / 1000000000000) (89036002236 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 33 12 (408920457474711 / 4000000000000)) (orderedInterval (48274756039 / 1000000000000) (48274779240 / 1000000000000), orderedInterval (-62661163270 / 1000000000000) (-62661140069 / 1000000000000))) = true
  norm_num [besselStateAtRationalPoint, besselIntervalStepZero,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, besselZeroTransition,
    besselInitial, besselGridStateAt, besselGridStateBlock00, besselGridStateBlock01,
    besselGridStateBlock02, besselGridStateBlock03, besselGridStateBlock04,
    besselGridStateBlock05, besselGridStateBlock06, besselGridStateBlock07,
    besselGridStateBlock08, besselGridStateBlock09, besselGridStateBlock10,
    besselGridStateBlock11, besselGridStateBlock12, besselGridStateBlock13,
    besselGridStateBlock14, besselGridState006, besselGridState009, besselGridState014, besselGridState016, besselGridState017, besselGridState022, besselGridState024, besselGridState026, besselGridState030, besselGridState031, besselGridState033, besselGridState035, besselGridState036, besselGridState037, besselGridState038, besselGridState039, besselGridState043, besselGridState044, besselGridState046, besselGridState047, besselGridState052, besselGridState056, besselGridState060, besselGridState064, besselGridState067, besselGridState069, besselStateSubset, linearInterval, widenInterval,
    rationalErrorInterval, rationalIntervalSubset, orderedInterval, Finset.sum_range_succ,
    IntervalRat.add, IntervalRat.mul, IntervalRat.scale, IntervalRat.singleton]

theorem compactCertificate213_stateChecks8 :
    compactCertificate213.stateChecks 24 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 14 12 (172907446731957 / 4000000000000)) (orderedInterval (3284826701 / 1000000000000) (3284826708 / 1000000000000), orderedInterval (121278143119 / 1000000000000) (121278143125 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 56 12 (702859171430997 / 4000000000000)) (orderedInterval (32495999283 / 1000000000000) (32495999284 / 1000000000000), orderedInterval (50573547428 / 1000000000000) (50573547429 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 37 12 (469477353165723 / 4000000000000)) (orderedInterval (-69334485261 / 1000000000000) (-69334482200 / 1000000000000), orderedInterval (25130087488 / 1000000000000) (25130090549 / 1000000000000))) = true
  norm_num [besselStateAtRationalPoint, besselIntervalStepZero,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, besselZeroTransition,
    besselInitial, besselGridStateAt, besselGridStateBlock00, besselGridStateBlock01,
    besselGridStateBlock02, besselGridStateBlock03, besselGridStateBlock04,
    besselGridStateBlock05, besselGridStateBlock06, besselGridStateBlock07,
    besselGridStateBlock08, besselGridStateBlock09, besselGridStateBlock10,
    besselGridStateBlock11, besselGridStateBlock12, besselGridStateBlock13,
    besselGridStateBlock14, besselGridState006, besselGridState009, besselGridState014, besselGridState016, besselGridState017, besselGridState022, besselGridState024, besselGridState026, besselGridState030, besselGridState031, besselGridState033, besselGridState035, besselGridState036, besselGridState037, besselGridState038, besselGridState039, besselGridState043, besselGridState044, besselGridState046, besselGridState047, besselGridState052, besselGridState056, besselGridState060, besselGridState064, besselGridState067, besselGridState069, besselStateSubset, linearInterval, widenInterval,
    rationalErrorInterval, rationalIntervalSubset, orderedInterval, Finset.sum_range_succ,
    IntervalRat.add, IntervalRat.mul, IntervalRat.scale, IntervalRat.singleton]

theorem compactCertificate213_states : ∀ j,
    BesselStateValid (compactCertificate213.point j) (compactCertificate213.state j) :=
  compactCertificate213.statesValid_of_checks3 compactCertificate213_stateChecks0
    compactCertificate213_stateChecks1 compactCertificate213_stateChecks2
    compactCertificate213_stateChecks3 compactCertificate213_stateChecks4
    compactCertificate213_stateChecks5 compactCertificate213_stateChecks6
    compactCertificate213_stateChecks7 compactCertificate213_stateChecks8

theorem compactCertificate213_chunkChecks0_0 :
    compactCertificate213.chunkChecks (0 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 0) <| besselDerivativeNearFromState (189 / 2) 0 (IntervalRat.scale (189 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (70629106079 / 1000000000000) (70629106080 / 1000000000000), orderedInterval (41437807446 / 1000000000000) (41437807447 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 0) <| besselDerivativeNearFromState (278433089153289 / 4000000000000) 0 (IntervalRat.scale (189 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (91529941720 / 1000000000000) (91529941721 / 1000000000000), orderedInterval (27052176074 / 1000000000000) (27052176075 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 0) <| besselDerivativeNearFromState (90039540263337 / 800000000000) 0 (IntervalRat.scale (189 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (17612472567 / 1000000000000) (17612472568 / 1000000000000), orderedInterval (73039525435 / 1000000000000) (73039525436 / 1000000000000)))) (orderedInterval (29881306590 / 1000000000000) (29881306598 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 0) <| besselDerivativeNearFromState (81246080992923 / 4000000000000) 0 (IntervalRat.scale (189 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (138699856782 / 1000000000000) (138699905503 / 1000000000000), orderedInterval (-113425831048 / 1000000000000) (-113425782326 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 0) <| besselDerivativeNearFromState (218238401753631 / 4000000000000) 0 (IntervalRat.scale (189 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-100908304802 / 1000000000000) (-100908302051 / 1000000000000), orderedInterval (39466672748 / 1000000000000) (39466675499 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 0) <| besselDerivativeNearFromState (592559714176227 / 4000000000000) 0 (IntervalRat.scale (189 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-62603969683 / 1000000000000) (-62603969682 / 1000000000000), orderedInterval (-19234645459 / 1000000000000) (-19234645458 / 1000000000000)))) (orderedInterval (-738640307 / 1000000000000) (-738639666 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 0) <| besselDerivativeNearFromState (436476803507451 / 4000000000000) 0 (IntervalRat.scale (189 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (3992107943 / 1000000000000) (3992107957 / 1000000000000), orderedInterval (-76296022632 / 1000000000000) (-76296022618 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 0) <| besselDerivativeNearFromState (747910442318823 / 4000000000000) 0 (IntervalRat.scale (189 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-39051946713 / 1000000000000) (-39051915380 / 1000000000000), orderedInterval (43460373506 / 1000000000000) (43460404839 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 0) <| besselDerivativeNearFromState (550907446731957 / 4000000000000) 0 (IntervalRat.scale (189 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (18872066636 / 1000000000000) (18872066637 / 1000000000000), orderedInterval (65247691747 / 1000000000000) (65247691748 / 1000000000000)))) (orderedInterval (1660617930 / 1000000000000) (1660618903 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate213_chunkChecks0_1 :
    compactCertificate213.chunkChecks (0 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 0) <| besselDerivativeNearFromState (845233695494811 / 4000000000000) 0 (IntervalRat.scale (189 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-54853434976 / 1000000000000) (-54853434852 / 1000000000000), orderedInterval (2090347967 / 1000000000000) (2090348090 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 0) <| besselDerivativeNearFromState (487995901622019 / 4000000000000) 0 (IntervalRat.scale (189 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-18656983018 / 1000000000000) (-18656983017 / 1000000000000), orderedInterval (-69710310261 / 1000000000000) (-69710310260 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 0) <| besselDerivativeNearFromState (865957290938271 / 4000000000000) 0 (IntervalRat.scale (189 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-26200186266 / 1000000000000) (-26200186265 / 1000000000000), orderedInterval (-47417973200 / 1000000000000) (-47417973199 / 1000000000000)))) (orderedInterval (4639953291 / 1000000000000) (4639953352 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 0) <| besselDerivativeNearFromState (809089630219899 / 4000000000000) 0 (IntervalRat.scale (189 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (51122680845 / 1000000000000) (51122691853 / 1000000000000), orderedInterval (-23230557826 / 1000000000000) (-23230546819 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 0) <| besselDerivativeNearFromState (577404537564267 / 4000000000000) 0 (IntervalRat.scale (189 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (38715969523 / 1000000000000) (38715969524 / 1000000000000), orderedInterval (53822350956 / 1000000000000) (53822350957 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 0) <| besselDerivativeNearFromState (654715205260893 / 4000000000000) 0 (IntervalRat.scale (189 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (55597857219 / 1000000000000) (55597857220 / 1000000000000), orderedInterval (28084597379 / 1000000000000) (28084597380 / 1000000000000)))) (orderedInterval (2456813498 / 1000000000000) (2456813708 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 0) <| besselDerivativeNearFromState (545833280655117 / 4000000000000) 0 (IntervalRat.scale (189 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-57000585728 / 1000000000000) (-57000549513 / 1000000000000), orderedInterval (37841647349 / 1000000000000) (37841683564 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 0) <| besselDerivativeNearFromState (482260256921457 / 4000000000000) 0 (IntervalRat.scale (189 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (66982634415 / 1000000000000) (66982639965 / 1000000000000), orderedInterval (-28448603607 / 1000000000000) (-28448598057 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 0) <| besselDerivativeNearFromState (139777819452243 / 800000000000) 0 (IntervalRat.scale (189 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-24736249082 / 1000000000000) (-24736247716 / 1000000000000), orderedInterval (55132003024 / 1000000000000) (55132004390 / 1000000000000)))) (orderedInterval (-5124763545 / 1000000000000) (-5124762765 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate213_chunkChecks0_2 :
    compactCertificate213.chunkChecks (0 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 0) <| besselDerivativeNearFromState (386632804708521 / 4000000000000) 0 (IntervalRat.scale (189 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-4293872500 / 1000000000000) (-4293872497 / 1000000000000), orderedInterval (-81020671704 / 1000000000000) (-81020671701 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 0) <| besselDerivativeNearFromState (327752910392481 / 4000000000000) 0 (IntervalRat.scale (189 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (76046584944 / 1000000000000) (76046584945 / 1000000000000), orderedInterval (44104511139 / 1000000000000) (44104511140 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 0) <| besselDerivativeNearFromState (205092553268043 / 4000000000000) 0 (IntervalRat.scale (189 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (108744280340 / 1000000000000) (108744280832 / 1000000000000), orderedInterval (-25358305389 / 1000000000000) (-25358304898 / 1000000000000)))) (orderedInterval (-77476099 / 1000000000000) (-77476058 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 0) <| besselDerivativeNearFromState (110299457254581 / 4000000000000) 0 (IntervalRat.scale (189 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-12353352851 / 1000000000000) (-12353352848 / 1000000000000), orderedInterval (-151229342009 / 1000000000000) (-151229342006 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 0) <| besselDerivativeNearFromState (299484482746743 / 4000000000000) 0 (IntervalRat.scale (189 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (23404585820 / 1000000000000) (23404585821 / 1000000000000), orderedInterval (89036002235 / 1000000000000) (89036002236 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 0) <| besselDerivativeNearFromState (408920457474711 / 4000000000000) 0 (IntervalRat.scale (189 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (48274756039 / 1000000000000) (48274779240 / 1000000000000), orderedInterval (-62661163270 / 1000000000000) (-62661140069 / 1000000000000)))) (orderedInterval (-4002595040 / 1000000000000) (-4002593249 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 0) <| besselDerivativeNearFromState (172907446731957 / 4000000000000) 0 (IntervalRat.scale (189 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (3284826701 / 1000000000000) (3284826708 / 1000000000000), orderedInterval (121278143119 / 1000000000000) (121278143125 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 0) <| besselDerivativeNearFromState (702859171430997 / 4000000000000) 0 (IntervalRat.scale (189 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (32495999283 / 1000000000000) (32495999284 / 1000000000000), orderedInterval (50573547428 / 1000000000000) (50573547429 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 0) <| besselDerivativeNearFromState (469477353165723 / 4000000000000) 0 (IntervalRat.scale (189 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-69334485261 / 1000000000000) (-69334482200 / 1000000000000), orderedInterval (25130087488 / 1000000000000) (25130090549 / 1000000000000)))) (orderedInterval (10383558009 / 1000000000000) (10383558610 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate213_chunkChecks0 :
    compactCertificate213.chunkChecks (0 : Fin 5) 0 9 = true :=
  compactCertificate213.chunkChecks_nine_of_three (0 : Fin 5) compactCertificate213_chunkChecks0_0
    compactCertificate213_chunkChecks0_1 compactCertificate213_chunkChecks0_2

theorem compactCertificate213_chunkChecks1_0 :
    compactCertificate213.chunkChecks (1 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 1) <| besselDerivativeNearFromState (189 / 2) 1 (IntervalRat.scale (189 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (70629106079 / 1000000000000) (70629106080 / 1000000000000), orderedInterval (41437807446 / 1000000000000) (41437807447 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 1) <| besselDerivativeNearFromState (278433089153289 / 4000000000000) 1 (IntervalRat.scale (189 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (91529941720 / 1000000000000) (91529941721 / 1000000000000), orderedInterval (27052176074 / 1000000000000) (27052176075 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 1) <| besselDerivativeNearFromState (90039540263337 / 800000000000) 1 (IntervalRat.scale (189 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (17612472567 / 1000000000000) (17612472568 / 1000000000000), orderedInterval (73039525435 / 1000000000000) (73039525436 / 1000000000000)))) (orderedInterval (21714846045 / 1000000000000) (21714846054 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 1) <| besselDerivativeNearFromState (81246080992923 / 4000000000000) 1 (IntervalRat.scale (189 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (138699856782 / 1000000000000) (138699905503 / 1000000000000), orderedInterval (-113425831048 / 1000000000000) (-113425782326 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 1) <| besselDerivativeNearFromState (218238401753631 / 4000000000000) 1 (IntervalRat.scale (189 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-100908304802 / 1000000000000) (-100908302051 / 1000000000000), orderedInterval (39466672748 / 1000000000000) (39466675499 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 1) <| besselDerivativeNearFromState (592559714176227 / 4000000000000) 1 (IntervalRat.scale (189 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-62603969683 / 1000000000000) (-62603969682 / 1000000000000), orderedInterval (-19234645459 / 1000000000000) (-19234645458 / 1000000000000)))) (orderedInterval (3239995142 / 1000000000000) (3239995328 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 1) <| besselDerivativeNearFromState (436476803507451 / 4000000000000) 1 (IntervalRat.scale (189 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (3992107943 / 1000000000000) (3992107957 / 1000000000000), orderedInterval (-76296022632 / 1000000000000) (-76296022618 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 1) <| besselDerivativeNearFromState (747910442318823 / 4000000000000) 1 (IntervalRat.scale (189 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-39051946713 / 1000000000000) (-39051915380 / 1000000000000), orderedInterval (43460373506 / 1000000000000) (43460404839 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 1) <| besselDerivativeNearFromState (550907446731957 / 4000000000000) 1 (IntervalRat.scale (189 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (18872066636 / 1000000000000) (18872066637 / 1000000000000), orderedInterval (65247691747 / 1000000000000) (65247691748 / 1000000000000)))) (orderedInterval (-354069302 / 1000000000000) (-354067379 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate213_chunkChecks1_1 :
    compactCertificate213.chunkChecks (1 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 1) <| besselDerivativeNearFromState (845233695494811 / 4000000000000) 1 (IntervalRat.scale (189 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-54853434976 / 1000000000000) (-54853434852 / 1000000000000), orderedInterval (2090347967 / 1000000000000) (2090348090 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 1) <| besselDerivativeNearFromState (487995901622019 / 4000000000000) 1 (IntervalRat.scale (189 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-18656983018 / 1000000000000) (-18656983017 / 1000000000000), orderedInterval (-69710310261 / 1000000000000) (-69710310260 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 1) <| besselDerivativeNearFromState (865957290938271 / 4000000000000) 1 (IntervalRat.scale (189 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-26200186266 / 1000000000000) (-26200186265 / 1000000000000), orderedInterval (-47417973200 / 1000000000000) (-47417973199 / 1000000000000)))) (orderedInterval (-22940796231 / 1000000000000) (-22940796104 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 1) <| besselDerivativeNearFromState (809089630219899 / 4000000000000) 1 (IntervalRat.scale (189 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (51122680845 / 1000000000000) (51122691853 / 1000000000000), orderedInterval (-23230557826 / 1000000000000) (-23230546819 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 1) <| besselDerivativeNearFromState (577404537564267 / 4000000000000) 1 (IntervalRat.scale (189 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (38715969523 / 1000000000000) (38715969524 / 1000000000000), orderedInterval (53822350956 / 1000000000000) (53822350957 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 1) <| besselDerivativeNearFromState (654715205260893 / 4000000000000) 1 (IntervalRat.scale (189 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (55597857219 / 1000000000000) (55597857220 / 1000000000000), orderedInterval (28084597379 / 1000000000000) (28084597380 / 1000000000000)))) (orderedInterval (8425987480 / 1000000000000) (8425987924 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 1) <| besselDerivativeNearFromState (545833280655117 / 4000000000000) 1 (IntervalRat.scale (189 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-57000585728 / 1000000000000) (-57000549513 / 1000000000000), orderedInterval (37841647349 / 1000000000000) (37841683564 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 1) <| besselDerivativeNearFromState (482260256921457 / 4000000000000) 1 (IntervalRat.scale (189 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (66982634415 / 1000000000000) (66982639965 / 1000000000000), orderedInterval (-28448603607 / 1000000000000) (-28448598057 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 1) <| besselDerivativeNearFromState (139777819452243 / 800000000000) 1 (IntervalRat.scale (189 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-24736249082 / 1000000000000) (-24736247716 / 1000000000000), orderedInterval (55132003024 / 1000000000000) (55132004390 / 1000000000000)))) (orderedInterval (5317984927 / 1000000000000) (5317986015 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate213_chunkChecks1_2 :
    compactCertificate213.chunkChecks (1 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 1) <| besselDerivativeNearFromState (386632804708521 / 4000000000000) 1 (IntervalRat.scale (189 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-4293872500 / 1000000000000) (-4293872497 / 1000000000000), orderedInterval (-81020671704 / 1000000000000) (-81020671701 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 1) <| besselDerivativeNearFromState (327752910392481 / 4000000000000) 1 (IntervalRat.scale (189 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (76046584944 / 1000000000000) (76046584945 / 1000000000000), orderedInterval (44104511139 / 1000000000000) (44104511140 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 1) <| besselDerivativeNearFromState (205092553268043 / 4000000000000) 1 (IntervalRat.scale (189 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (108744280340 / 1000000000000) (108744280832 / 1000000000000), orderedInterval (-25358305389 / 1000000000000) (-25358304898 / 1000000000000)))) (orderedInterval (10638050851 / 1000000000000) (10638050883 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 1) <| besselDerivativeNearFromState (110299457254581 / 4000000000000) 1 (IntervalRat.scale (189 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-12353352851 / 1000000000000) (-12353352848 / 1000000000000), orderedInterval (-151229342009 / 1000000000000) (-151229342006 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 1) <| besselDerivativeNearFromState (299484482746743 / 4000000000000) 1 (IntervalRat.scale (189 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (23404585820 / 1000000000000) (23404585821 / 1000000000000), orderedInterval (89036002235 / 1000000000000) (89036002236 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 1) <| besselDerivativeNearFromState (408920457474711 / 4000000000000) 1 (IntervalRat.scale (189 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (48274756039 / 1000000000000) (48274779240 / 1000000000000), orderedInterval (-62661163270 / 1000000000000) (-62661140069 / 1000000000000)))) (orderedInterval (4409563038 / 1000000000000) (4409564973 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 1) <| besselDerivativeNearFromState (172907446731957 / 4000000000000) 1 (IntervalRat.scale (189 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (3284826701 / 1000000000000) (3284826708 / 1000000000000), orderedInterval (121278143119 / 1000000000000) (121278143125 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 1) <| besselDerivativeNearFromState (702859171430997 / 4000000000000) 1 (IntervalRat.scale (189 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (32495999283 / 1000000000000) (32495999284 / 1000000000000), orderedInterval (50573547428 / 1000000000000) (50573547429 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 1) <| besselDerivativeNearFromState (469477353165723 / 4000000000000) 1 (IntervalRat.scale (189 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-69334485261 / 1000000000000) (-69334482200 / 1000000000000), orderedInterval (25130087488 / 1000000000000) (25130090549 / 1000000000000)))) (orderedInterval (-13176508358 / 1000000000000) (-13176507607 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate213_chunkChecks1 :
    compactCertificate213.chunkChecks (1 : Fin 5) 0 9 = true :=
  compactCertificate213.chunkChecks_nine_of_three (1 : Fin 5) compactCertificate213_chunkChecks1_0
    compactCertificate213_chunkChecks1_1 compactCertificate213_chunkChecks1_2

theorem compactCertificate213_chunkChecks2_0 :
    compactCertificate213.chunkChecks (2 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 2) <| besselDerivativeNearFromState (189 / 2) 2 (IntervalRat.scale (189 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (70629106079 / 1000000000000) (70629106080 / 1000000000000), orderedInterval (41437807446 / 1000000000000) (41437807447 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 2) <| besselDerivativeNearFromState (278433089153289 / 4000000000000) 2 (IntervalRat.scale (189 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (91529941720 / 1000000000000) (91529941721 / 1000000000000), orderedInterval (27052176074 / 1000000000000) (27052176075 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 2) <| besselDerivativeNearFromState (90039540263337 / 800000000000) 2 (IntervalRat.scale (189 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (17612472567 / 1000000000000) (17612472568 / 1000000000000), orderedInterval (73039525435 / 1000000000000) (73039525436 / 1000000000000)))) (orderedInterval (-30153468742 / 1000000000000) (-30153468732 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 2) <| besselDerivativeNearFromState (81246080992923 / 4000000000000) 2 (IntervalRat.scale (189 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (138699856782 / 1000000000000) (138699905503 / 1000000000000), orderedInterval (-113425831048 / 1000000000000) (-113425782326 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 2) <| besselDerivativeNearFromState (218238401753631 / 4000000000000) 2 (IntervalRat.scale (189 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-100908304802 / 1000000000000) (-100908302051 / 1000000000000), orderedInterval (39466672748 / 1000000000000) (39466675499 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 2) <| besselDerivativeNearFromState (592559714176227 / 4000000000000) 2 (IntervalRat.scale (189 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-62603969683 / 1000000000000) (-62603969682 / 1000000000000), orderedInterval (-19234645459 / 1000000000000) (-19234645458 / 1000000000000)))) (orderedInterval (-9673418629 / 1000000000000) (-9673418551 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 2) <| besselDerivativeNearFromState (436476803507451 / 4000000000000) 2 (IntervalRat.scale (189 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (3992107943 / 1000000000000) (3992107957 / 1000000000000), orderedInterval (-76296022632 / 1000000000000) (-76296022618 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 2) <| besselDerivativeNearFromState (747910442318823 / 4000000000000) 2 (IntervalRat.scale (189 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-39051946713 / 1000000000000) (-39051915380 / 1000000000000), orderedInterval (43460373506 / 1000000000000) (43460404839 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 2) <| besselDerivativeNearFromState (550907446731957 / 4000000000000) 2 (IntervalRat.scale (189 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (18872066636 / 1000000000000) (18872066637 / 1000000000000), orderedInterval (65247691747 / 1000000000000) (65247691748 / 1000000000000)))) (orderedInterval (-5680567223 / 1000000000000) (-5680563402 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate213_chunkChecks2_1 :
    compactCertificate213.chunkChecks (2 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 2) <| besselDerivativeNearFromState (845233695494811 / 4000000000000) 2 (IntervalRat.scale (189 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-54853434976 / 1000000000000) (-54853434852 / 1000000000000), orderedInterval (2090347967 / 1000000000000) (2090348090 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 2) <| besselDerivativeNearFromState (487995901622019 / 4000000000000) 2 (IntervalRat.scale (189 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-18656983018 / 1000000000000) (-18656983017 / 1000000000000), orderedInterval (-69710310261 / 1000000000000) (-69710310260 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 2) <| besselDerivativeNearFromState (865957290938271 / 4000000000000) 2 (IntervalRat.scale (189 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-26200186266 / 1000000000000) (-26200186265 / 1000000000000), orderedInterval (-47417973200 / 1000000000000) (-47417973199 / 1000000000000)))) (orderedInterval (-26640392825 / 1000000000000) (-26640392546 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 2) <| besselDerivativeNearFromState (809089630219899 / 4000000000000) 2 (IntervalRat.scale (189 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (51122680845 / 1000000000000) (51122691853 / 1000000000000), orderedInterval (-23230557826 / 1000000000000) (-23230546819 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 2) <| besselDerivativeNearFromState (577404537564267 / 4000000000000) 2 (IntervalRat.scale (189 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (38715969523 / 1000000000000) (38715969524 / 1000000000000), orderedInterval (53822350956 / 1000000000000) (53822350957 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 2) <| besselDerivativeNearFromState (654715205260893 / 4000000000000) 2 (IntervalRat.scale (189 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (55597857219 / 1000000000000) (55597857220 / 1000000000000), orderedInterval (28084597379 / 1000000000000) (28084597380 / 1000000000000)))) (orderedInterval (-3559255665 / 1000000000000) (-3559254719 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 2) <| besselDerivativeNearFromState (545833280655117 / 4000000000000) 2 (IntervalRat.scale (189 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-57000585728 / 1000000000000) (-57000549513 / 1000000000000), orderedInterval (37841647349 / 1000000000000) (37841683564 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 2) <| besselDerivativeNearFromState (482260256921457 / 4000000000000) 2 (IntervalRat.scale (189 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (66982634415 / 1000000000000) (66982639965 / 1000000000000), orderedInterval (-28448603607 / 1000000000000) (-28448598057 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 2) <| besselDerivativeNearFromState (139777819452243 / 800000000000) 2 (IntervalRat.scale (189 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-24736249082 / 1000000000000) (-24736247716 / 1000000000000), orderedInterval (55132003024 / 1000000000000) (55132004390 / 1000000000000)))) (orderedInterval (9720656703 / 1000000000000) (9720658243 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate213_chunkChecks2_2 :
    compactCertificate213.chunkChecks (2 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 2) <| besselDerivativeNearFromState (386632804708521 / 4000000000000) 2 (IntervalRat.scale (189 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-4293872500 / 1000000000000) (-4293872497 / 1000000000000), orderedInterval (-81020671704 / 1000000000000) (-81020671701 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 2) <| besselDerivativeNearFromState (327752910392481 / 4000000000000) 2 (IntervalRat.scale (189 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (76046584944 / 1000000000000) (76046584945 / 1000000000000), orderedInterval (44104511139 / 1000000000000) (44104511140 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 2) <| besselDerivativeNearFromState (205092553268043 / 4000000000000) 2 (IntervalRat.scale (189 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (108744280340 / 1000000000000) (108744280832 / 1000000000000), orderedInterval (-25358305389 / 1000000000000) (-25358304898 / 1000000000000)))) (orderedInterval (1362946187 / 1000000000000) (1362946214 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 2) <| besselDerivativeNearFromState (110299457254581 / 4000000000000) 2 (IntervalRat.scale (189 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-12353352851 / 1000000000000) (-12353352848 / 1000000000000), orderedInterval (-151229342009 / 1000000000000) (-151229342006 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 2) <| besselDerivativeNearFromState (299484482746743 / 4000000000000) 2 (IntervalRat.scale (189 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (23404585820 / 1000000000000) (23404585821 / 1000000000000), orderedInterval (89036002235 / 1000000000000) (89036002236 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 2) <| besselDerivativeNearFromState (408920457474711 / 4000000000000) 2 (IntervalRat.scale (189 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (48274756039 / 1000000000000) (48274779240 / 1000000000000), orderedInterval (-62661163270 / 1000000000000) (-62661140069 / 1000000000000)))) (orderedInterval (4596973937 / 1000000000000) (4596976049 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 2) <| besselDerivativeNearFromState (172907446731957 / 4000000000000) 2 (IntervalRat.scale (189 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (3284826701 / 1000000000000) (3284826708 / 1000000000000), orderedInterval (121278143119 / 1000000000000) (121278143125 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 2) <| besselDerivativeNearFromState (702859171430997 / 4000000000000) 2 (IntervalRat.scale (189 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (32495999283 / 1000000000000) (32495999284 / 1000000000000), orderedInterval (50573547428 / 1000000000000) (50573547429 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 2) <| besselDerivativeNearFromState (469477353165723 / 4000000000000) 2 (IntervalRat.scale (189 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-69334485261 / 1000000000000) (-69334482200 / 1000000000000), orderedInterval (25130087488 / 1000000000000) (25130090549 / 1000000000000)))) (orderedInterval (-10786325604 / 1000000000000) (-10786324655 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate213_chunkChecks2 :
    compactCertificate213.chunkChecks (2 : Fin 5) 0 9 = true :=
  compactCertificate213.chunkChecks_nine_of_three (2 : Fin 5) compactCertificate213_chunkChecks2_0
    compactCertificate213_chunkChecks2_1 compactCertificate213_chunkChecks2_2

theorem compactCertificate213_chunkChecks3_0 :
    compactCertificate213.chunkChecks (3 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 3) <| besselDerivativeNearFromState (189 / 2) 3 (IntervalRat.scale (189 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (70629106079 / 1000000000000) (70629106080 / 1000000000000), orderedInterval (41437807446 / 1000000000000) (41437807447 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 3) <| besselDerivativeNearFromState (278433089153289 / 4000000000000) 3 (IntervalRat.scale (189 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (91529941720 / 1000000000000) (91529941721 / 1000000000000), orderedInterval (27052176074 / 1000000000000) (27052176075 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 3) <| besselDerivativeNearFromState (90039540263337 / 800000000000) 3 (IntervalRat.scale (189 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (17612472567 / 1000000000000) (17612472568 / 1000000000000), orderedInterval (73039525435 / 1000000000000) (73039525436 / 1000000000000)))) (orderedInterval (-23444595905 / 1000000000000) (-23444595894 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 3) <| besselDerivativeNearFromState (81246080992923 / 4000000000000) 3 (IntervalRat.scale (189 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (138699856782 / 1000000000000) (138699905503 / 1000000000000), orderedInterval (-113425831048 / 1000000000000) (-113425782326 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 3) <| besselDerivativeNearFromState (218238401753631 / 4000000000000) 3 (IntervalRat.scale (189 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-100908304802 / 1000000000000) (-100908302051 / 1000000000000), orderedInterval (39466672748 / 1000000000000) (39466675499 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 3) <| besselDerivativeNearFromState (592559714176227 / 4000000000000) 3 (IntervalRat.scale (189 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-62603969683 / 1000000000000) (-62603969682 / 1000000000000), orderedInterval (-19234645459 / 1000000000000) (-19234645458 / 1000000000000)))) (orderedInterval (-5454396346 / 1000000000000) (-5454396293 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 3) <| besselDerivativeNearFromState (436476803507451 / 4000000000000) 3 (IntervalRat.scale (189 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (3992107943 / 1000000000000) (3992107957 / 1000000000000), orderedInterval (-76296022632 / 1000000000000) (-76296022618 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 3) <| besselDerivativeNearFromState (747910442318823 / 4000000000000) 3 (IntervalRat.scale (189 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-39051946713 / 1000000000000) (-39051915380 / 1000000000000), orderedInterval (43460373506 / 1000000000000) (43460404839 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 3) <| besselDerivativeNearFromState (550907446731957 / 4000000000000) 3 (IntervalRat.scale (189 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (18872066636 / 1000000000000) (18872066637 / 1000000000000), orderedInterval (65247691747 / 1000000000000) (65247691748 / 1000000000000)))) (orderedInterval (5561770869 / 1000000000000) (5561778425 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate213_chunkChecks3_1 :
    compactCertificate213.chunkChecks (3 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 3) <| besselDerivativeNearFromState (845233695494811 / 4000000000000) 3 (IntervalRat.scale (189 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-54853434976 / 1000000000000) (-54853434852 / 1000000000000), orderedInterval (2090347967 / 1000000000000) (2090348090 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 3) <| besselDerivativeNearFromState (487995901622019 / 4000000000000) 3 (IntervalRat.scale (189 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-18656983018 / 1000000000000) (-18656983017 / 1000000000000), orderedInterval (-69710310261 / 1000000000000) (-69710310260 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 3) <| besselDerivativeNearFromState (865957290938271 / 4000000000000) 3 (IntervalRat.scale (189 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-26200186266 / 1000000000000) (-26200186265 / 1000000000000), orderedInterval (-47417973200 / 1000000000000) (-47417973199 / 1000000000000)))) (orderedInterval (96589461469 / 1000000000000) (96589462082 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 3) <| besselDerivativeNearFromState (809089630219899 / 4000000000000) 3 (IntervalRat.scale (189 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (51122680845 / 1000000000000) (51122691853 / 1000000000000), orderedInterval (-23230557826 / 1000000000000) (-23230546819 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 3) <| besselDerivativeNearFromState (577404537564267 / 4000000000000) 3 (IntervalRat.scale (189 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (38715969523 / 1000000000000) (38715969524 / 1000000000000), orderedInterval (53822350956 / 1000000000000) (53822350957 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 3) <| besselDerivativeNearFromState (654715205260893 / 4000000000000) 3 (IntervalRat.scale (189 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (55597857219 / 1000000000000) (55597857220 / 1000000000000), orderedInterval (28084597379 / 1000000000000) (28084597380 / 1000000000000)))) (orderedInterval (-21476046814 / 1000000000000) (-21476044804 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 3) <| besselDerivativeNearFromState (545833280655117 / 4000000000000) 3 (IntervalRat.scale (189 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-57000585728 / 1000000000000) (-57000549513 / 1000000000000), orderedInterval (37841647349 / 1000000000000) (37841683564 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 3) <| besselDerivativeNearFromState (482260256921457 / 4000000000000) 3 (IntervalRat.scale (189 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (66982634415 / 1000000000000) (66982639965 / 1000000000000), orderedInterval (-28448603607 / 1000000000000) (-28448598057 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 3) <| besselDerivativeNearFromState (139777819452243 / 800000000000) 3 (IntervalRat.scale (189 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-24736249082 / 1000000000000) (-24736247716 / 1000000000000), orderedInterval (55132003024 / 1000000000000) (55132004390 / 1000000000000)))) (orderedInterval (-13720834445 / 1000000000000) (-13720832259 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate213_chunkChecks3_2 :
    compactCertificate213.chunkChecks (3 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 3) <| besselDerivativeNearFromState (386632804708521 / 4000000000000) 3 (IntervalRat.scale (189 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-4293872500 / 1000000000000) (-4293872497 / 1000000000000), orderedInterval (-81020671704 / 1000000000000) (-81020671701 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 3) <| besselDerivativeNearFromState (327752910392481 / 4000000000000) 3 (IntervalRat.scale (189 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (76046584944 / 1000000000000) (76046584945 / 1000000000000), orderedInterval (44104511139 / 1000000000000) (44104511140 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 3) <| besselDerivativeNearFromState (205092553268043 / 4000000000000) 3 (IntervalRat.scale (189 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (108744280340 / 1000000000000) (108744280832 / 1000000000000), orderedInterval (-25358305389 / 1000000000000) (-25358304898 / 1000000000000)))) (orderedInterval (-12116679643 / 1000000000000) (-12116679618 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 3) <| besselDerivativeNearFromState (110299457254581 / 4000000000000) 3 (IntervalRat.scale (189 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-12353352851 / 1000000000000) (-12353352848 / 1000000000000), orderedInterval (-151229342009 / 1000000000000) (-151229342006 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 3) <| besselDerivativeNearFromState (299484482746743 / 4000000000000) 3 (IntervalRat.scale (189 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (23404585820 / 1000000000000) (23404585821 / 1000000000000), orderedInterval (89036002235 / 1000000000000) (89036002236 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 3) <| besselDerivativeNearFromState (408920457474711 / 4000000000000) 3 (IntervalRat.scale (189 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (48274756039 / 1000000000000) (48274779240 / 1000000000000), orderedInterval (-62661163270 / 1000000000000) (-62661140069 / 1000000000000)))) (orderedInterval (-5192735148 / 1000000000000) (-5192732864 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 3) <| besselDerivativeNearFromState (172907446731957 / 4000000000000) 3 (IntervalRat.scale (189 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (3284826701 / 1000000000000) (3284826708 / 1000000000000), orderedInterval (121278143119 / 1000000000000) (121278143125 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 3) <| besselDerivativeNearFromState (702859171430997 / 4000000000000) 3 (IntervalRat.scale (189 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (32495999283 / 1000000000000) (32495999284 / 1000000000000), orderedInterval (50573547428 / 1000000000000) (50573547429 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 3) <| besselDerivativeNearFromState (469477353165723 / 4000000000000) 3 (IntervalRat.scale (189 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-69334485261 / 1000000000000) (-69334482200 / 1000000000000), orderedInterval (25130087488 / 1000000000000) (25130090549 / 1000000000000)))) (orderedInterval (35542116682 / 1000000000000) (35542117877 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate213_chunkChecks3 :
    compactCertificate213.chunkChecks (3 : Fin 5) 0 9 = true :=
  compactCertificate213.chunkChecks_nine_of_three (3 : Fin 5) compactCertificate213_chunkChecks3_0
    compactCertificate213_chunkChecks3_1 compactCertificate213_chunkChecks3_2

theorem compactCertificate213_chunkChecks4_0 :
    compactCertificate213.chunkChecks (4 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 4) <| besselDerivativeNearFromState (189 / 2) 4 (IntervalRat.scale (189 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (70629106079 / 1000000000000) (70629106080 / 1000000000000), orderedInterval (41437807446 / 1000000000000) (41437807447 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 4) <| besselDerivativeNearFromState (278433089153289 / 4000000000000) 4 (IntervalRat.scale (189 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (91529941720 / 1000000000000) (91529941721 / 1000000000000), orderedInterval (27052176074 / 1000000000000) (27052176075 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 4) <| besselDerivativeNearFromState (90039540263337 / 800000000000) 4 (IntervalRat.scale (189 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (17612472567 / 1000000000000) (17612472568 / 1000000000000), orderedInterval (73039525435 / 1000000000000) (73039525436 / 1000000000000)))) (orderedInterval (30818288546 / 1000000000000) (30818288559 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 4) <| besselDerivativeNearFromState (81246080992923 / 4000000000000) 4 (IntervalRat.scale (189 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (138699856782 / 1000000000000) (138699905503 / 1000000000000), orderedInterval (-113425831048 / 1000000000000) (-113425782326 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 4) <| besselDerivativeNearFromState (218238401753631 / 4000000000000) 4 (IntervalRat.scale (189 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-100908304802 / 1000000000000) (-100908302051 / 1000000000000), orderedInterval (39466672748 / 1000000000000) (39466675499 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 4) <| besselDerivativeNearFromState (592559714176227 / 4000000000000) 4 (IntervalRat.scale (189 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-62603969683 / 1000000000000) (-62603969682 / 1000000000000), orderedInterval (-19234645459 / 1000000000000) (-19234645458 / 1000000000000)))) (orderedInterval (26578067522 / 1000000000000) (26578067577 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 4) <| besselDerivativeNearFromState (436476803507451 / 4000000000000) 4 (IntervalRat.scale (189 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (3992107943 / 1000000000000) (3992107957 / 1000000000000), orderedInterval (-76296022632 / 1000000000000) (-76296022618 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 4) <| besselDerivativeNearFromState (747910442318823 / 4000000000000) 4 (IntervalRat.scale (189 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-39051946713 / 1000000000000) (-39051915380 / 1000000000000), orderedInterval (43460373506 / 1000000000000) (43460404839 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 4) <| besselDerivativeNearFromState (550907446731957 / 4000000000000) 4 (IntervalRat.scale (189 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (18872066636 / 1000000000000) (18872066637 / 1000000000000), orderedInterval (65247691747 / 1000000000000) (65247691748 / 1000000000000)))) (orderedInterval (20400010772 / 1000000000000) (20400025797 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate213_chunkChecks4_1 :
    compactCertificate213.chunkChecks (4 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 4) <| besselDerivativeNearFromState (845233695494811 / 4000000000000) 4 (IntervalRat.scale (189 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-54853434976 / 1000000000000) (-54853434852 / 1000000000000), orderedInterval (2090347967 / 1000000000000) (2090348090 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 4) <| besselDerivativeNearFromState (487995901622019 / 4000000000000) 4 (IntervalRat.scale (189 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-18656983018 / 1000000000000) (-18656983017 / 1000000000000), orderedInterval (-69710310261 / 1000000000000) (-69710310260 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 4) <| besselDerivativeNearFromState (865957290938271 / 4000000000000) 4 (IntervalRat.scale (189 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-26200186266 / 1000000000000) (-26200186265 / 1000000000000), orderedInterval (-47417973200 / 1000000000000) (-47417973199 / 1000000000000)))) (orderedInterval (135196884154 / 1000000000000) (135196885525 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 4) <| besselDerivativeNearFromState (809089630219899 / 4000000000000) 4 (IntervalRat.scale (189 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (51122680845 / 1000000000000) (51122691853 / 1000000000000), orderedInterval (-23230557826 / 1000000000000) (-23230546819 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 4) <| besselDerivativeNearFromState (577404537564267 / 4000000000000) 4 (IntervalRat.scale (189 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (38715969523 / 1000000000000) (38715969524 / 1000000000000), orderedInterval (53822350956 / 1000000000000) (53822350957 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 4) <| besselDerivativeNearFromState (654715205260893 / 4000000000000) 4 (IntervalRat.scale (189 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (55597857219 / 1000000000000) (55597857220 / 1000000000000), orderedInterval (28084597379 / 1000000000000) (28084597380 / 1000000000000)))) (orderedInterval (-1517934171 / 1000000000000) (-1517929868 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 4) <| besselDerivativeNearFromState (545833280655117 / 4000000000000) 4 (IntervalRat.scale (189 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-57000585728 / 1000000000000) (-57000549513 / 1000000000000), orderedInterval (37841647349 / 1000000000000) (37841683564 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 4) <| besselDerivativeNearFromState (482260256921457 / 4000000000000) 4 (IntervalRat.scale (189 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (66982634415 / 1000000000000) (66982639965 / 1000000000000), orderedInterval (-28448603607 / 1000000000000) (-28448598057 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 4) <| besselDerivativeNearFromState (139777819452243 / 800000000000) 4 (IntervalRat.scale (189 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-24736249082 / 1000000000000) (-24736247716 / 1000000000000), orderedInterval (55132003024 / 1000000000000) (55132004390 / 1000000000000)))) (orderedInterval (-20127579891 / 1000000000000) (-20127576729 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate213_chunkChecks4_2 :
    compactCertificate213.chunkChecks (4 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 4) <| besselDerivativeNearFromState (386632804708521 / 4000000000000) 4 (IntervalRat.scale (189 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-4293872500 / 1000000000000) (-4293872497 / 1000000000000), orderedInterval (-81020671704 / 1000000000000) (-81020671701 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 4) <| besselDerivativeNearFromState (327752910392481 / 4000000000000) 4 (IntervalRat.scale (189 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (76046584944 / 1000000000000) (76046584945 / 1000000000000), orderedInterval (44104511139 / 1000000000000) (44104511140 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 4) <| besselDerivativeNearFromState (205092553268043 / 4000000000000) 4 (IntervalRat.scale (189 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (108744280340 / 1000000000000) (108744280832 / 1000000000000), orderedInterval (-25358305389 / 1000000000000) (-25358304898 / 1000000000000)))) (orderedInterval (-1118008255 / 1000000000000) (-1118008232 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 4) <| besselDerivativeNearFromState (110299457254581 / 4000000000000) 4 (IntervalRat.scale (189 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-12353352851 / 1000000000000) (-12353352848 / 1000000000000), orderedInterval (-151229342009 / 1000000000000) (-151229342006 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 4) <| besselDerivativeNearFromState (299484482746743 / 4000000000000) 4 (IntervalRat.scale (189 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (23404585820 / 1000000000000) (23404585821 / 1000000000000), orderedInterval (89036002235 / 1000000000000) (89036002236 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 4) <| besselDerivativeNearFromState (408920457474711 / 4000000000000) 4 (IntervalRat.scale (189 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (48274756039 / 1000000000000) (48274779240 / 1000000000000), orderedInterval (-62661163270 / 1000000000000) (-62661140069 / 1000000000000)))) (orderedInterval (-5164236178 / 1000000000000) (-5164233684 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 4) <| besselDerivativeNearFromState (172907446731957 / 4000000000000) 4 (IntervalRat.scale (189 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (3284826701 / 1000000000000) (3284826708 / 1000000000000), orderedInterval (121278143119 / 1000000000000) (121278143125 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 4) <| besselDerivativeNearFromState (702859171430997 / 4000000000000) 4 (IntervalRat.scale (189 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (32495999283 / 1000000000000) (32495999284 / 1000000000000), orderedInterval (50573547428 / 1000000000000) (50573547429 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 4) <| besselDerivativeNearFromState (469477353165723 / 4000000000000) 4 (IntervalRat.scale (189 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-69334485261 / 1000000000000) (-69334482200 / 1000000000000), orderedInterval (25130087488 / 1000000000000) (25130090549 / 1000000000000)))) (orderedInterval (-1417828512 / 1000000000000) (-1417826986 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate213_chunkChecks4 :
    compactCertificate213.chunkChecks (4 : Fin 5) 0 9 = true :=
  compactCertificate213.chunkChecks_nine_of_three (4 : Fin 5) compactCertificate213_chunkChecks4_0
    compactCertificate213_chunkChecks4_1 compactCertificate213_chunkChecks4_2

theorem compactCertificate213_chunks :
    ∀ r : Fin 5, ∀ b, compactCertificate213.chunkCheck r b = true :=
  compactCertificate213.chunkChecks_all (by
    intro r
    fin_cases r
    · exact compactCertificate213_chunkChecks0
    · exact compactCertificate213_chunkChecks1
    · exact compactCertificate213_chunkChecks2
    · exact compactCertificate213_chunkChecks3
    · exact compactCertificate213_chunkChecks4)

theorem compactCertificate213_coefficient0 :
    compactCertificate213.coefficientCheck (0 : Fin 5) = true := by
  norm_num [CompactCertificate.coefficientCheck, intervalFinSumHull,
    compactCertificate213, rationalIntervalSubset, orderedInterval, Fin.sum_univ_succ]

theorem compactCertificate213_coefficient1 :
    compactCertificate213.coefficientCheck (1 : Fin 5) = true := by
  norm_num [CompactCertificate.coefficientCheck, intervalFinSumHull,
    compactCertificate213, rationalIntervalSubset, orderedInterval, Fin.sum_univ_succ]

theorem compactCertificate213_coefficient2 :
    compactCertificate213.coefficientCheck (2 : Fin 5) = true := by
  norm_num [CompactCertificate.coefficientCheck, intervalFinSumHull,
    compactCertificate213, rationalIntervalSubset, orderedInterval, Fin.sum_univ_succ]

theorem compactCertificate213_coefficient3 :
    compactCertificate213.coefficientCheck (3 : Fin 5) = true := by
  norm_num [CompactCertificate.coefficientCheck, intervalFinSumHull,
    compactCertificate213, rationalIntervalSubset, orderedInterval, Fin.sum_univ_succ]

theorem compactCertificate213_coefficient4 :
    compactCertificate213.coefficientCheck (4 : Fin 5) = true := by
  norm_num [CompactCertificate.coefficientCheck, intervalFinSumHull,
    compactCertificate213, rationalIntervalSubset, orderedInterval, Fin.sum_univ_succ]

theorem compactCertificate213_coefficients : ∀ r : Fin 5,
    compactCertificate213.coefficientCheck r = true := by
  intro r
  fin_cases r
  · exact compactCertificate213_coefficient0
  · exact compactCertificate213_coefficient1
  · exact compactCertificate213_coefficient2
  · exact compactCertificate213_coefficient3
  · exact compactCertificate213_coefficient4

theorem compactCertificate213_lower : (1 : ℚ) ≤ compactCertificate213.output.lo := by
  norm_num [CompactCertificate.output, CompactCertificate.interval,
    CompactCertificate.coefficientTargetNat, compactCertificate213, dualConstant,
    intervalTaylorSum, intervalPow, intervalSub, intervalMaxAbs, widenInterval,
    rationalErrorInterval, orderedInterval, IntervalRat.add, IntervalRat.mul, IntervalRat.scale,
    IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4]

theorem compactCertificate213_proves {t : ℝ} (ht : t ∈ compactCertificate213.interval) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t :=
  compactCertificate213.proves compactCertificate213_states compactCertificate213_chunks
    compactCertificate213_coefficients compactCertificate213_lower ht

end Erdos232
