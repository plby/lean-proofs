/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, OpenAI Codex
-/
import ErdosProblems.Erdos232.CompactBase

open LeanCert.Core
namespace Erdos232

def compactCertificate219 : CompactCertificate where
  left := 197 / 2
  right := 99
  center := 395 / 4
  grid := fun i =>
    match i.val with
    | 0 => 31
    | 1 => 23
    | 2 => 37
    | 3 => 7
    | 4 => 18
    | 5 => 49
    | 6 => 36
    | 7 => 62
    | 8 => 46
    | 9 => 70
    | 10 => 41
    | 11 => 72
    | 12 => 67
    | 13 => 48
    | 14 => 54
    | 15 => 45
    | 16 => 40
    | 17 => 58
    | 18 => 32
    | 19 => 27
    | 20 => 17
    | 21 => 9
    | 22 => 25
    | 23 => 34
    | 24 => 14
    | 25 => 58
    | _ => 39
  point := fun i =>
    match i.val with
    | 0 => 395 / 4
    | 1 => 116382084884179 / 1600000000000
    | 2 => 37635575030707 / 320000000000
    | 3 => 33960002108153 / 1600000000000
    | 4 => 91221342531941 / 1600000000000
    | 5 => 247683690052497 / 1600000000000
    | 6 => 182442685063961 / 1600000000000
    | 7 => 312618650493053 / 1600000000000
    | 8 => 230273483025527 / 1600000000000
    | 9 => 353298740444921 / 1600000000000
    | 10 => 203977122900209 / 1600000000000
    | 11 => 361960984042981 / 1600000000000
    | 12 => 338190903636889 / 1600000000000
    | 13 => 241348986600937 / 1600000000000
    | 14 => 273664027595823 / 1600000000000
    | 15 => 228152535300287 / 1600000000000
    | 16 => 201579684110027 / 1600000000000
    | 17 => 58425649400673 / 320000000000
    | 18 => 161608421015731 / 1600000000000
    | 19 => 136997248259291 / 1600000000000
    | 20 => 85726516974473 / 1600000000000
    | 21 => 46104005942391 / 1600000000000
    | 22 => 125181344640173 / 1600000000000
    | 23 => 170924424023821 / 1600000000000
    | 24 => 72273483025527 / 1600000000000
    | 25 => 293787695994967 / 1600000000000
    | _ => 196236565608953 / 1600000000000
  state := fun i =>
    match i.val with
    | 0 => (orderedInterval (-67425099763 / 1000000000000) (-67425071799 / 1000000000000), orderedInterval (43937312986 / 1000000000000) (43937340951 / 1000000000000))
    | 1 => (orderedInterval (-89235600066 / 1000000000000) (-89235600065 / 1000000000000), orderedInterval (-27475286317 / 1000000000000) (-27475286316 / 1000000000000))
    | 2 => (orderedInterval (-61306235196 / 1000000000000) (-61306201253 / 1000000000000), orderedInterval (40935511003 / 1000000000000) (40935544947 / 1000000000000))
    | 3 => (orderedInterval (-2314846465 / 1000000000000) (-2314846456 / 1000000000000), orderedInterval (-173141327171 / 1000000000000) (-173141327162 / 1000000000000))
    | 4 => (orderedInterval (100206353237 / 1000000000000) (100206353238 / 1000000000000), orderedInterval (32654818627 / 1000000000000) (32654818628 / 1000000000000))
    | 5 => (orderedInterval (-63933089480 / 1000000000000) (-63933089331 / 1000000000000), orderedInterval (5207341772 / 1000000000000) (5207341921 / 1000000000000))
    | 6 => (orderedInterval (73958578995 / 1000000000000) (73958579266 / 1000000000000), orderedInterval (-10961708207 / 1000000000000) (-10961707936 / 1000000000000))
    | 7 => (orderedInterval (56177877503 / 1000000000000) (56177877507 / 1000000000000), orderedInterval (9970201569 / 1000000000000) (9970201574 / 1000000000000))
    | 8 => (orderedInterval (12704005439 / 1000000000000) (12704005440 / 1000000000000), orderedInterval (65240109848 / 1000000000000) (65240109849 / 1000000000000))
    | 9 => (orderedInterval (53344197840 / 1000000000000) (53344198215 / 1000000000000), orderedInterval (-6242728350 / 1000000000000) (-6242727975 / 1000000000000))
    | 10 => (orderedInterval (36039085467 / 1000000000000) (36039091577 / 1000000000000), orderedInterval (-60926696305 / 1000000000000) (-60926690195 / 1000000000000))
    | 11 => (orderedInterval (38633070837 / 1000000000000) (38633070838 / 1000000000000), orderedInterval (36268125359 / 1000000000000) (36268125360 / 1000000000000))
    | 12 => (orderedInterval (-54624599937 / 1000000000000) (-54624599656 / 1000000000000), orderedInterval (5423403012 / 1000000000000) (5423403292 / 1000000000000))
    | 13 => (orderedInterval (47993618882 / 1000000000000) (47993618883 / 1000000000000), orderedInterval (43624707065 / 1000000000000) (43624707066 / 1000000000000))
    | 14 => (orderedInterval (50079267219 / 1000000000000) (50079319727 / 1000000000000), orderedInterval (-34990506465 / 1000000000000) (-34990453957 / 1000000000000))
    | 15 => (orderedInterval (-60526733505 / 1000000000000) (-60526724221 / 1000000000000), orderedInterval (28514483203 / 1000000000000) (28514492488 / 1000000000000))
    | 16 => (orderedInterval (63607034128 / 1000000000000) (63607034129 / 1000000000000), orderedInterval (31483485754 / 1000000000000) (31483485755 / 1000000000000))
    | 17 => (orderedInterval (53957777179 / 1000000000000) (53957777180 / 1000000000000), orderedInterval (23838599984 / 1000000000000) (23838599985 / 1000000000000))
    | 18 => (orderedInterval (75548876026 / 1000000000000) (75548876027 / 1000000000000), orderedInterval (24021563266 / 1000000000000) (24021563267 / 1000000000000))
    | 19 => (orderedInterval (-86218669648 / 1000000000000) (-86218669612 / 1000000000000), orderedInterval (1660652686 / 1000000000000) (1660652722 / 1000000000000))
    | 20 => (orderedInterval (-88983535686 / 1000000000000) (-88983535685 / 1000000000000), orderedInterval (-62127058859 / 1000000000000) (-62127058858 / 1000000000000))
    | 21 => (orderedInterval (-144041041065 / 1000000000000) (-144041041064 / 1000000000000), orderedInterval (-34142926646 / 1000000000000) (-34142926645 / 1000000000000))
    | 22 => (orderedInterval (-41840216280 / 1000000000000) (-41840216279 / 1000000000000), orderedInterval (-79647697129 / 1000000000000) (-79647697128 / 1000000000000))
    | 23 => (orderedInterval (55260980561 / 1000000000000) (55260980562 / 1000000000000), orderedInterval (53644351472 / 1000000000000) (53644351473 / 1000000000000))
    | 24 => (orderedInterval (109320147895 / 1000000000000) (109320151762 / 1000000000000), orderedInterval (-47492511311 / 1000000000000) (-47492507443 / 1000000000000))
    | 25 => (orderedInterval (47961815462 / 1000000000000) (47961876530 / 1000000000000), orderedInterval (-34288471693 / 1000000000000) (-34288410626 / 1000000000000))
    | _ => (orderedInterval (-56885640973 / 1000000000000) (-56885640972 / 1000000000000), orderedInterval (-43979457805 / 1000000000000) (-43979457804 / 1000000000000))
  chunkTarget := fun r b =>
    match r.val with
    | 0 =>
      match b.val with
      | 0 => orderedInterval (-31153971645 / 1000000000000) (-31153958562 / 1000000000000)
      | 1 => orderedInterval (8228803722 / 1000000000000) (8228803745 / 1000000000000)
      | 2 => orderedInterval (-1425719767 / 1000000000000) (-1425719760 / 1000000000000)
      | 3 => orderedInterval (-1316501652 / 1000000000000) (-1316501093 / 1000000000000)
      | 4 => orderedInterval (5271126537 / 1000000000000) (5271126820 / 1000000000000)
      | 5 => orderedInterval (-2957429718 / 1000000000000) (-2957429600 / 1000000000000)
      | 6 => orderedInterval (-10096604503 / 1000000000000) (-10096604476 / 1000000000000)
      | 7 => orderedInterval (-626181223 / 1000000000000) (-626181210 / 1000000000000)
      | _ => orderedInterval (7428090968 / 1000000000000) (7428095991 / 1000000000000)
    | 1 =>
      match b.val with
      | 0 => orderedInterval (20087582015 / 1000000000000) (20087595481 / 1000000000000)
      | 1 => orderedInterval (511802324 / 1000000000000) (511802355 / 1000000000000)
      | 2 => orderedInterval (1689500791 / 1000000000000) (1689500802 / 1000000000000)
      | 3 => orderedInterval (8463827497 / 1000000000000) (8463828313 / 1000000000000)
      | 4 => orderedInterval (6398593087 / 1000000000000) (6398593579 / 1000000000000)
      | 5 => orderedInterval (-694658045 / 1000000000000) (-694657876 / 1000000000000)
      | 6 => orderedInterval (-5107471040 / 1000000000000) (-5107471015 / 1000000000000)
      | 7 => orderedInterval (-2831950111 / 1000000000000) (-2831950099 / 1000000000000)
      | _ => orderedInterval (15307580659 / 1000000000000) (15307589952 / 1000000000000)
    | 2 =>
      match b.val with
      | 0 => orderedInterval (32075674075 / 1000000000000) (32075688130 / 1000000000000)
      | 1 => orderedInterval (-12394870677 / 1000000000000) (-12394870631 / 1000000000000)
      | 2 => orderedInterval (6114194663 / 1000000000000) (6114194682 / 1000000000000)
      | 3 => orderedInterval (14034437062 / 1000000000000) (14034438332 / 1000000000000)
      | 4 => orderedInterval (-14412172023 / 1000000000000) (-14412171165 / 1000000000000)
      | 5 => orderedInterval (2666619949 / 1000000000000) (2666620195 / 1000000000000)
      | 6 => orderedInterval (9873446265 / 1000000000000) (9873446289 / 1000000000000)
      | 7 => orderedInterval (4162715224 / 1000000000000) (4162715235 / 1000000000000)
      | _ => orderedInterval (-3258772984 / 1000000000000) (-3258755641 / 1000000000000)
    | 3 =>
      match b.val with
      | 0 => orderedInterval (-21693863196 / 1000000000000) (-21693848597 / 1000000000000)
      | 1 => orderedInterval (1303540829 / 1000000000000) (1303540898 / 1000000000000)
      | 2 => orderedInterval (-2560793651 / 1000000000000) (-2560793618 / 1000000000000)
      | 3 => orderedInterval (-64817670593 / 1000000000000) (-64817668480 / 1000000000000)
      | 4 => orderedInterval (-14516763124 / 1000000000000) (-14516761630 / 1000000000000)
      | 5 => orderedInterval (-1134748156 / 1000000000000) (-1134747799 / 1000000000000)
      | 6 => orderedInterval (4393894969 / 1000000000000) (4393894993 / 1000000000000)
      | 7 => orderedInterval (4248153839 / 1000000000000) (4248153851 / 1000000000000)
      | _ => orderedInterval (-33691010303 / 1000000000000) (-33690978083 / 1000000000000)
    | _ =>
      match b.val with
      | 0 => orderedInterval (-33765602287 / 1000000000000) (-33765586894 / 1000000000000)
      | 1 => orderedInterval (27825804428 / 1000000000000) (27825804536 / 1000000000000)
      | 2 => orderedInterval (-25118536213 / 1000000000000) (-25118536152 / 1000000000000)
      | 3 => orderedInterval (-76967573981 / 1000000000000) (-76967570172 / 1000000000000)
      | 4 => orderedInterval (43420259664 / 1000000000000) (43420262285 / 1000000000000)
      | 5 => orderedInterval (3484840292 / 1000000000000) (3484840816 / 1000000000000)
      | 6 => orderedInterval (-10802342096 / 1000000000000) (-10802342073 / 1000000000000)
      | 7 => orderedInterval (-5492674864 / 1000000000000) (-5492674852 / 1000000000000)
      | _ => orderedInterval (-20561624665 / 1000000000000) (-20561564457 / 1000000000000)
  coefficientTarget := fun i =>
    match i.val with
    | 0 => orderedInterval (-26648387281 / 1000000000000) (-26648368145 / 1000000000000)
    | 1 => orderedInterval (43824807177 / 1000000000000) (43824831492 / 1000000000000)
    | 2 => orderedInterval (38861271554 / 1000000000000) (38861305426 / 1000000000000)
    | 3 => orderedInterval (-128469259386 / 1000000000000) (-128469208465 / 1000000000000)
    | _ => orderedInterval (-97977449722 / 1000000000000) (-97977366963 / 1000000000000)

theorem compactCertificate219_stateChecks0 :
    compactCertificate219.stateChecks 0 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 31 12 (395 / 4)) (orderedInterval (-67425099763 / 1000000000000) (-67425071799 / 1000000000000), orderedInterval (43937312986 / 1000000000000) (43937340951 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 23 12 (116382084884179 / 1600000000000)) (orderedInterval (-89235600066 / 1000000000000) (-89235600065 / 1000000000000), orderedInterval (-27475286317 / 1000000000000) (-27475286316 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 37 12 (37635575030707 / 320000000000)) (orderedInterval (-61306235196 / 1000000000000) (-61306201253 / 1000000000000), orderedInterval (40935511003 / 1000000000000) (40935544947 / 1000000000000))) = true
  norm_num [besselStateAtRationalPoint, besselIntervalStepZero,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, besselZeroTransition,
    besselInitial, besselGridStateAt, besselGridStateBlock00, besselGridStateBlock01,
    besselGridStateBlock02, besselGridStateBlock03, besselGridStateBlock04,
    besselGridStateBlock05, besselGridStateBlock06, besselGridStateBlock07,
    besselGridStateBlock08, besselGridStateBlock09, besselGridStateBlock10,
    besselGridStateBlock11, besselGridStateBlock12, besselGridStateBlock13,
    besselGridStateBlock14, besselGridState007, besselGridState009, besselGridState014, besselGridState017, besselGridState018, besselGridState023, besselGridState025, besselGridState027, besselGridState031, besselGridState032, besselGridState034, besselGridState036, besselGridState037, besselGridState039, besselGridState040, besselGridState041, besselGridState045, besselGridState046, besselGridState048, besselGridState049, besselGridState054, besselGridState058, besselGridState062, besselGridState067, besselGridState070, besselGridState072, besselStateSubset, linearInterval, widenInterval,
    rationalErrorInterval, rationalIntervalSubset, orderedInterval, Finset.sum_range_succ,
    IntervalRat.add, IntervalRat.mul, IntervalRat.scale, IntervalRat.singleton]

theorem compactCertificate219_stateChecks1 :
    compactCertificate219.stateChecks 3 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 7 12 (33960002108153 / 1600000000000)) (orderedInterval (-2314846465 / 1000000000000) (-2314846456 / 1000000000000), orderedInterval (-173141327171 / 1000000000000) (-173141327162 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 18 12 (91221342531941 / 1600000000000)) (orderedInterval (100206353237 / 1000000000000) (100206353238 / 1000000000000), orderedInterval (32654818627 / 1000000000000) (32654818628 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 49 12 (247683690052497 / 1600000000000)) (orderedInterval (-63933089480 / 1000000000000) (-63933089331 / 1000000000000), orderedInterval (5207341772 / 1000000000000) (5207341921 / 1000000000000))) = true
  norm_num [besselStateAtRationalPoint, besselIntervalStepZero,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, besselZeroTransition,
    besselInitial, besselGridStateAt, besselGridStateBlock00, besselGridStateBlock01,
    besselGridStateBlock02, besselGridStateBlock03, besselGridStateBlock04,
    besselGridStateBlock05, besselGridStateBlock06, besselGridStateBlock07,
    besselGridStateBlock08, besselGridStateBlock09, besselGridStateBlock10,
    besselGridStateBlock11, besselGridStateBlock12, besselGridStateBlock13,
    besselGridStateBlock14, besselGridState007, besselGridState009, besselGridState014, besselGridState017, besselGridState018, besselGridState023, besselGridState025, besselGridState027, besselGridState031, besselGridState032, besselGridState034, besselGridState036, besselGridState037, besselGridState039, besselGridState040, besselGridState041, besselGridState045, besselGridState046, besselGridState048, besselGridState049, besselGridState054, besselGridState058, besselGridState062, besselGridState067, besselGridState070, besselGridState072, besselStateSubset, linearInterval, widenInterval,
    rationalErrorInterval, rationalIntervalSubset, orderedInterval, Finset.sum_range_succ,
    IntervalRat.add, IntervalRat.mul, IntervalRat.scale, IntervalRat.singleton]

theorem compactCertificate219_stateChecks2 :
    compactCertificate219.stateChecks 6 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 36 12 (182442685063961 / 1600000000000)) (orderedInterval (73958578995 / 1000000000000) (73958579266 / 1000000000000), orderedInterval (-10961708207 / 1000000000000) (-10961707936 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 62 12 (312618650493053 / 1600000000000)) (orderedInterval (56177877503 / 1000000000000) (56177877507 / 1000000000000), orderedInterval (9970201569 / 1000000000000) (9970201574 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 46 12 (230273483025527 / 1600000000000)) (orderedInterval (12704005439 / 1000000000000) (12704005440 / 1000000000000), orderedInterval (65240109848 / 1000000000000) (65240109849 / 1000000000000))) = true
  norm_num [besselStateAtRationalPoint, besselIntervalStepZero,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, besselZeroTransition,
    besselInitial, besselGridStateAt, besselGridStateBlock00, besselGridStateBlock01,
    besselGridStateBlock02, besselGridStateBlock03, besselGridStateBlock04,
    besselGridStateBlock05, besselGridStateBlock06, besselGridStateBlock07,
    besselGridStateBlock08, besselGridStateBlock09, besselGridStateBlock10,
    besselGridStateBlock11, besselGridStateBlock12, besselGridStateBlock13,
    besselGridStateBlock14, besselGridState007, besselGridState009, besselGridState014, besselGridState017, besselGridState018, besselGridState023, besselGridState025, besselGridState027, besselGridState031, besselGridState032, besselGridState034, besselGridState036, besselGridState037, besselGridState039, besselGridState040, besselGridState041, besselGridState045, besselGridState046, besselGridState048, besselGridState049, besselGridState054, besselGridState058, besselGridState062, besselGridState067, besselGridState070, besselGridState072, besselStateSubset, linearInterval, widenInterval,
    rationalErrorInterval, rationalIntervalSubset, orderedInterval, Finset.sum_range_succ,
    IntervalRat.add, IntervalRat.mul, IntervalRat.scale, IntervalRat.singleton]

theorem compactCertificate219_stateChecks3 :
    compactCertificate219.stateChecks 9 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 70 12 (353298740444921 / 1600000000000)) (orderedInterval (53344197840 / 1000000000000) (53344198215 / 1000000000000), orderedInterval (-6242728350 / 1000000000000) (-6242727975 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 41 12 (203977122900209 / 1600000000000)) (orderedInterval (36039085467 / 1000000000000) (36039091577 / 1000000000000), orderedInterval (-60926696305 / 1000000000000) (-60926690195 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 72 12 (361960984042981 / 1600000000000)) (orderedInterval (38633070837 / 1000000000000) (38633070838 / 1000000000000), orderedInterval (36268125359 / 1000000000000) (36268125360 / 1000000000000))) = true
  norm_num [besselStateAtRationalPoint, besselIntervalStepZero,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, besselZeroTransition,
    besselInitial, besselGridStateAt, besselGridStateBlock00, besselGridStateBlock01,
    besselGridStateBlock02, besselGridStateBlock03, besselGridStateBlock04,
    besselGridStateBlock05, besselGridStateBlock06, besselGridStateBlock07,
    besselGridStateBlock08, besselGridStateBlock09, besselGridStateBlock10,
    besselGridStateBlock11, besselGridStateBlock12, besselGridStateBlock13,
    besselGridStateBlock14, besselGridState007, besselGridState009, besselGridState014, besselGridState017, besselGridState018, besselGridState023, besselGridState025, besselGridState027, besselGridState031, besselGridState032, besselGridState034, besselGridState036, besselGridState037, besselGridState039, besselGridState040, besselGridState041, besselGridState045, besselGridState046, besselGridState048, besselGridState049, besselGridState054, besselGridState058, besselGridState062, besselGridState067, besselGridState070, besselGridState072, besselStateSubset, linearInterval, widenInterval,
    rationalErrorInterval, rationalIntervalSubset, orderedInterval, Finset.sum_range_succ,
    IntervalRat.add, IntervalRat.mul, IntervalRat.scale, IntervalRat.singleton]

theorem compactCertificate219_stateChecks4 :
    compactCertificate219.stateChecks 12 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 67 12 (338190903636889 / 1600000000000)) (orderedInterval (-54624599937 / 1000000000000) (-54624599656 / 1000000000000), orderedInterval (5423403012 / 1000000000000) (5423403292 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 48 12 (241348986600937 / 1600000000000)) (orderedInterval (47993618882 / 1000000000000) (47993618883 / 1000000000000), orderedInterval (43624707065 / 1000000000000) (43624707066 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 54 12 (273664027595823 / 1600000000000)) (orderedInterval (50079267219 / 1000000000000) (50079319727 / 1000000000000), orderedInterval (-34990506465 / 1000000000000) (-34990453957 / 1000000000000))) = true
  norm_num [besselStateAtRationalPoint, besselIntervalStepZero,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, besselZeroTransition,
    besselInitial, besselGridStateAt, besselGridStateBlock00, besselGridStateBlock01,
    besselGridStateBlock02, besselGridStateBlock03, besselGridStateBlock04,
    besselGridStateBlock05, besselGridStateBlock06, besselGridStateBlock07,
    besselGridStateBlock08, besselGridStateBlock09, besselGridStateBlock10,
    besselGridStateBlock11, besselGridStateBlock12, besselGridStateBlock13,
    besselGridStateBlock14, besselGridState007, besselGridState009, besselGridState014, besselGridState017, besselGridState018, besselGridState023, besselGridState025, besselGridState027, besselGridState031, besselGridState032, besselGridState034, besselGridState036, besselGridState037, besselGridState039, besselGridState040, besselGridState041, besselGridState045, besselGridState046, besselGridState048, besselGridState049, besselGridState054, besselGridState058, besselGridState062, besselGridState067, besselGridState070, besselGridState072, besselStateSubset, linearInterval, widenInterval,
    rationalErrorInterval, rationalIntervalSubset, orderedInterval, Finset.sum_range_succ,
    IntervalRat.add, IntervalRat.mul, IntervalRat.scale, IntervalRat.singleton]

theorem compactCertificate219_stateChecks5 :
    compactCertificate219.stateChecks 15 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 45 12 (228152535300287 / 1600000000000)) (orderedInterval (-60526733505 / 1000000000000) (-60526724221 / 1000000000000), orderedInterval (28514483203 / 1000000000000) (28514492488 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 40 12 (201579684110027 / 1600000000000)) (orderedInterval (63607034128 / 1000000000000) (63607034129 / 1000000000000), orderedInterval (31483485754 / 1000000000000) (31483485755 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 58 12 (58425649400673 / 320000000000)) (orderedInterval (53957777179 / 1000000000000) (53957777180 / 1000000000000), orderedInterval (23838599984 / 1000000000000) (23838599985 / 1000000000000))) = true
  norm_num [besselStateAtRationalPoint, besselIntervalStepZero,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, besselZeroTransition,
    besselInitial, besselGridStateAt, besselGridStateBlock00, besselGridStateBlock01,
    besselGridStateBlock02, besselGridStateBlock03, besselGridStateBlock04,
    besselGridStateBlock05, besselGridStateBlock06, besselGridStateBlock07,
    besselGridStateBlock08, besselGridStateBlock09, besselGridStateBlock10,
    besselGridStateBlock11, besselGridStateBlock12, besselGridStateBlock13,
    besselGridStateBlock14, besselGridState007, besselGridState009, besselGridState014, besselGridState017, besselGridState018, besselGridState023, besselGridState025, besselGridState027, besselGridState031, besselGridState032, besselGridState034, besselGridState036, besselGridState037, besselGridState039, besselGridState040, besselGridState041, besselGridState045, besselGridState046, besselGridState048, besselGridState049, besselGridState054, besselGridState058, besselGridState062, besselGridState067, besselGridState070, besselGridState072, besselStateSubset, linearInterval, widenInterval,
    rationalErrorInterval, rationalIntervalSubset, orderedInterval, Finset.sum_range_succ,
    IntervalRat.add, IntervalRat.mul, IntervalRat.scale, IntervalRat.singleton]

theorem compactCertificate219_stateChecks6 :
    compactCertificate219.stateChecks 18 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 32 12 (161608421015731 / 1600000000000)) (orderedInterval (75548876026 / 1000000000000) (75548876027 / 1000000000000), orderedInterval (24021563266 / 1000000000000) (24021563267 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 27 12 (136997248259291 / 1600000000000)) (orderedInterval (-86218669648 / 1000000000000) (-86218669612 / 1000000000000), orderedInterval (1660652686 / 1000000000000) (1660652722 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 17 12 (85726516974473 / 1600000000000)) (orderedInterval (-88983535686 / 1000000000000) (-88983535685 / 1000000000000), orderedInterval (-62127058859 / 1000000000000) (-62127058858 / 1000000000000))) = true
  norm_num [besselStateAtRationalPoint, besselIntervalStepZero,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, besselZeroTransition,
    besselInitial, besselGridStateAt, besselGridStateBlock00, besselGridStateBlock01,
    besselGridStateBlock02, besselGridStateBlock03, besselGridStateBlock04,
    besselGridStateBlock05, besselGridStateBlock06, besselGridStateBlock07,
    besselGridStateBlock08, besselGridStateBlock09, besselGridStateBlock10,
    besselGridStateBlock11, besselGridStateBlock12, besselGridStateBlock13,
    besselGridStateBlock14, besselGridState007, besselGridState009, besselGridState014, besselGridState017, besselGridState018, besselGridState023, besselGridState025, besselGridState027, besselGridState031, besselGridState032, besselGridState034, besselGridState036, besselGridState037, besselGridState039, besselGridState040, besselGridState041, besselGridState045, besselGridState046, besselGridState048, besselGridState049, besselGridState054, besselGridState058, besselGridState062, besselGridState067, besselGridState070, besselGridState072, besselStateSubset, linearInterval, widenInterval,
    rationalErrorInterval, rationalIntervalSubset, orderedInterval, Finset.sum_range_succ,
    IntervalRat.add, IntervalRat.mul, IntervalRat.scale, IntervalRat.singleton]

theorem compactCertificate219_stateChecks7 :
    compactCertificate219.stateChecks 21 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 9 12 (46104005942391 / 1600000000000)) (orderedInterval (-144041041065 / 1000000000000) (-144041041064 / 1000000000000), orderedInterval (-34142926646 / 1000000000000) (-34142926645 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 25 12 (125181344640173 / 1600000000000)) (orderedInterval (-41840216280 / 1000000000000) (-41840216279 / 1000000000000), orderedInterval (-79647697129 / 1000000000000) (-79647697128 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 34 12 (170924424023821 / 1600000000000)) (orderedInterval (55260980561 / 1000000000000) (55260980562 / 1000000000000), orderedInterval (53644351472 / 1000000000000) (53644351473 / 1000000000000))) = true
  norm_num [besselStateAtRationalPoint, besselIntervalStepZero,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, besselZeroTransition,
    besselInitial, besselGridStateAt, besselGridStateBlock00, besselGridStateBlock01,
    besselGridStateBlock02, besselGridStateBlock03, besselGridStateBlock04,
    besselGridStateBlock05, besselGridStateBlock06, besselGridStateBlock07,
    besselGridStateBlock08, besselGridStateBlock09, besselGridStateBlock10,
    besselGridStateBlock11, besselGridStateBlock12, besselGridStateBlock13,
    besselGridStateBlock14, besselGridState007, besselGridState009, besselGridState014, besselGridState017, besselGridState018, besselGridState023, besselGridState025, besselGridState027, besselGridState031, besselGridState032, besselGridState034, besselGridState036, besselGridState037, besselGridState039, besselGridState040, besselGridState041, besselGridState045, besselGridState046, besselGridState048, besselGridState049, besselGridState054, besselGridState058, besselGridState062, besselGridState067, besselGridState070, besselGridState072, besselStateSubset, linearInterval, widenInterval,
    rationalErrorInterval, rationalIntervalSubset, orderedInterval, Finset.sum_range_succ,
    IntervalRat.add, IntervalRat.mul, IntervalRat.scale, IntervalRat.singleton]

theorem compactCertificate219_stateChecks8 :
    compactCertificate219.stateChecks 24 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 14 12 (72273483025527 / 1600000000000)) (orderedInterval (109320147895 / 1000000000000) (109320151762 / 1000000000000), orderedInterval (-47492511311 / 1000000000000) (-47492507443 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 58 12 (293787695994967 / 1600000000000)) (orderedInterval (47961815462 / 1000000000000) (47961876530 / 1000000000000), orderedInterval (-34288471693 / 1000000000000) (-34288410626 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 39 12 (196236565608953 / 1600000000000)) (orderedInterval (-56885640973 / 1000000000000) (-56885640972 / 1000000000000), orderedInterval (-43979457805 / 1000000000000) (-43979457804 / 1000000000000))) = true
  norm_num [besselStateAtRationalPoint, besselIntervalStepZero,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, besselZeroTransition,
    besselInitial, besselGridStateAt, besselGridStateBlock00, besselGridStateBlock01,
    besselGridStateBlock02, besselGridStateBlock03, besselGridStateBlock04,
    besselGridStateBlock05, besselGridStateBlock06, besselGridStateBlock07,
    besselGridStateBlock08, besselGridStateBlock09, besselGridStateBlock10,
    besselGridStateBlock11, besselGridStateBlock12, besselGridStateBlock13,
    besselGridStateBlock14, besselGridState007, besselGridState009, besselGridState014, besselGridState017, besselGridState018, besselGridState023, besselGridState025, besselGridState027, besselGridState031, besselGridState032, besselGridState034, besselGridState036, besselGridState037, besselGridState039, besselGridState040, besselGridState041, besselGridState045, besselGridState046, besselGridState048, besselGridState049, besselGridState054, besselGridState058, besselGridState062, besselGridState067, besselGridState070, besselGridState072, besselStateSubset, linearInterval, widenInterval,
    rationalErrorInterval, rationalIntervalSubset, orderedInterval, Finset.sum_range_succ,
    IntervalRat.add, IntervalRat.mul, IntervalRat.scale, IntervalRat.singleton]

theorem compactCertificate219_states : ∀ j,
    BesselStateValid (compactCertificate219.point j) (compactCertificate219.state j) :=
  compactCertificate219.statesValid_of_checks3 compactCertificate219_stateChecks0
    compactCertificate219_stateChecks1 compactCertificate219_stateChecks2
    compactCertificate219_stateChecks3 compactCertificate219_stateChecks4
    compactCertificate219_stateChecks5 compactCertificate219_stateChecks6
    compactCertificate219_stateChecks7 compactCertificate219_stateChecks8

theorem compactCertificate219_chunkChecks0_0 :
    compactCertificate219.chunkChecks (0 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 0) <| besselDerivativeNearFromState (395 / 4) 0 (IntervalRat.scale (395 / 4) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-67425099763 / 1000000000000) (-67425071799 / 1000000000000), orderedInterval (43937312986 / 1000000000000) (43937340951 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 0) <| besselDerivativeNearFromState (116382084884179 / 1600000000000) 0 (IntervalRat.scale (395 / 4) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-89235600066 / 1000000000000) (-89235600065 / 1000000000000), orderedInterval (-27475286317 / 1000000000000) (-27475286316 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 0) <| besselDerivativeNearFromState (37635575030707 / 320000000000) 0 (IntervalRat.scale (395 / 4) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-61306235196 / 1000000000000) (-61306201253 / 1000000000000), orderedInterval (40935511003 / 1000000000000) (40935544947 / 1000000000000)))) (orderedInterval (-31153971645 / 1000000000000) (-31153958562 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 0) <| besselDerivativeNearFromState (33960002108153 / 1600000000000) 0 (IntervalRat.scale (395 / 4) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-2314846465 / 1000000000000) (-2314846456 / 1000000000000), orderedInterval (-173141327171 / 1000000000000) (-173141327162 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 0) <| besselDerivativeNearFromState (91221342531941 / 1600000000000) 0 (IntervalRat.scale (395 / 4) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (100206353237 / 1000000000000) (100206353238 / 1000000000000), orderedInterval (32654818627 / 1000000000000) (32654818628 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 0) <| besselDerivativeNearFromState (247683690052497 / 1600000000000) 0 (IntervalRat.scale (395 / 4) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-63933089480 / 1000000000000) (-63933089331 / 1000000000000), orderedInterval (5207341772 / 1000000000000) (5207341921 / 1000000000000)))) (orderedInterval (8228803722 / 1000000000000) (8228803745 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 0) <| besselDerivativeNearFromState (182442685063961 / 1600000000000) 0 (IntervalRat.scale (395 / 4) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (73958578995 / 1000000000000) (73958579266 / 1000000000000), orderedInterval (-10961708207 / 1000000000000) (-10961707936 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 0) <| besselDerivativeNearFromState (312618650493053 / 1600000000000) 0 (IntervalRat.scale (395 / 4) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (56177877503 / 1000000000000) (56177877507 / 1000000000000), orderedInterval (9970201569 / 1000000000000) (9970201574 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 0) <| besselDerivativeNearFromState (230273483025527 / 1600000000000) 0 (IntervalRat.scale (395 / 4) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (12704005439 / 1000000000000) (12704005440 / 1000000000000), orderedInterval (65240109848 / 1000000000000) (65240109849 / 1000000000000)))) (orderedInterval (-1425719767 / 1000000000000) (-1425719760 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate219_chunkChecks0_1 :
    compactCertificate219.chunkChecks (0 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 0) <| besselDerivativeNearFromState (353298740444921 / 1600000000000) 0 (IntervalRat.scale (395 / 4) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (53344197840 / 1000000000000) (53344198215 / 1000000000000), orderedInterval (-6242728350 / 1000000000000) (-6242727975 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 0) <| besselDerivativeNearFromState (203977122900209 / 1600000000000) 0 (IntervalRat.scale (395 / 4) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (36039085467 / 1000000000000) (36039091577 / 1000000000000), orderedInterval (-60926696305 / 1000000000000) (-60926690195 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 0) <| besselDerivativeNearFromState (361960984042981 / 1600000000000) 0 (IntervalRat.scale (395 / 4) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (38633070837 / 1000000000000) (38633070838 / 1000000000000), orderedInterval (36268125359 / 1000000000000) (36268125360 / 1000000000000)))) (orderedInterval (-1316501652 / 1000000000000) (-1316501093 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 0) <| besselDerivativeNearFromState (338190903636889 / 1600000000000) 0 (IntervalRat.scale (395 / 4) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-54624599937 / 1000000000000) (-54624599656 / 1000000000000), orderedInterval (5423403012 / 1000000000000) (5423403292 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 0) <| besselDerivativeNearFromState (241348986600937 / 1600000000000) 0 (IntervalRat.scale (395 / 4) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (47993618882 / 1000000000000) (47993618883 / 1000000000000), orderedInterval (43624707065 / 1000000000000) (43624707066 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 0) <| besselDerivativeNearFromState (273664027595823 / 1600000000000) 0 (IntervalRat.scale (395 / 4) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (50079267219 / 1000000000000) (50079319727 / 1000000000000), orderedInterval (-34990506465 / 1000000000000) (-34990453957 / 1000000000000)))) (orderedInterval (5271126537 / 1000000000000) (5271126820 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 0) <| besselDerivativeNearFromState (228152535300287 / 1600000000000) 0 (IntervalRat.scale (395 / 4) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-60526733505 / 1000000000000) (-60526724221 / 1000000000000), orderedInterval (28514483203 / 1000000000000) (28514492488 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 0) <| besselDerivativeNearFromState (201579684110027 / 1600000000000) 0 (IntervalRat.scale (395 / 4) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (63607034128 / 1000000000000) (63607034129 / 1000000000000), orderedInterval (31483485754 / 1000000000000) (31483485755 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 0) <| besselDerivativeNearFromState (58425649400673 / 320000000000) 0 (IntervalRat.scale (395 / 4) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (53957777179 / 1000000000000) (53957777180 / 1000000000000), orderedInterval (23838599984 / 1000000000000) (23838599985 / 1000000000000)))) (orderedInterval (-2957429718 / 1000000000000) (-2957429600 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate219_chunkChecks0_2 :
    compactCertificate219.chunkChecks (0 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 0) <| besselDerivativeNearFromState (161608421015731 / 1600000000000) 0 (IntervalRat.scale (395 / 4) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (75548876026 / 1000000000000) (75548876027 / 1000000000000), orderedInterval (24021563266 / 1000000000000) (24021563267 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 0) <| besselDerivativeNearFromState (136997248259291 / 1600000000000) 0 (IntervalRat.scale (395 / 4) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-86218669648 / 1000000000000) (-86218669612 / 1000000000000), orderedInterval (1660652686 / 1000000000000) (1660652722 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 0) <| besselDerivativeNearFromState (85726516974473 / 1600000000000) 0 (IntervalRat.scale (395 / 4) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-88983535686 / 1000000000000) (-88983535685 / 1000000000000), orderedInterval (-62127058859 / 1000000000000) (-62127058858 / 1000000000000)))) (orderedInterval (-10096604503 / 1000000000000) (-10096604476 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 0) <| besselDerivativeNearFromState (46104005942391 / 1600000000000) 0 (IntervalRat.scale (395 / 4) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-144041041065 / 1000000000000) (-144041041064 / 1000000000000), orderedInterval (-34142926646 / 1000000000000) (-34142926645 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 0) <| besselDerivativeNearFromState (125181344640173 / 1600000000000) 0 (IntervalRat.scale (395 / 4) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-41840216280 / 1000000000000) (-41840216279 / 1000000000000), orderedInterval (-79647697129 / 1000000000000) (-79647697128 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 0) <| besselDerivativeNearFromState (170924424023821 / 1600000000000) 0 (IntervalRat.scale (395 / 4) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (55260980561 / 1000000000000) (55260980562 / 1000000000000), orderedInterval (53644351472 / 1000000000000) (53644351473 / 1000000000000)))) (orderedInterval (-626181223 / 1000000000000) (-626181210 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 0) <| besselDerivativeNearFromState (72273483025527 / 1600000000000) 0 (IntervalRat.scale (395 / 4) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (109320147895 / 1000000000000) (109320151762 / 1000000000000), orderedInterval (-47492511311 / 1000000000000) (-47492507443 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 0) <| besselDerivativeNearFromState (293787695994967 / 1600000000000) 0 (IntervalRat.scale (395 / 4) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (47961815462 / 1000000000000) (47961876530 / 1000000000000), orderedInterval (-34288471693 / 1000000000000) (-34288410626 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 0) <| besselDerivativeNearFromState (196236565608953 / 1600000000000) 0 (IntervalRat.scale (395 / 4) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-56885640973 / 1000000000000) (-56885640972 / 1000000000000), orderedInterval (-43979457805 / 1000000000000) (-43979457804 / 1000000000000)))) (orderedInterval (7428090968 / 1000000000000) (7428095991 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate219_chunkChecks0 :
    compactCertificate219.chunkChecks (0 : Fin 5) 0 9 = true :=
  compactCertificate219.chunkChecks_nine_of_three (0 : Fin 5) compactCertificate219_chunkChecks0_0
    compactCertificate219_chunkChecks0_1 compactCertificate219_chunkChecks0_2

theorem compactCertificate219_chunkChecks1_0 :
    compactCertificate219.chunkChecks (1 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 1) <| besselDerivativeNearFromState (395 / 4) 1 (IntervalRat.scale (395 / 4) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-67425099763 / 1000000000000) (-67425071799 / 1000000000000), orderedInterval (43937312986 / 1000000000000) (43937340951 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 1) <| besselDerivativeNearFromState (116382084884179 / 1600000000000) 1 (IntervalRat.scale (395 / 4) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-89235600066 / 1000000000000) (-89235600065 / 1000000000000), orderedInterval (-27475286317 / 1000000000000) (-27475286316 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 1) <| besselDerivativeNearFromState (37635575030707 / 320000000000) 1 (IntervalRat.scale (395 / 4) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-61306235196 / 1000000000000) (-61306201253 / 1000000000000), orderedInterval (40935511003 / 1000000000000) (40935544947 / 1000000000000)))) (orderedInterval (20087582015 / 1000000000000) (20087595481 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 1) <| besselDerivativeNearFromState (33960002108153 / 1600000000000) 1 (IntervalRat.scale (395 / 4) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-2314846465 / 1000000000000) (-2314846456 / 1000000000000), orderedInterval (-173141327171 / 1000000000000) (-173141327162 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 1) <| besselDerivativeNearFromState (91221342531941 / 1600000000000) 1 (IntervalRat.scale (395 / 4) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (100206353237 / 1000000000000) (100206353238 / 1000000000000), orderedInterval (32654818627 / 1000000000000) (32654818628 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 1) <| besselDerivativeNearFromState (247683690052497 / 1600000000000) 1 (IntervalRat.scale (395 / 4) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-63933089480 / 1000000000000) (-63933089331 / 1000000000000), orderedInterval (5207341772 / 1000000000000) (5207341921 / 1000000000000)))) (orderedInterval (511802324 / 1000000000000) (511802355 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 1) <| besselDerivativeNearFromState (182442685063961 / 1600000000000) 1 (IntervalRat.scale (395 / 4) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (73958578995 / 1000000000000) (73958579266 / 1000000000000), orderedInterval (-10961708207 / 1000000000000) (-10961707936 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 1) <| besselDerivativeNearFromState (312618650493053 / 1600000000000) 1 (IntervalRat.scale (395 / 4) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (56177877503 / 1000000000000) (56177877507 / 1000000000000), orderedInterval (9970201569 / 1000000000000) (9970201574 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 1) <| besselDerivativeNearFromState (230273483025527 / 1600000000000) 1 (IntervalRat.scale (395 / 4) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (12704005439 / 1000000000000) (12704005440 / 1000000000000), orderedInterval (65240109848 / 1000000000000) (65240109849 / 1000000000000)))) (orderedInterval (1689500791 / 1000000000000) (1689500802 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate219_chunkChecks1_1 :
    compactCertificate219.chunkChecks (1 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 1) <| besselDerivativeNearFromState (353298740444921 / 1600000000000) 1 (IntervalRat.scale (395 / 4) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (53344197840 / 1000000000000) (53344198215 / 1000000000000), orderedInterval (-6242728350 / 1000000000000) (-6242727975 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 1) <| besselDerivativeNearFromState (203977122900209 / 1600000000000) 1 (IntervalRat.scale (395 / 4) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (36039085467 / 1000000000000) (36039091577 / 1000000000000), orderedInterval (-60926696305 / 1000000000000) (-60926690195 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 1) <| besselDerivativeNearFromState (361960984042981 / 1600000000000) 1 (IntervalRat.scale (395 / 4) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (38633070837 / 1000000000000) (38633070838 / 1000000000000), orderedInterval (36268125359 / 1000000000000) (36268125360 / 1000000000000)))) (orderedInterval (8463827497 / 1000000000000) (8463828313 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 1) <| besselDerivativeNearFromState (338190903636889 / 1600000000000) 1 (IntervalRat.scale (395 / 4) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-54624599937 / 1000000000000) (-54624599656 / 1000000000000), orderedInterval (5423403012 / 1000000000000) (5423403292 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 1) <| besselDerivativeNearFromState (241348986600937 / 1600000000000) 1 (IntervalRat.scale (395 / 4) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (47993618882 / 1000000000000) (47993618883 / 1000000000000), orderedInterval (43624707065 / 1000000000000) (43624707066 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 1) <| besselDerivativeNearFromState (273664027595823 / 1600000000000) 1 (IntervalRat.scale (395 / 4) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (50079267219 / 1000000000000) (50079319727 / 1000000000000), orderedInterval (-34990506465 / 1000000000000) (-34990453957 / 1000000000000)))) (orderedInterval (6398593087 / 1000000000000) (6398593579 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 1) <| besselDerivativeNearFromState (228152535300287 / 1600000000000) 1 (IntervalRat.scale (395 / 4) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-60526733505 / 1000000000000) (-60526724221 / 1000000000000), orderedInterval (28514483203 / 1000000000000) (28514492488 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 1) <| besselDerivativeNearFromState (201579684110027 / 1600000000000) 1 (IntervalRat.scale (395 / 4) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (63607034128 / 1000000000000) (63607034129 / 1000000000000), orderedInterval (31483485754 / 1000000000000) (31483485755 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 1) <| besselDerivativeNearFromState (58425649400673 / 320000000000) 1 (IntervalRat.scale (395 / 4) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (53957777179 / 1000000000000) (53957777180 / 1000000000000), orderedInterval (23838599984 / 1000000000000) (23838599985 / 1000000000000)))) (orderedInterval (-694658045 / 1000000000000) (-694657876 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate219_chunkChecks1_2 :
    compactCertificate219.chunkChecks (1 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 1) <| besselDerivativeNearFromState (161608421015731 / 1600000000000) 1 (IntervalRat.scale (395 / 4) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (75548876026 / 1000000000000) (75548876027 / 1000000000000), orderedInterval (24021563266 / 1000000000000) (24021563267 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 1) <| besselDerivativeNearFromState (136997248259291 / 1600000000000) 1 (IntervalRat.scale (395 / 4) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-86218669648 / 1000000000000) (-86218669612 / 1000000000000), orderedInterval (1660652686 / 1000000000000) (1660652722 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 1) <| besselDerivativeNearFromState (85726516974473 / 1600000000000) 1 (IntervalRat.scale (395 / 4) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-88983535686 / 1000000000000) (-88983535685 / 1000000000000), orderedInterval (-62127058859 / 1000000000000) (-62127058858 / 1000000000000)))) (orderedInterval (-5107471040 / 1000000000000) (-5107471015 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 1) <| besselDerivativeNearFromState (46104005942391 / 1600000000000) 1 (IntervalRat.scale (395 / 4) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-144041041065 / 1000000000000) (-144041041064 / 1000000000000), orderedInterval (-34142926646 / 1000000000000) (-34142926645 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 1) <| besselDerivativeNearFromState (125181344640173 / 1600000000000) 1 (IntervalRat.scale (395 / 4) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-41840216280 / 1000000000000) (-41840216279 / 1000000000000), orderedInterval (-79647697129 / 1000000000000) (-79647697128 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 1) <| besselDerivativeNearFromState (170924424023821 / 1600000000000) 1 (IntervalRat.scale (395 / 4) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (55260980561 / 1000000000000) (55260980562 / 1000000000000), orderedInterval (53644351472 / 1000000000000) (53644351473 / 1000000000000)))) (orderedInterval (-2831950111 / 1000000000000) (-2831950099 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 1) <| besselDerivativeNearFromState (72273483025527 / 1600000000000) 1 (IntervalRat.scale (395 / 4) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (109320147895 / 1000000000000) (109320151762 / 1000000000000), orderedInterval (-47492511311 / 1000000000000) (-47492507443 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 1) <| besselDerivativeNearFromState (293787695994967 / 1600000000000) 1 (IntervalRat.scale (395 / 4) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (47961815462 / 1000000000000) (47961876530 / 1000000000000), orderedInterval (-34288471693 / 1000000000000) (-34288410626 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 1) <| besselDerivativeNearFromState (196236565608953 / 1600000000000) 1 (IntervalRat.scale (395 / 4) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-56885640973 / 1000000000000) (-56885640972 / 1000000000000), orderedInterval (-43979457805 / 1000000000000) (-43979457804 / 1000000000000)))) (orderedInterval (15307580659 / 1000000000000) (15307589952 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate219_chunkChecks1 :
    compactCertificate219.chunkChecks (1 : Fin 5) 0 9 = true :=
  compactCertificate219.chunkChecks_nine_of_three (1 : Fin 5) compactCertificate219_chunkChecks1_0
    compactCertificate219_chunkChecks1_1 compactCertificate219_chunkChecks1_2

theorem compactCertificate219_chunkChecks2_0 :
    compactCertificate219.chunkChecks (2 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 2) <| besselDerivativeNearFromState (395 / 4) 2 (IntervalRat.scale (395 / 4) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-67425099763 / 1000000000000) (-67425071799 / 1000000000000), orderedInterval (43937312986 / 1000000000000) (43937340951 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 2) <| besselDerivativeNearFromState (116382084884179 / 1600000000000) 2 (IntervalRat.scale (395 / 4) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-89235600066 / 1000000000000) (-89235600065 / 1000000000000), orderedInterval (-27475286317 / 1000000000000) (-27475286316 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 2) <| besselDerivativeNearFromState (37635575030707 / 320000000000) 2 (IntervalRat.scale (395 / 4) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-61306235196 / 1000000000000) (-61306201253 / 1000000000000), orderedInterval (40935511003 / 1000000000000) (40935544947 / 1000000000000)))) (orderedInterval (32075674075 / 1000000000000) (32075688130 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 2) <| besselDerivativeNearFromState (33960002108153 / 1600000000000) 2 (IntervalRat.scale (395 / 4) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-2314846465 / 1000000000000) (-2314846456 / 1000000000000), orderedInterval (-173141327171 / 1000000000000) (-173141327162 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 2) <| besselDerivativeNearFromState (91221342531941 / 1600000000000) 2 (IntervalRat.scale (395 / 4) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (100206353237 / 1000000000000) (100206353238 / 1000000000000), orderedInterval (32654818627 / 1000000000000) (32654818628 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 2) <| besselDerivativeNearFromState (247683690052497 / 1600000000000) 2 (IntervalRat.scale (395 / 4) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-63933089480 / 1000000000000) (-63933089331 / 1000000000000), orderedInterval (5207341772 / 1000000000000) (5207341921 / 1000000000000)))) (orderedInterval (-12394870677 / 1000000000000) (-12394870631 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 2) <| besselDerivativeNearFromState (182442685063961 / 1600000000000) 2 (IntervalRat.scale (395 / 4) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (73958578995 / 1000000000000) (73958579266 / 1000000000000), orderedInterval (-10961708207 / 1000000000000) (-10961707936 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 2) <| besselDerivativeNearFromState (312618650493053 / 1600000000000) 2 (IntervalRat.scale (395 / 4) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (56177877503 / 1000000000000) (56177877507 / 1000000000000), orderedInterval (9970201569 / 1000000000000) (9970201574 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 2) <| besselDerivativeNearFromState (230273483025527 / 1600000000000) 2 (IntervalRat.scale (395 / 4) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (12704005439 / 1000000000000) (12704005440 / 1000000000000), orderedInterval (65240109848 / 1000000000000) (65240109849 / 1000000000000)))) (orderedInterval (6114194663 / 1000000000000) (6114194682 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate219_chunkChecks2_1 :
    compactCertificate219.chunkChecks (2 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 2) <| besselDerivativeNearFromState (353298740444921 / 1600000000000) 2 (IntervalRat.scale (395 / 4) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (53344197840 / 1000000000000) (53344198215 / 1000000000000), orderedInterval (-6242728350 / 1000000000000) (-6242727975 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 2) <| besselDerivativeNearFromState (203977122900209 / 1600000000000) 2 (IntervalRat.scale (395 / 4) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (36039085467 / 1000000000000) (36039091577 / 1000000000000), orderedInterval (-60926696305 / 1000000000000) (-60926690195 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 2) <| besselDerivativeNearFromState (361960984042981 / 1600000000000) 2 (IntervalRat.scale (395 / 4) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (38633070837 / 1000000000000) (38633070838 / 1000000000000), orderedInterval (36268125359 / 1000000000000) (36268125360 / 1000000000000)))) (orderedInterval (14034437062 / 1000000000000) (14034438332 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 2) <| besselDerivativeNearFromState (338190903636889 / 1600000000000) 2 (IntervalRat.scale (395 / 4) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-54624599937 / 1000000000000) (-54624599656 / 1000000000000), orderedInterval (5423403012 / 1000000000000) (5423403292 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 2) <| besselDerivativeNearFromState (241348986600937 / 1600000000000) 2 (IntervalRat.scale (395 / 4) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (47993618882 / 1000000000000) (47993618883 / 1000000000000), orderedInterval (43624707065 / 1000000000000) (43624707066 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 2) <| besselDerivativeNearFromState (273664027595823 / 1600000000000) 2 (IntervalRat.scale (395 / 4) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (50079267219 / 1000000000000) (50079319727 / 1000000000000), orderedInterval (-34990506465 / 1000000000000) (-34990453957 / 1000000000000)))) (orderedInterval (-14412172023 / 1000000000000) (-14412171165 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 2) <| besselDerivativeNearFromState (228152535300287 / 1600000000000) 2 (IntervalRat.scale (395 / 4) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-60526733505 / 1000000000000) (-60526724221 / 1000000000000), orderedInterval (28514483203 / 1000000000000) (28514492488 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 2) <| besselDerivativeNearFromState (201579684110027 / 1600000000000) 2 (IntervalRat.scale (395 / 4) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (63607034128 / 1000000000000) (63607034129 / 1000000000000), orderedInterval (31483485754 / 1000000000000) (31483485755 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 2) <| besselDerivativeNearFromState (58425649400673 / 320000000000) 2 (IntervalRat.scale (395 / 4) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (53957777179 / 1000000000000) (53957777180 / 1000000000000), orderedInterval (23838599984 / 1000000000000) (23838599985 / 1000000000000)))) (orderedInterval (2666619949 / 1000000000000) (2666620195 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate219_chunkChecks2_2 :
    compactCertificate219.chunkChecks (2 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 2) <| besselDerivativeNearFromState (161608421015731 / 1600000000000) 2 (IntervalRat.scale (395 / 4) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (75548876026 / 1000000000000) (75548876027 / 1000000000000), orderedInterval (24021563266 / 1000000000000) (24021563267 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 2) <| besselDerivativeNearFromState (136997248259291 / 1600000000000) 2 (IntervalRat.scale (395 / 4) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-86218669648 / 1000000000000) (-86218669612 / 1000000000000), orderedInterval (1660652686 / 1000000000000) (1660652722 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 2) <| besselDerivativeNearFromState (85726516974473 / 1600000000000) 2 (IntervalRat.scale (395 / 4) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-88983535686 / 1000000000000) (-88983535685 / 1000000000000), orderedInterval (-62127058859 / 1000000000000) (-62127058858 / 1000000000000)))) (orderedInterval (9873446265 / 1000000000000) (9873446289 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 2) <| besselDerivativeNearFromState (46104005942391 / 1600000000000) 2 (IntervalRat.scale (395 / 4) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-144041041065 / 1000000000000) (-144041041064 / 1000000000000), orderedInterval (-34142926646 / 1000000000000) (-34142926645 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 2) <| besselDerivativeNearFromState (125181344640173 / 1600000000000) 2 (IntervalRat.scale (395 / 4) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-41840216280 / 1000000000000) (-41840216279 / 1000000000000), orderedInterval (-79647697129 / 1000000000000) (-79647697128 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 2) <| besselDerivativeNearFromState (170924424023821 / 1600000000000) 2 (IntervalRat.scale (395 / 4) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (55260980561 / 1000000000000) (55260980562 / 1000000000000), orderedInterval (53644351472 / 1000000000000) (53644351473 / 1000000000000)))) (orderedInterval (4162715224 / 1000000000000) (4162715235 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 2) <| besselDerivativeNearFromState (72273483025527 / 1600000000000) 2 (IntervalRat.scale (395 / 4) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (109320147895 / 1000000000000) (109320151762 / 1000000000000), orderedInterval (-47492511311 / 1000000000000) (-47492507443 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 2) <| besselDerivativeNearFromState (293787695994967 / 1600000000000) 2 (IntervalRat.scale (395 / 4) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (47961815462 / 1000000000000) (47961876530 / 1000000000000), orderedInterval (-34288471693 / 1000000000000) (-34288410626 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 2) <| besselDerivativeNearFromState (196236565608953 / 1600000000000) 2 (IntervalRat.scale (395 / 4) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-56885640973 / 1000000000000) (-56885640972 / 1000000000000), orderedInterval (-43979457805 / 1000000000000) (-43979457804 / 1000000000000)))) (orderedInterval (-3258772984 / 1000000000000) (-3258755641 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate219_chunkChecks2 :
    compactCertificate219.chunkChecks (2 : Fin 5) 0 9 = true :=
  compactCertificate219.chunkChecks_nine_of_three (2 : Fin 5) compactCertificate219_chunkChecks2_0
    compactCertificate219_chunkChecks2_1 compactCertificate219_chunkChecks2_2

theorem compactCertificate219_chunkChecks3_0 :
    compactCertificate219.chunkChecks (3 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 3) <| besselDerivativeNearFromState (395 / 4) 3 (IntervalRat.scale (395 / 4) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-67425099763 / 1000000000000) (-67425071799 / 1000000000000), orderedInterval (43937312986 / 1000000000000) (43937340951 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 3) <| besselDerivativeNearFromState (116382084884179 / 1600000000000) 3 (IntervalRat.scale (395 / 4) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-89235600066 / 1000000000000) (-89235600065 / 1000000000000), orderedInterval (-27475286317 / 1000000000000) (-27475286316 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 3) <| besselDerivativeNearFromState (37635575030707 / 320000000000) 3 (IntervalRat.scale (395 / 4) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-61306235196 / 1000000000000) (-61306201253 / 1000000000000), orderedInterval (40935511003 / 1000000000000) (40935544947 / 1000000000000)))) (orderedInterval (-21693863196 / 1000000000000) (-21693848597 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 3) <| besselDerivativeNearFromState (33960002108153 / 1600000000000) 3 (IntervalRat.scale (395 / 4) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-2314846465 / 1000000000000) (-2314846456 / 1000000000000), orderedInterval (-173141327171 / 1000000000000) (-173141327162 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 3) <| besselDerivativeNearFromState (91221342531941 / 1600000000000) 3 (IntervalRat.scale (395 / 4) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (100206353237 / 1000000000000) (100206353238 / 1000000000000), orderedInterval (32654818627 / 1000000000000) (32654818628 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 3) <| besselDerivativeNearFromState (247683690052497 / 1600000000000) 3 (IntervalRat.scale (395 / 4) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-63933089480 / 1000000000000) (-63933089331 / 1000000000000), orderedInterval (5207341772 / 1000000000000) (5207341921 / 1000000000000)))) (orderedInterval (1303540829 / 1000000000000) (1303540898 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 3) <| besselDerivativeNearFromState (182442685063961 / 1600000000000) 3 (IntervalRat.scale (395 / 4) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (73958578995 / 1000000000000) (73958579266 / 1000000000000), orderedInterval (-10961708207 / 1000000000000) (-10961707936 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 3) <| besselDerivativeNearFromState (312618650493053 / 1600000000000) 3 (IntervalRat.scale (395 / 4) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (56177877503 / 1000000000000) (56177877507 / 1000000000000), orderedInterval (9970201569 / 1000000000000) (9970201574 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 3) <| besselDerivativeNearFromState (230273483025527 / 1600000000000) 3 (IntervalRat.scale (395 / 4) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (12704005439 / 1000000000000) (12704005440 / 1000000000000), orderedInterval (65240109848 / 1000000000000) (65240109849 / 1000000000000)))) (orderedInterval (-2560793651 / 1000000000000) (-2560793618 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate219_chunkChecks3_1 :
    compactCertificate219.chunkChecks (3 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 3) <| besselDerivativeNearFromState (353298740444921 / 1600000000000) 3 (IntervalRat.scale (395 / 4) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (53344197840 / 1000000000000) (53344198215 / 1000000000000), orderedInterval (-6242728350 / 1000000000000) (-6242727975 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 3) <| besselDerivativeNearFromState (203977122900209 / 1600000000000) 3 (IntervalRat.scale (395 / 4) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (36039085467 / 1000000000000) (36039091577 / 1000000000000), orderedInterval (-60926696305 / 1000000000000) (-60926690195 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 3) <| besselDerivativeNearFromState (361960984042981 / 1600000000000) 3 (IntervalRat.scale (395 / 4) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (38633070837 / 1000000000000) (38633070838 / 1000000000000), orderedInterval (36268125359 / 1000000000000) (36268125360 / 1000000000000)))) (orderedInterval (-64817670593 / 1000000000000) (-64817668480 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 3) <| besselDerivativeNearFromState (338190903636889 / 1600000000000) 3 (IntervalRat.scale (395 / 4) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-54624599937 / 1000000000000) (-54624599656 / 1000000000000), orderedInterval (5423403012 / 1000000000000) (5423403292 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 3) <| besselDerivativeNearFromState (241348986600937 / 1600000000000) 3 (IntervalRat.scale (395 / 4) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (47993618882 / 1000000000000) (47993618883 / 1000000000000), orderedInterval (43624707065 / 1000000000000) (43624707066 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 3) <| besselDerivativeNearFromState (273664027595823 / 1600000000000) 3 (IntervalRat.scale (395 / 4) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (50079267219 / 1000000000000) (50079319727 / 1000000000000), orderedInterval (-34990506465 / 1000000000000) (-34990453957 / 1000000000000)))) (orderedInterval (-14516763124 / 1000000000000) (-14516761630 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 3) <| besselDerivativeNearFromState (228152535300287 / 1600000000000) 3 (IntervalRat.scale (395 / 4) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-60526733505 / 1000000000000) (-60526724221 / 1000000000000), orderedInterval (28514483203 / 1000000000000) (28514492488 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 3) <| besselDerivativeNearFromState (201579684110027 / 1600000000000) 3 (IntervalRat.scale (395 / 4) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (63607034128 / 1000000000000) (63607034129 / 1000000000000), orderedInterval (31483485754 / 1000000000000) (31483485755 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 3) <| besselDerivativeNearFromState (58425649400673 / 320000000000) 3 (IntervalRat.scale (395 / 4) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (53957777179 / 1000000000000) (53957777180 / 1000000000000), orderedInterval (23838599984 / 1000000000000) (23838599985 / 1000000000000)))) (orderedInterval (-1134748156 / 1000000000000) (-1134747799 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate219_chunkChecks3_2 :
    compactCertificate219.chunkChecks (3 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 3) <| besselDerivativeNearFromState (161608421015731 / 1600000000000) 3 (IntervalRat.scale (395 / 4) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (75548876026 / 1000000000000) (75548876027 / 1000000000000), orderedInterval (24021563266 / 1000000000000) (24021563267 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 3) <| besselDerivativeNearFromState (136997248259291 / 1600000000000) 3 (IntervalRat.scale (395 / 4) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-86218669648 / 1000000000000) (-86218669612 / 1000000000000), orderedInterval (1660652686 / 1000000000000) (1660652722 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 3) <| besselDerivativeNearFromState (85726516974473 / 1600000000000) 3 (IntervalRat.scale (395 / 4) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-88983535686 / 1000000000000) (-88983535685 / 1000000000000), orderedInterval (-62127058859 / 1000000000000) (-62127058858 / 1000000000000)))) (orderedInterval (4393894969 / 1000000000000) (4393894993 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 3) <| besselDerivativeNearFromState (46104005942391 / 1600000000000) 3 (IntervalRat.scale (395 / 4) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-144041041065 / 1000000000000) (-144041041064 / 1000000000000), orderedInterval (-34142926646 / 1000000000000) (-34142926645 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 3) <| besselDerivativeNearFromState (125181344640173 / 1600000000000) 3 (IntervalRat.scale (395 / 4) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-41840216280 / 1000000000000) (-41840216279 / 1000000000000), orderedInterval (-79647697129 / 1000000000000) (-79647697128 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 3) <| besselDerivativeNearFromState (170924424023821 / 1600000000000) 3 (IntervalRat.scale (395 / 4) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (55260980561 / 1000000000000) (55260980562 / 1000000000000), orderedInterval (53644351472 / 1000000000000) (53644351473 / 1000000000000)))) (orderedInterval (4248153839 / 1000000000000) (4248153851 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 3) <| besselDerivativeNearFromState (72273483025527 / 1600000000000) 3 (IntervalRat.scale (395 / 4) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (109320147895 / 1000000000000) (109320151762 / 1000000000000), orderedInterval (-47492511311 / 1000000000000) (-47492507443 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 3) <| besselDerivativeNearFromState (293787695994967 / 1600000000000) 3 (IntervalRat.scale (395 / 4) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (47961815462 / 1000000000000) (47961876530 / 1000000000000), orderedInterval (-34288471693 / 1000000000000) (-34288410626 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 3) <| besselDerivativeNearFromState (196236565608953 / 1600000000000) 3 (IntervalRat.scale (395 / 4) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-56885640973 / 1000000000000) (-56885640972 / 1000000000000), orderedInterval (-43979457805 / 1000000000000) (-43979457804 / 1000000000000)))) (orderedInterval (-33691010303 / 1000000000000) (-33690978083 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate219_chunkChecks3 :
    compactCertificate219.chunkChecks (3 : Fin 5) 0 9 = true :=
  compactCertificate219.chunkChecks_nine_of_three (3 : Fin 5) compactCertificate219_chunkChecks3_0
    compactCertificate219_chunkChecks3_1 compactCertificate219_chunkChecks3_2

theorem compactCertificate219_chunkChecks4_0 :
    compactCertificate219.chunkChecks (4 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 4) <| besselDerivativeNearFromState (395 / 4) 4 (IntervalRat.scale (395 / 4) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-67425099763 / 1000000000000) (-67425071799 / 1000000000000), orderedInterval (43937312986 / 1000000000000) (43937340951 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 4) <| besselDerivativeNearFromState (116382084884179 / 1600000000000) 4 (IntervalRat.scale (395 / 4) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-89235600066 / 1000000000000) (-89235600065 / 1000000000000), orderedInterval (-27475286317 / 1000000000000) (-27475286316 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 4) <| besselDerivativeNearFromState (37635575030707 / 320000000000) 4 (IntervalRat.scale (395 / 4) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-61306235196 / 1000000000000) (-61306201253 / 1000000000000), orderedInterval (40935511003 / 1000000000000) (40935544947 / 1000000000000)))) (orderedInterval (-33765602287 / 1000000000000) (-33765586894 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 4) <| besselDerivativeNearFromState (33960002108153 / 1600000000000) 4 (IntervalRat.scale (395 / 4) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-2314846465 / 1000000000000) (-2314846456 / 1000000000000), orderedInterval (-173141327171 / 1000000000000) (-173141327162 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 4) <| besselDerivativeNearFromState (91221342531941 / 1600000000000) 4 (IntervalRat.scale (395 / 4) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (100206353237 / 1000000000000) (100206353238 / 1000000000000), orderedInterval (32654818627 / 1000000000000) (32654818628 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 4) <| besselDerivativeNearFromState (247683690052497 / 1600000000000) 4 (IntervalRat.scale (395 / 4) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-63933089480 / 1000000000000) (-63933089331 / 1000000000000), orderedInterval (5207341772 / 1000000000000) (5207341921 / 1000000000000)))) (orderedInterval (27825804428 / 1000000000000) (27825804536 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 4) <| besselDerivativeNearFromState (182442685063961 / 1600000000000) 4 (IntervalRat.scale (395 / 4) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (73958578995 / 1000000000000) (73958579266 / 1000000000000), orderedInterval (-10961708207 / 1000000000000) (-10961707936 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 4) <| besselDerivativeNearFromState (312618650493053 / 1600000000000) 4 (IntervalRat.scale (395 / 4) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (56177877503 / 1000000000000) (56177877507 / 1000000000000), orderedInterval (9970201569 / 1000000000000) (9970201574 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 4) <| besselDerivativeNearFromState (230273483025527 / 1600000000000) 4 (IntervalRat.scale (395 / 4) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (12704005439 / 1000000000000) (12704005440 / 1000000000000), orderedInterval (65240109848 / 1000000000000) (65240109849 / 1000000000000)))) (orderedInterval (-25118536213 / 1000000000000) (-25118536152 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate219_chunkChecks4_1 :
    compactCertificate219.chunkChecks (4 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 4) <| besselDerivativeNearFromState (353298740444921 / 1600000000000) 4 (IntervalRat.scale (395 / 4) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (53344197840 / 1000000000000) (53344198215 / 1000000000000), orderedInterval (-6242728350 / 1000000000000) (-6242727975 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 4) <| besselDerivativeNearFromState (203977122900209 / 1600000000000) 4 (IntervalRat.scale (395 / 4) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (36039085467 / 1000000000000) (36039091577 / 1000000000000), orderedInterval (-60926696305 / 1000000000000) (-60926690195 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 4) <| besselDerivativeNearFromState (361960984042981 / 1600000000000) 4 (IntervalRat.scale (395 / 4) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (38633070837 / 1000000000000) (38633070838 / 1000000000000), orderedInterval (36268125359 / 1000000000000) (36268125360 / 1000000000000)))) (orderedInterval (-76967573981 / 1000000000000) (-76967570172 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 4) <| besselDerivativeNearFromState (338190903636889 / 1600000000000) 4 (IntervalRat.scale (395 / 4) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-54624599937 / 1000000000000) (-54624599656 / 1000000000000), orderedInterval (5423403012 / 1000000000000) (5423403292 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 4) <| besselDerivativeNearFromState (241348986600937 / 1600000000000) 4 (IntervalRat.scale (395 / 4) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (47993618882 / 1000000000000) (47993618883 / 1000000000000), orderedInterval (43624707065 / 1000000000000) (43624707066 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 4) <| besselDerivativeNearFromState (273664027595823 / 1600000000000) 4 (IntervalRat.scale (395 / 4) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (50079267219 / 1000000000000) (50079319727 / 1000000000000), orderedInterval (-34990506465 / 1000000000000) (-34990453957 / 1000000000000)))) (orderedInterval (43420259664 / 1000000000000) (43420262285 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 4) <| besselDerivativeNearFromState (228152535300287 / 1600000000000) 4 (IntervalRat.scale (395 / 4) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-60526733505 / 1000000000000) (-60526724221 / 1000000000000), orderedInterval (28514483203 / 1000000000000) (28514492488 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 4) <| besselDerivativeNearFromState (201579684110027 / 1600000000000) 4 (IntervalRat.scale (395 / 4) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (63607034128 / 1000000000000) (63607034129 / 1000000000000), orderedInterval (31483485754 / 1000000000000) (31483485755 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 4) <| besselDerivativeNearFromState (58425649400673 / 320000000000) 4 (IntervalRat.scale (395 / 4) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (53957777179 / 1000000000000) (53957777180 / 1000000000000), orderedInterval (23838599984 / 1000000000000) (23838599985 / 1000000000000)))) (orderedInterval (3484840292 / 1000000000000) (3484840816 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate219_chunkChecks4_2 :
    compactCertificate219.chunkChecks (4 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 4) <| besselDerivativeNearFromState (161608421015731 / 1600000000000) 4 (IntervalRat.scale (395 / 4) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (75548876026 / 1000000000000) (75548876027 / 1000000000000), orderedInterval (24021563266 / 1000000000000) (24021563267 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 4) <| besselDerivativeNearFromState (136997248259291 / 1600000000000) 4 (IntervalRat.scale (395 / 4) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-86218669648 / 1000000000000) (-86218669612 / 1000000000000), orderedInterval (1660652686 / 1000000000000) (1660652722 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 4) <| besselDerivativeNearFromState (85726516974473 / 1600000000000) 4 (IntervalRat.scale (395 / 4) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-88983535686 / 1000000000000) (-88983535685 / 1000000000000), orderedInterval (-62127058859 / 1000000000000) (-62127058858 / 1000000000000)))) (orderedInterval (-10802342096 / 1000000000000) (-10802342073 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 4) <| besselDerivativeNearFromState (46104005942391 / 1600000000000) 4 (IntervalRat.scale (395 / 4) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-144041041065 / 1000000000000) (-144041041064 / 1000000000000), orderedInterval (-34142926646 / 1000000000000) (-34142926645 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 4) <| besselDerivativeNearFromState (125181344640173 / 1600000000000) 4 (IntervalRat.scale (395 / 4) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-41840216280 / 1000000000000) (-41840216279 / 1000000000000), orderedInterval (-79647697129 / 1000000000000) (-79647697128 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 4) <| besselDerivativeNearFromState (170924424023821 / 1600000000000) 4 (IntervalRat.scale (395 / 4) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (55260980561 / 1000000000000) (55260980562 / 1000000000000), orderedInterval (53644351472 / 1000000000000) (53644351473 / 1000000000000)))) (orderedInterval (-5492674864 / 1000000000000) (-5492674852 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 4) <| besselDerivativeNearFromState (72273483025527 / 1600000000000) 4 (IntervalRat.scale (395 / 4) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (109320147895 / 1000000000000) (109320151762 / 1000000000000), orderedInterval (-47492511311 / 1000000000000) (-47492507443 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 4) <| besselDerivativeNearFromState (293787695994967 / 1600000000000) 4 (IntervalRat.scale (395 / 4) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (47961815462 / 1000000000000) (47961876530 / 1000000000000), orderedInterval (-34288471693 / 1000000000000) (-34288410626 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 4) <| besselDerivativeNearFromState (196236565608953 / 1600000000000) 4 (IntervalRat.scale (395 / 4) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-56885640973 / 1000000000000) (-56885640972 / 1000000000000), orderedInterval (-43979457805 / 1000000000000) (-43979457804 / 1000000000000)))) (orderedInterval (-20561624665 / 1000000000000) (-20561564457 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate219_chunkChecks4 :
    compactCertificate219.chunkChecks (4 : Fin 5) 0 9 = true :=
  compactCertificate219.chunkChecks_nine_of_three (4 : Fin 5) compactCertificate219_chunkChecks4_0
    compactCertificate219_chunkChecks4_1 compactCertificate219_chunkChecks4_2

theorem compactCertificate219_chunks :
    ∀ r : Fin 5, ∀ b, compactCertificate219.chunkCheck r b = true :=
  compactCertificate219.chunkChecks_all (by
    intro r
    fin_cases r
    · exact compactCertificate219_chunkChecks0
    · exact compactCertificate219_chunkChecks1
    · exact compactCertificate219_chunkChecks2
    · exact compactCertificate219_chunkChecks3
    · exact compactCertificate219_chunkChecks4)

theorem compactCertificate219_coefficient0 :
    compactCertificate219.coefficientCheck (0 : Fin 5) = true := by
  norm_num [CompactCertificate.coefficientCheck, intervalFinSumHull,
    compactCertificate219, rationalIntervalSubset, orderedInterval, Fin.sum_univ_succ]

theorem compactCertificate219_coefficient1 :
    compactCertificate219.coefficientCheck (1 : Fin 5) = true := by
  norm_num [CompactCertificate.coefficientCheck, intervalFinSumHull,
    compactCertificate219, rationalIntervalSubset, orderedInterval, Fin.sum_univ_succ]

theorem compactCertificate219_coefficient2 :
    compactCertificate219.coefficientCheck (2 : Fin 5) = true := by
  norm_num [CompactCertificate.coefficientCheck, intervalFinSumHull,
    compactCertificate219, rationalIntervalSubset, orderedInterval, Fin.sum_univ_succ]

theorem compactCertificate219_coefficient3 :
    compactCertificate219.coefficientCheck (3 : Fin 5) = true := by
  norm_num [CompactCertificate.coefficientCheck, intervalFinSumHull,
    compactCertificate219, rationalIntervalSubset, orderedInterval, Fin.sum_univ_succ]

theorem compactCertificate219_coefficient4 :
    compactCertificate219.coefficientCheck (4 : Fin 5) = true := by
  norm_num [CompactCertificate.coefficientCheck, intervalFinSumHull,
    compactCertificate219, rationalIntervalSubset, orderedInterval, Fin.sum_univ_succ]

theorem compactCertificate219_coefficients : ∀ r : Fin 5,
    compactCertificate219.coefficientCheck r = true := by
  intro r
  fin_cases r
  · exact compactCertificate219_coefficient0
  · exact compactCertificate219_coefficient1
  · exact compactCertificate219_coefficient2
  · exact compactCertificate219_coefficient3
  · exact compactCertificate219_coefficient4

theorem compactCertificate219_lower : (1 : ℚ) ≤ compactCertificate219.output.lo := by
  norm_num [CompactCertificate.output, CompactCertificate.interval,
    CompactCertificate.coefficientTargetNat, compactCertificate219, dualConstant,
    intervalTaylorSum, intervalPow, intervalSub, intervalMaxAbs, widenInterval,
    rationalErrorInterval, orderedInterval, IntervalRat.add, IntervalRat.mul, IntervalRat.scale,
    IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4]

theorem compactCertificate219_proves {t : ℝ} (ht : t ∈ compactCertificate219.interval) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t :=
  compactCertificate219.proves compactCertificate219_states compactCertificate219_chunks
    compactCertificate219_coefficients compactCertificate219_lower ht

end Erdos232
