/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, OpenAI Codex
-/
import ErdosProblems.Erdos232.CompactBase

open LeanCert.Core
namespace Erdos232

def compactCertificate211 : CompactCertificate where
  left := 371 / 4
  right := 93
  center := 743 / 8
  grid := fun i =>
    match i.val with
    | 0 => 30
    | 1 => 22
    | 2 => 35
    | 3 => 6
    | 4 => 17
    | 5 => 46
    | 6 => 34
    | 7 => 59
    | 8 => 43
    | 9 => 66
    | 10 => 38
    | 11 => 68
    | 12 => 63
    | 13 => 45
    | 14 => 51
    | 15 => 43
    | 16 => 38
    | 17 => 55
    | 18 => 30
    | 19 => 26
    | 20 => 16
    | 21 => 9
    | 22 => 23
    | 23 => 32
    | 24 => 14
    | 25 => 55
    | _ => 37
  point := fun i =>
    match i.val with
    | 0 => 743 / 8
    | 1 => 1094580874290443 / 16000000000000
    | 2 => 353964965162219 / 3200000000000
    | 3 => 319395969194401 / 16000000000000
    | 4 => 857942500015597 / 16000000000000
    | 5 => 2329480781126649 / 16000000000000
    | 6 => 1715885000031937 / 16000000000000
    | 7 => 2940198193877701 / 16000000000000
    | 8 => 2165736682126159 / 16000000000000
    | 9 => 3322797014564257 / 16000000000000
    | 10 => 1918417750820953 / 16000000000000
    | 11 => 3404265963847277 / 16000000000000
    | 12 => 3180706853192513 / 16000000000000
    | 13 => 2269902494234129 / 16000000000000
    | 14 => 2573827500046791 / 16000000000000
    | 15 => 2145789034533079 / 16000000000000
    | 16 => 1895869687262659 / 16000000000000
    | 17 => 549496930439241 / 3200000000000
    | 18 => 1519937428034027 / 16000000000000
    | 19 => 1288467790590547 / 16000000000000
    | 20 => 806263317873841 / 16000000000000
    | 21 => 433611093863247 / 16000000000000
    | 22 => 1177338469210741 / 16000000000000
    | 23 => 1607555025945557 / 16000000000000
    | 24 => 679736682126159 / 16000000000000
    | 25 => 2763091874990639 / 16000000000000
    | _ => 1845617319588001 / 16000000000000
  state := fun i =>
    match i.val with
    | 0 => (orderedInterval (-45974559471 / 1000000000000) (-45974547009 / 1000000000000), orderedInterval (69102163628 / 1000000000000) (69102176090 / 1000000000000))
    | 1 => (orderedInterval (7693350261 / 1000000000000) (7693350264 / 1000000000000), orderedInterval (96104193910 / 1000000000000) (96104193912 / 1000000000000))
    | 2 => (orderedInterval (-75240715940 / 1000000000000) (-75240715935 / 1000000000000), orderedInterval (-9360541327 / 1000000000000) (-9360541322 / 1000000000000))
    | 3 => (orderedInterval (169430443842 / 1000000000000) (169430445281 / 1000000000000), orderedInterval (-60601871452 / 1000000000000) (-60601870013 / 1000000000000))
    | 4 => (orderedInterval (-91532045086 / 1000000000000) (-91532045085 / 1000000000000), orderedInterval (-58258038378 / 1000000000000) (-58258038377 / 1000000000000))
    | 5 => (orderedInterval (63306803712 / 1000000000000) (63306805747 / 1000000000000), orderedInterval (-19318176442 / 1000000000000) (-19318174407 / 1000000000000))
    | 6 => (orderedInterval (72164489234 / 1000000000000) (72164489235 / 1000000000000), orderedInterval (26654002551 / 1000000000000) (26654002552 / 1000000000000))
    | 7 => (orderedInterval (42503017289 / 1000000000000) (42503078517 / 1000000000000), orderedInterval (-40832430052 / 1000000000000) (-40832368824 / 1000000000000))
    | 8 => (orderedInterval (-59641724524 / 1000000000000) (-59641724523 / 1000000000000), orderedInterval (-33633188119 / 1000000000000) (-33633188118 / 1000000000000))
    | 9 => (orderedInterval (49701903896 / 1000000000000) (49701903897 / 1000000000000), orderedInterval (24276645707 / 1000000000000) (24276645708 / 1000000000000))
    | 10 => (orderedInterval (70306409702 / 1000000000000) (70306409704 / 1000000000000), orderedInterval (18851251830 / 1000000000000) (18851251831 / 1000000000000))
    | 11 => (orderedInterval (-4200491054 / 1000000000000) (-4200491045 / 1000000000000), orderedInterval (54548551038 / 1000000000000) (54548551047 / 1000000000000))
    | 12 => (orderedInterval (-56371668985 / 1000000000000) (-56371668755 / 1000000000000), orderedInterval (5104795486 / 1000000000000) (5104795716 / 1000000000000))
    | 13 => (orderedInterval (-64208865503 / 1000000000000) (-64208865502 / 1000000000000), orderedInterval (-18867653709 / 1000000000000) (-18867653707 / 1000000000000))
    | 14 => (orderedInterval (-62264750272 / 1000000000000) (-62264750266 / 1000000000000), orderedInterval (-8783118244 / 1000000000000) (-8783118238 / 1000000000000))
    | 15 => (orderedInterval (13160992527 / 1000000000000) (13160992620 / 1000000000000), orderedInterval (-67678584256 / 1000000000000) (-67678584163 / 1000000000000))
    | 16 => (orderedInterval (-7632770228 / 1000000000000) (-7632770199 / 1000000000000), orderedInterval (72932657541 / 1000000000000) (72932657570 / 1000000000000))
    | 17 => (orderedInterval (17126991395 / 1000000000000) (17126991650 / 1000000000000), orderedInterval (-58479656154 / 1000000000000) (-58479655898 / 1000000000000))
    | 18 => (orderedInterval (81801985280 / 1000000000000) (81801985297 / 1000000000000), orderedInterval (2712593240 / 1000000000000) (2712593258 / 1000000000000))
    | 19 => (orderedInterval (-32013047148 / 1000000000000) (-32013045889 / 1000000000000), orderedInterval (83148903894 / 1000000000000) (83148905153 / 1000000000000))
    | 20 => (orderedInterval (88660657470 / 1000000000000) (88660657471 / 1000000000000), orderedInterval (68204532765 / 1000000000000) (68204532766 / 1000000000000))
    | 21 => (orderedInterval (58669506303 / 1000000000000) (58669508499 / 1000000000000), orderedInterval (-142685786790 / 1000000000000) (-142685784595 / 1000000000000))
    | 22 => (orderedInterval (-79781711172 / 1000000000000) (-79781693062 / 1000000000000), orderedInterval (48358734786 / 1000000000000) (48358752896 / 1000000000000))
    | 23 => (orderedInterval (52808284243 / 1000000000000) (52808284244 / 1000000000000), orderedInterval (59298712159 / 1000000000000) (59298712160 / 1000000000000))
    | 24 => (orderedInterval (-80373631006 / 1000000000000) (-80373580116 / 1000000000000), orderedInterval (93278425903 / 1000000000000) (93278476793 / 1000000000000))
    | 25 => (orderedInterval (-38662852876 / 1000000000000) (-38662852875 / 1000000000000), orderedInterval (-46702656555 / 1000000000000) (-46702656554 / 1000000000000))
    | _ => (orderedInterval (7677540276 / 1000000000000) (7677540305 / 1000000000000), orderedInterval (-73925641917 / 1000000000000) (-73925641888 / 1000000000000))
  chunkTarget := fun r b =>
    match r.val with
    | 0 =>
      match b.val with
      | 0 => orderedInterval (-22566229833 / 1000000000000) (-22566224886 / 1000000000000)
      | 1 => orderedInterval (-9680653086 / 1000000000000) (-9680652913 / 1000000000000)
      | 2 => orderedInterval (-2752387808 / 1000000000000) (-2752385913 / 1000000000000)
      | 3 => orderedInterval (-4219426386 / 1000000000000) (-4219426346 / 1000000000000)
      | 4 => orderedInterval (-4738996266 / 1000000000000) (-4738996249 / 1000000000000)
      | 5 => orderedInterval (1027295500 / 1000000000000) (1027295519 / 1000000000000)
      | 6 => orderedInterval (-8381210482 / 1000000000000) (-8381210384 / 1000000000000)
      | 7 => orderedInterval (-3320510315 / 1000000000000) (-3320509852 / 1000000000000)
      | _ => orderedInterval (1222196081 / 1000000000000) (1222196420 / 1000000000000)
    | 1 =>
      match b.val with
      | 0 => orderedInterval (27395102603 / 1000000000000) (27395107551 / 1000000000000)
      | 1 => orderedInterval (1066079665 / 1000000000000) (1066079909 / 1000000000000)
      | 2 => orderedInterval (1307247757 / 1000000000000) (1307251504 / 1000000000000)
      | 3 => orderedInterval (9921999413 / 1000000000000) (9921999494 / 1000000000000)
      | 4 => orderedInterval (-2845651522 / 1000000000000) (-2845651494 / 1000000000000)
      | 5 => orderedInterval (-9221813221 / 1000000000000) (-9221813191 / 1000000000000)
      | 6 => orderedInterval (-3319522063 / 1000000000000) (-3319521976 / 1000000000000)
      | 7 => orderedInterval (-5016757103 / 1000000000000) (-5016756754 / 1000000000000)
      | _ => orderedInterval (24553220257 / 1000000000000) (24553220442 / 1000000000000)
    | 2 =>
      match b.val with
      | 0 => orderedInterval (24151722595 / 1000000000000) (24151727597 / 1000000000000)
      | 1 => orderedInterval (12246987753 / 1000000000000) (12246988130 / 1000000000000)
      | 2 => orderedInterval (8179871268 / 1000000000000) (8179878719 / 1000000000000)
      | 3 => orderedInterval (38502253558 / 1000000000000) (38502253730 / 1000000000000)
      | 4 => orderedInterval (8590292509 / 1000000000000) (8590292559 / 1000000000000)
      | 5 => orderedInterval (-2427656417 / 1000000000000) (-2427656370 / 1000000000000)
      | 6 => orderedInterval (11507563566 / 1000000000000) (11507563644 / 1000000000000)
      | 7 => orderedInterval (3746454966 / 1000000000000) (3746455242 / 1000000000000)
      | _ => orderedInterval (-8822196855 / 1000000000000) (-8822196726 / 1000000000000)
    | 3 =>
      match b.val with
      | 0 => orderedInterval (-27076477587 / 1000000000000) (-27076472585 / 1000000000000)
      | 1 => orderedInterval (-5019368958 / 1000000000000) (-5019368370 / 1000000000000)
      | 2 => orderedInterval (-7327075322 / 1000000000000) (-7327060585 / 1000000000000)
      | 3 => orderedInterval (-48421795256 / 1000000000000) (-48421794879 / 1000000000000)
      | 4 => orderedInterval (6939179801 / 1000000000000) (6939179894 / 1000000000000)
      | 5 => orderedInterval (20509342912 / 1000000000000) (20509342991 / 1000000000000)
      | 6 => orderedInterval (3053046947 / 1000000000000) (3053047018 / 1000000000000)
      | 7 => orderedInterval (6192792239 / 1000000000000) (6192792458 / 1000000000000)
      | _ => orderedInterval (-50970256954 / 1000000000000) (-50970256830 / 1000000000000)
    | _ =>
      match b.val with
      | 0 => orderedInterval (-26499534127 / 1000000000000) (-26499529070 / 1000000000000)
      | 1 => orderedInterval (-27443781114 / 1000000000000) (-27443780187 / 1000000000000)
      | 2 => orderedInterval (-26436603590 / 1000000000000) (-26436574279 / 1000000000000)
      | 3 => orderedInterval (-221715612394 / 1000000000000) (-221715611557 / 1000000000000)
      | 4 => orderedInterval (-9008512786 / 1000000000000) (-9008512609 / 1000000000000)
      | 5 => orderedInterval (6500664769 / 1000000000000) (6500664903 / 1000000000000)
      | 6 => orderedInterval (-13106043486 / 1000000000000) (-13106043422 / 1000000000000)
      | 7 => orderedInterval (-4970505658 / 1000000000000) (-4970505480 / 1000000000000)
      | _ => orderedInterval (35268908916 / 1000000000000) (35268909077 / 1000000000000)
  coefficientTarget := fun i =>
    match i.val with
    | 0 => orderedInterval (-53409922595 / 1000000000000) (-53409914604 / 1000000000000)
    | 1 => orderedInterval (43839905786 / 1000000000000) (43839915485 / 1000000000000)
    | 2 => orderedInterval (95675292943 / 1000000000000) (95675306525 / 1000000000000)
    | 3 => orderedInterval (-102120612178 / 1000000000000) (-102120590888 / 1000000000000)
    | _ => orderedInterval (-287411019470 / 1000000000000) (-287410982624 / 1000000000000)

theorem compactCertificate211_stateChecks0 :
    compactCertificate211.stateChecks 0 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 30 12 (743 / 8)) (orderedInterval (-45974559471 / 1000000000000) (-45974547009 / 1000000000000), orderedInterval (69102163628 / 1000000000000) (69102176090 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 22 12 (1094580874290443 / 16000000000000)) (orderedInterval (7693350261 / 1000000000000) (7693350264 / 1000000000000), orderedInterval (96104193910 / 1000000000000) (96104193912 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 35 12 (353964965162219 / 3200000000000)) (orderedInterval (-75240715940 / 1000000000000) (-75240715935 / 1000000000000), orderedInterval (-9360541327 / 1000000000000) (-9360541322 / 1000000000000))) = true
  norm_num [besselStateAtRationalPoint, besselIntervalStepZero,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, besselZeroTransition,
    besselInitial, besselGridStateAt, besselGridStateBlock00, besselGridStateBlock01,
    besselGridStateBlock02, besselGridStateBlock03, besselGridStateBlock04,
    besselGridStateBlock05, besselGridStateBlock06, besselGridStateBlock07,
    besselGridStateBlock08, besselGridStateBlock09, besselGridStateBlock10,
    besselGridStateBlock11, besselGridStateBlock12, besselGridStateBlock13,
    besselGridStateBlock14, besselGridState006, besselGridState009, besselGridState014, besselGridState016, besselGridState017, besselGridState022, besselGridState023, besselGridState026, besselGridState030, besselGridState032, besselGridState034, besselGridState035, besselGridState037, besselGridState038, besselGridState043, besselGridState045, besselGridState046, besselGridState051, besselGridState055, besselGridState059, besselGridState063, besselGridState066, besselGridState068, besselStateSubset, linearInterval, widenInterval,
    rationalErrorInterval, rationalIntervalSubset, orderedInterval, Finset.sum_range_succ,
    IntervalRat.add, IntervalRat.mul, IntervalRat.scale, IntervalRat.singleton]

theorem compactCertificate211_stateChecks1 :
    compactCertificate211.stateChecks 3 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 6 12 (319395969194401 / 16000000000000)) (orderedInterval (169430443842 / 1000000000000) (169430445281 / 1000000000000), orderedInterval (-60601871452 / 1000000000000) (-60601870013 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 17 12 (857942500015597 / 16000000000000)) (orderedInterval (-91532045086 / 1000000000000) (-91532045085 / 1000000000000), orderedInterval (-58258038378 / 1000000000000) (-58258038377 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 46 12 (2329480781126649 / 16000000000000)) (orderedInterval (63306803712 / 1000000000000) (63306805747 / 1000000000000), orderedInterval (-19318176442 / 1000000000000) (-19318174407 / 1000000000000))) = true
  norm_num [besselStateAtRationalPoint, besselIntervalStepZero,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, besselZeroTransition,
    besselInitial, besselGridStateAt, besselGridStateBlock00, besselGridStateBlock01,
    besselGridStateBlock02, besselGridStateBlock03, besselGridStateBlock04,
    besselGridStateBlock05, besselGridStateBlock06, besselGridStateBlock07,
    besselGridStateBlock08, besselGridStateBlock09, besselGridStateBlock10,
    besselGridStateBlock11, besselGridStateBlock12, besselGridStateBlock13,
    besselGridStateBlock14, besselGridState006, besselGridState009, besselGridState014, besselGridState016, besselGridState017, besselGridState022, besselGridState023, besselGridState026, besselGridState030, besselGridState032, besselGridState034, besselGridState035, besselGridState037, besselGridState038, besselGridState043, besselGridState045, besselGridState046, besselGridState051, besselGridState055, besselGridState059, besselGridState063, besselGridState066, besselGridState068, besselStateSubset, linearInterval, widenInterval,
    rationalErrorInterval, rationalIntervalSubset, orderedInterval, Finset.sum_range_succ,
    IntervalRat.add, IntervalRat.mul, IntervalRat.scale, IntervalRat.singleton]

theorem compactCertificate211_stateChecks2 :
    compactCertificate211.stateChecks 6 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 34 12 (1715885000031937 / 16000000000000)) (orderedInterval (72164489234 / 1000000000000) (72164489235 / 1000000000000), orderedInterval (26654002551 / 1000000000000) (26654002552 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 59 12 (2940198193877701 / 16000000000000)) (orderedInterval (42503017289 / 1000000000000) (42503078517 / 1000000000000), orderedInterval (-40832430052 / 1000000000000) (-40832368824 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 43 12 (2165736682126159 / 16000000000000)) (orderedInterval (-59641724524 / 1000000000000) (-59641724523 / 1000000000000), orderedInterval (-33633188119 / 1000000000000) (-33633188118 / 1000000000000))) = true
  norm_num [besselStateAtRationalPoint, besselIntervalStepZero,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, besselZeroTransition,
    besselInitial, besselGridStateAt, besselGridStateBlock00, besselGridStateBlock01,
    besselGridStateBlock02, besselGridStateBlock03, besselGridStateBlock04,
    besselGridStateBlock05, besselGridStateBlock06, besselGridStateBlock07,
    besselGridStateBlock08, besselGridStateBlock09, besselGridStateBlock10,
    besselGridStateBlock11, besselGridStateBlock12, besselGridStateBlock13,
    besselGridStateBlock14, besselGridState006, besselGridState009, besselGridState014, besselGridState016, besselGridState017, besselGridState022, besselGridState023, besselGridState026, besselGridState030, besselGridState032, besselGridState034, besselGridState035, besselGridState037, besselGridState038, besselGridState043, besselGridState045, besselGridState046, besselGridState051, besselGridState055, besselGridState059, besselGridState063, besselGridState066, besselGridState068, besselStateSubset, linearInterval, widenInterval,
    rationalErrorInterval, rationalIntervalSubset, orderedInterval, Finset.sum_range_succ,
    IntervalRat.add, IntervalRat.mul, IntervalRat.scale, IntervalRat.singleton]

theorem compactCertificate211_stateChecks3 :
    compactCertificate211.stateChecks 9 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 66 12 (3322797014564257 / 16000000000000)) (orderedInterval (49701903896 / 1000000000000) (49701903897 / 1000000000000), orderedInterval (24276645707 / 1000000000000) (24276645708 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 38 12 (1918417750820953 / 16000000000000)) (orderedInterval (70306409702 / 1000000000000) (70306409704 / 1000000000000), orderedInterval (18851251830 / 1000000000000) (18851251831 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 68 12 (3404265963847277 / 16000000000000)) (orderedInterval (-4200491054 / 1000000000000) (-4200491045 / 1000000000000), orderedInterval (54548551038 / 1000000000000) (54548551047 / 1000000000000))) = true
  norm_num [besselStateAtRationalPoint, besselIntervalStepZero,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, besselZeroTransition,
    besselInitial, besselGridStateAt, besselGridStateBlock00, besselGridStateBlock01,
    besselGridStateBlock02, besselGridStateBlock03, besselGridStateBlock04,
    besselGridStateBlock05, besselGridStateBlock06, besselGridStateBlock07,
    besselGridStateBlock08, besselGridStateBlock09, besselGridStateBlock10,
    besselGridStateBlock11, besselGridStateBlock12, besselGridStateBlock13,
    besselGridStateBlock14, besselGridState006, besselGridState009, besselGridState014, besselGridState016, besselGridState017, besselGridState022, besselGridState023, besselGridState026, besselGridState030, besselGridState032, besselGridState034, besselGridState035, besselGridState037, besselGridState038, besselGridState043, besselGridState045, besselGridState046, besselGridState051, besselGridState055, besselGridState059, besselGridState063, besselGridState066, besselGridState068, besselStateSubset, linearInterval, widenInterval,
    rationalErrorInterval, rationalIntervalSubset, orderedInterval, Finset.sum_range_succ,
    IntervalRat.add, IntervalRat.mul, IntervalRat.scale, IntervalRat.singleton]

theorem compactCertificate211_stateChecks4 :
    compactCertificate211.stateChecks 12 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 63 12 (3180706853192513 / 16000000000000)) (orderedInterval (-56371668985 / 1000000000000) (-56371668755 / 1000000000000), orderedInterval (5104795486 / 1000000000000) (5104795716 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 45 12 (2269902494234129 / 16000000000000)) (orderedInterval (-64208865503 / 1000000000000) (-64208865502 / 1000000000000), orderedInterval (-18867653709 / 1000000000000) (-18867653707 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 51 12 (2573827500046791 / 16000000000000)) (orderedInterval (-62264750272 / 1000000000000) (-62264750266 / 1000000000000), orderedInterval (-8783118244 / 1000000000000) (-8783118238 / 1000000000000))) = true
  norm_num [besselStateAtRationalPoint, besselIntervalStepZero,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, besselZeroTransition,
    besselInitial, besselGridStateAt, besselGridStateBlock00, besselGridStateBlock01,
    besselGridStateBlock02, besselGridStateBlock03, besselGridStateBlock04,
    besselGridStateBlock05, besselGridStateBlock06, besselGridStateBlock07,
    besselGridStateBlock08, besselGridStateBlock09, besselGridStateBlock10,
    besselGridStateBlock11, besselGridStateBlock12, besselGridStateBlock13,
    besselGridStateBlock14, besselGridState006, besselGridState009, besselGridState014, besselGridState016, besselGridState017, besselGridState022, besselGridState023, besselGridState026, besselGridState030, besselGridState032, besselGridState034, besselGridState035, besselGridState037, besselGridState038, besselGridState043, besselGridState045, besselGridState046, besselGridState051, besselGridState055, besselGridState059, besselGridState063, besselGridState066, besselGridState068, besselStateSubset, linearInterval, widenInterval,
    rationalErrorInterval, rationalIntervalSubset, orderedInterval, Finset.sum_range_succ,
    IntervalRat.add, IntervalRat.mul, IntervalRat.scale, IntervalRat.singleton]

theorem compactCertificate211_stateChecks5 :
    compactCertificate211.stateChecks 15 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 43 12 (2145789034533079 / 16000000000000)) (orderedInterval (13160992527 / 1000000000000) (13160992620 / 1000000000000), orderedInterval (-67678584256 / 1000000000000) (-67678584163 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 38 12 (1895869687262659 / 16000000000000)) (orderedInterval (-7632770228 / 1000000000000) (-7632770199 / 1000000000000), orderedInterval (72932657541 / 1000000000000) (72932657570 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 55 12 (549496930439241 / 3200000000000)) (orderedInterval (17126991395 / 1000000000000) (17126991650 / 1000000000000), orderedInterval (-58479656154 / 1000000000000) (-58479655898 / 1000000000000))) = true
  norm_num [besselStateAtRationalPoint, besselIntervalStepZero,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, besselZeroTransition,
    besselInitial, besselGridStateAt, besselGridStateBlock00, besselGridStateBlock01,
    besselGridStateBlock02, besselGridStateBlock03, besselGridStateBlock04,
    besselGridStateBlock05, besselGridStateBlock06, besselGridStateBlock07,
    besselGridStateBlock08, besselGridStateBlock09, besselGridStateBlock10,
    besselGridStateBlock11, besselGridStateBlock12, besselGridStateBlock13,
    besselGridStateBlock14, besselGridState006, besselGridState009, besselGridState014, besselGridState016, besselGridState017, besselGridState022, besselGridState023, besselGridState026, besselGridState030, besselGridState032, besselGridState034, besselGridState035, besselGridState037, besselGridState038, besselGridState043, besselGridState045, besselGridState046, besselGridState051, besselGridState055, besselGridState059, besselGridState063, besselGridState066, besselGridState068, besselStateSubset, linearInterval, widenInterval,
    rationalErrorInterval, rationalIntervalSubset, orderedInterval, Finset.sum_range_succ,
    IntervalRat.add, IntervalRat.mul, IntervalRat.scale, IntervalRat.singleton]

theorem compactCertificate211_stateChecks6 :
    compactCertificate211.stateChecks 18 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 30 12 (1519937428034027 / 16000000000000)) (orderedInterval (81801985280 / 1000000000000) (81801985297 / 1000000000000), orderedInterval (2712593240 / 1000000000000) (2712593258 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 26 12 (1288467790590547 / 16000000000000)) (orderedInterval (-32013047148 / 1000000000000) (-32013045889 / 1000000000000), orderedInterval (83148903894 / 1000000000000) (83148905153 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 16 12 (806263317873841 / 16000000000000)) (orderedInterval (88660657470 / 1000000000000) (88660657471 / 1000000000000), orderedInterval (68204532765 / 1000000000000) (68204532766 / 1000000000000))) = true
  norm_num [besselStateAtRationalPoint, besselIntervalStepZero,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, besselZeroTransition,
    besselInitial, besselGridStateAt, besselGridStateBlock00, besselGridStateBlock01,
    besselGridStateBlock02, besselGridStateBlock03, besselGridStateBlock04,
    besselGridStateBlock05, besselGridStateBlock06, besselGridStateBlock07,
    besselGridStateBlock08, besselGridStateBlock09, besselGridStateBlock10,
    besselGridStateBlock11, besselGridStateBlock12, besselGridStateBlock13,
    besselGridStateBlock14, besselGridState006, besselGridState009, besselGridState014, besselGridState016, besselGridState017, besselGridState022, besselGridState023, besselGridState026, besselGridState030, besselGridState032, besselGridState034, besselGridState035, besselGridState037, besselGridState038, besselGridState043, besselGridState045, besselGridState046, besselGridState051, besselGridState055, besselGridState059, besselGridState063, besselGridState066, besselGridState068, besselStateSubset, linearInterval, widenInterval,
    rationalErrorInterval, rationalIntervalSubset, orderedInterval, Finset.sum_range_succ,
    IntervalRat.add, IntervalRat.mul, IntervalRat.scale, IntervalRat.singleton]

theorem compactCertificate211_stateChecks7 :
    compactCertificate211.stateChecks 21 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 9 12 (433611093863247 / 16000000000000)) (orderedInterval (58669506303 / 1000000000000) (58669508499 / 1000000000000), orderedInterval (-142685786790 / 1000000000000) (-142685784595 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 23 12 (1177338469210741 / 16000000000000)) (orderedInterval (-79781711172 / 1000000000000) (-79781693062 / 1000000000000), orderedInterval (48358734786 / 1000000000000) (48358752896 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 32 12 (1607555025945557 / 16000000000000)) (orderedInterval (52808284243 / 1000000000000) (52808284244 / 1000000000000), orderedInterval (59298712159 / 1000000000000) (59298712160 / 1000000000000))) = true
  norm_num [besselStateAtRationalPoint, besselIntervalStepZero,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, besselZeroTransition,
    besselInitial, besselGridStateAt, besselGridStateBlock00, besselGridStateBlock01,
    besselGridStateBlock02, besselGridStateBlock03, besselGridStateBlock04,
    besselGridStateBlock05, besselGridStateBlock06, besselGridStateBlock07,
    besselGridStateBlock08, besselGridStateBlock09, besselGridStateBlock10,
    besselGridStateBlock11, besselGridStateBlock12, besselGridStateBlock13,
    besselGridStateBlock14, besselGridState006, besselGridState009, besselGridState014, besselGridState016, besselGridState017, besselGridState022, besselGridState023, besselGridState026, besselGridState030, besselGridState032, besselGridState034, besselGridState035, besselGridState037, besselGridState038, besselGridState043, besselGridState045, besselGridState046, besselGridState051, besselGridState055, besselGridState059, besselGridState063, besselGridState066, besselGridState068, besselStateSubset, linearInterval, widenInterval,
    rationalErrorInterval, rationalIntervalSubset, orderedInterval, Finset.sum_range_succ,
    IntervalRat.add, IntervalRat.mul, IntervalRat.scale, IntervalRat.singleton]

theorem compactCertificate211_stateChecks8 :
    compactCertificate211.stateChecks 24 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 14 12 (679736682126159 / 16000000000000)) (orderedInterval (-80373631006 / 1000000000000) (-80373580116 / 1000000000000), orderedInterval (93278425903 / 1000000000000) (93278476793 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 55 12 (2763091874990639 / 16000000000000)) (orderedInterval (-38662852876 / 1000000000000) (-38662852875 / 1000000000000), orderedInterval (-46702656555 / 1000000000000) (-46702656554 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 37 12 (1845617319588001 / 16000000000000)) (orderedInterval (7677540276 / 1000000000000) (7677540305 / 1000000000000), orderedInterval (-73925641917 / 1000000000000) (-73925641888 / 1000000000000))) = true
  norm_num [besselStateAtRationalPoint, besselIntervalStepZero,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, besselZeroTransition,
    besselInitial, besselGridStateAt, besselGridStateBlock00, besselGridStateBlock01,
    besselGridStateBlock02, besselGridStateBlock03, besselGridStateBlock04,
    besselGridStateBlock05, besselGridStateBlock06, besselGridStateBlock07,
    besselGridStateBlock08, besselGridStateBlock09, besselGridStateBlock10,
    besselGridStateBlock11, besselGridStateBlock12, besselGridStateBlock13,
    besselGridStateBlock14, besselGridState006, besselGridState009, besselGridState014, besselGridState016, besselGridState017, besselGridState022, besselGridState023, besselGridState026, besselGridState030, besselGridState032, besselGridState034, besselGridState035, besselGridState037, besselGridState038, besselGridState043, besselGridState045, besselGridState046, besselGridState051, besselGridState055, besselGridState059, besselGridState063, besselGridState066, besselGridState068, besselStateSubset, linearInterval, widenInterval,
    rationalErrorInterval, rationalIntervalSubset, orderedInterval, Finset.sum_range_succ,
    IntervalRat.add, IntervalRat.mul, IntervalRat.scale, IntervalRat.singleton]

theorem compactCertificate211_states : ∀ j,
    BesselStateValid (compactCertificate211.point j) (compactCertificate211.state j) :=
  compactCertificate211.statesValid_of_checks3 compactCertificate211_stateChecks0
    compactCertificate211_stateChecks1 compactCertificate211_stateChecks2
    compactCertificate211_stateChecks3 compactCertificate211_stateChecks4
    compactCertificate211_stateChecks5 compactCertificate211_stateChecks6
    compactCertificate211_stateChecks7 compactCertificate211_stateChecks8

theorem compactCertificate211_chunkChecks0_0 :
    compactCertificate211.chunkChecks (0 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 0) <| besselDerivativeNearFromState (743 / 8) 0 (IntervalRat.scale (743 / 8) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-45974559471 / 1000000000000) (-45974547009 / 1000000000000), orderedInterval (69102163628 / 1000000000000) (69102176090 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 0) <| besselDerivativeNearFromState (1094580874290443 / 16000000000000) 0 (IntervalRat.scale (743 / 8) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (7693350261 / 1000000000000) (7693350264 / 1000000000000), orderedInterval (96104193910 / 1000000000000) (96104193912 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 0) <| besselDerivativeNearFromState (353964965162219 / 3200000000000) 0 (IntervalRat.scale (743 / 8) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-75240715940 / 1000000000000) (-75240715935 / 1000000000000), orderedInterval (-9360541327 / 1000000000000) (-9360541322 / 1000000000000)))) (orderedInterval (-22566229833 / 1000000000000) (-22566224886 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 0) <| besselDerivativeNearFromState (319395969194401 / 16000000000000) 0 (IntervalRat.scale (743 / 8) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (169430443842 / 1000000000000) (169430445281 / 1000000000000), orderedInterval (-60601871452 / 1000000000000) (-60601870013 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 0) <| besselDerivativeNearFromState (857942500015597 / 16000000000000) 0 (IntervalRat.scale (743 / 8) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-91532045086 / 1000000000000) (-91532045085 / 1000000000000), orderedInterval (-58258038378 / 1000000000000) (-58258038377 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 0) <| besselDerivativeNearFromState (2329480781126649 / 16000000000000) 0 (IntervalRat.scale (743 / 8) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (63306803712 / 1000000000000) (63306805747 / 1000000000000), orderedInterval (-19318176442 / 1000000000000) (-19318174407 / 1000000000000)))) (orderedInterval (-9680653086 / 1000000000000) (-9680652913 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 0) <| besselDerivativeNearFromState (1715885000031937 / 16000000000000) 0 (IntervalRat.scale (743 / 8) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (72164489234 / 1000000000000) (72164489235 / 1000000000000), orderedInterval (26654002551 / 1000000000000) (26654002552 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 0) <| besselDerivativeNearFromState (2940198193877701 / 16000000000000) 0 (IntervalRat.scale (743 / 8) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (42503017289 / 1000000000000) (42503078517 / 1000000000000), orderedInterval (-40832430052 / 1000000000000) (-40832368824 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 0) <| besselDerivativeNearFromState (2165736682126159 / 16000000000000) 0 (IntervalRat.scale (743 / 8) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-59641724524 / 1000000000000) (-59641724523 / 1000000000000), orderedInterval (-33633188119 / 1000000000000) (-33633188118 / 1000000000000)))) (orderedInterval (-2752387808 / 1000000000000) (-2752385913 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate211_chunkChecks0_1 :
    compactCertificate211.chunkChecks (0 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 0) <| besselDerivativeNearFromState (3322797014564257 / 16000000000000) 0 (IntervalRat.scale (743 / 8) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (49701903896 / 1000000000000) (49701903897 / 1000000000000), orderedInterval (24276645707 / 1000000000000) (24276645708 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 0) <| besselDerivativeNearFromState (1918417750820953 / 16000000000000) 0 (IntervalRat.scale (743 / 8) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (70306409702 / 1000000000000) (70306409704 / 1000000000000), orderedInterval (18851251830 / 1000000000000) (18851251831 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 0) <| besselDerivativeNearFromState (3404265963847277 / 16000000000000) 0 (IntervalRat.scale (743 / 8) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-4200491054 / 1000000000000) (-4200491045 / 1000000000000), orderedInterval (54548551038 / 1000000000000) (54548551047 / 1000000000000)))) (orderedInterval (-4219426386 / 1000000000000) (-4219426346 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 0) <| besselDerivativeNearFromState (3180706853192513 / 16000000000000) 0 (IntervalRat.scale (743 / 8) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-56371668985 / 1000000000000) (-56371668755 / 1000000000000), orderedInterval (5104795486 / 1000000000000) (5104795716 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 0) <| besselDerivativeNearFromState (2269902494234129 / 16000000000000) 0 (IntervalRat.scale (743 / 8) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-64208865503 / 1000000000000) (-64208865502 / 1000000000000), orderedInterval (-18867653709 / 1000000000000) (-18867653707 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 0) <| besselDerivativeNearFromState (2573827500046791 / 16000000000000) 0 (IntervalRat.scale (743 / 8) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-62264750272 / 1000000000000) (-62264750266 / 1000000000000), orderedInterval (-8783118244 / 1000000000000) (-8783118238 / 1000000000000)))) (orderedInterval (-4738996266 / 1000000000000) (-4738996249 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 0) <| besselDerivativeNearFromState (2145789034533079 / 16000000000000) 0 (IntervalRat.scale (743 / 8) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (13160992527 / 1000000000000) (13160992620 / 1000000000000), orderedInterval (-67678584256 / 1000000000000) (-67678584163 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 0) <| besselDerivativeNearFromState (1895869687262659 / 16000000000000) 0 (IntervalRat.scale (743 / 8) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-7632770228 / 1000000000000) (-7632770199 / 1000000000000), orderedInterval (72932657541 / 1000000000000) (72932657570 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 0) <| besselDerivativeNearFromState (549496930439241 / 3200000000000) 0 (IntervalRat.scale (743 / 8) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (17126991395 / 1000000000000) (17126991650 / 1000000000000), orderedInterval (-58479656154 / 1000000000000) (-58479655898 / 1000000000000)))) (orderedInterval (1027295500 / 1000000000000) (1027295519 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate211_chunkChecks0_2 :
    compactCertificate211.chunkChecks (0 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 0) <| besselDerivativeNearFromState (1519937428034027 / 16000000000000) 0 (IntervalRat.scale (743 / 8) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (81801985280 / 1000000000000) (81801985297 / 1000000000000), orderedInterval (2712593240 / 1000000000000) (2712593258 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 0) <| besselDerivativeNearFromState (1288467790590547 / 16000000000000) 0 (IntervalRat.scale (743 / 8) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-32013047148 / 1000000000000) (-32013045889 / 1000000000000), orderedInterval (83148903894 / 1000000000000) (83148905153 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 0) <| besselDerivativeNearFromState (806263317873841 / 16000000000000) 0 (IntervalRat.scale (743 / 8) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (88660657470 / 1000000000000) (88660657471 / 1000000000000), orderedInterval (68204532765 / 1000000000000) (68204532766 / 1000000000000)))) (orderedInterval (-8381210482 / 1000000000000) (-8381210384 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 0) <| besselDerivativeNearFromState (433611093863247 / 16000000000000) 0 (IntervalRat.scale (743 / 8) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (58669506303 / 1000000000000) (58669508499 / 1000000000000), orderedInterval (-142685786790 / 1000000000000) (-142685784595 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 0) <| besselDerivativeNearFromState (1177338469210741 / 16000000000000) 0 (IntervalRat.scale (743 / 8) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-79781711172 / 1000000000000) (-79781693062 / 1000000000000), orderedInterval (48358734786 / 1000000000000) (48358752896 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 0) <| besselDerivativeNearFromState (1607555025945557 / 16000000000000) 0 (IntervalRat.scale (743 / 8) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (52808284243 / 1000000000000) (52808284244 / 1000000000000), orderedInterval (59298712159 / 1000000000000) (59298712160 / 1000000000000)))) (orderedInterval (-3320510315 / 1000000000000) (-3320509852 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 0) <| besselDerivativeNearFromState (679736682126159 / 16000000000000) 0 (IntervalRat.scale (743 / 8) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-80373631006 / 1000000000000) (-80373580116 / 1000000000000), orderedInterval (93278425903 / 1000000000000) (93278476793 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 0) <| besselDerivativeNearFromState (2763091874990639 / 16000000000000) 0 (IntervalRat.scale (743 / 8) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-38662852876 / 1000000000000) (-38662852875 / 1000000000000), orderedInterval (-46702656555 / 1000000000000) (-46702656554 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 0) <| besselDerivativeNearFromState (1845617319588001 / 16000000000000) 0 (IntervalRat.scale (743 / 8) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (7677540276 / 1000000000000) (7677540305 / 1000000000000), orderedInterval (-73925641917 / 1000000000000) (-73925641888 / 1000000000000)))) (orderedInterval (1222196081 / 1000000000000) (1222196420 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate211_chunkChecks0 :
    compactCertificate211.chunkChecks (0 : Fin 5) 0 9 = true :=
  compactCertificate211.chunkChecks_nine_of_three (0 : Fin 5) compactCertificate211_chunkChecks0_0
    compactCertificate211_chunkChecks0_1 compactCertificate211_chunkChecks0_2

theorem compactCertificate211_chunkChecks1_0 :
    compactCertificate211.chunkChecks (1 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 1) <| besselDerivativeNearFromState (743 / 8) 1 (IntervalRat.scale (743 / 8) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-45974559471 / 1000000000000) (-45974547009 / 1000000000000), orderedInterval (69102163628 / 1000000000000) (69102176090 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 1) <| besselDerivativeNearFromState (1094580874290443 / 16000000000000) 1 (IntervalRat.scale (743 / 8) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (7693350261 / 1000000000000) (7693350264 / 1000000000000), orderedInterval (96104193910 / 1000000000000) (96104193912 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 1) <| besselDerivativeNearFromState (353964965162219 / 3200000000000) 1 (IntervalRat.scale (743 / 8) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-75240715940 / 1000000000000) (-75240715935 / 1000000000000), orderedInterval (-9360541327 / 1000000000000) (-9360541322 / 1000000000000)))) (orderedInterval (27395102603 / 1000000000000) (27395107551 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 1) <| besselDerivativeNearFromState (319395969194401 / 16000000000000) 1 (IntervalRat.scale (743 / 8) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (169430443842 / 1000000000000) (169430445281 / 1000000000000), orderedInterval (-60601871452 / 1000000000000) (-60601870013 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 1) <| besselDerivativeNearFromState (857942500015597 / 16000000000000) 1 (IntervalRat.scale (743 / 8) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-91532045086 / 1000000000000) (-91532045085 / 1000000000000), orderedInterval (-58258038378 / 1000000000000) (-58258038377 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 1) <| besselDerivativeNearFromState (2329480781126649 / 16000000000000) 1 (IntervalRat.scale (743 / 8) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (63306803712 / 1000000000000) (63306805747 / 1000000000000), orderedInterval (-19318176442 / 1000000000000) (-19318174407 / 1000000000000)))) (orderedInterval (1066079665 / 1000000000000) (1066079909 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 1) <| besselDerivativeNearFromState (1715885000031937 / 16000000000000) 1 (IntervalRat.scale (743 / 8) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (72164489234 / 1000000000000) (72164489235 / 1000000000000), orderedInterval (26654002551 / 1000000000000) (26654002552 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 1) <| besselDerivativeNearFromState (2940198193877701 / 16000000000000) 1 (IntervalRat.scale (743 / 8) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (42503017289 / 1000000000000) (42503078517 / 1000000000000), orderedInterval (-40832430052 / 1000000000000) (-40832368824 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 1) <| besselDerivativeNearFromState (2165736682126159 / 16000000000000) 1 (IntervalRat.scale (743 / 8) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-59641724524 / 1000000000000) (-59641724523 / 1000000000000), orderedInterval (-33633188119 / 1000000000000) (-33633188118 / 1000000000000)))) (orderedInterval (1307247757 / 1000000000000) (1307251504 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate211_chunkChecks1_1 :
    compactCertificate211.chunkChecks (1 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 1) <| besselDerivativeNearFromState (3322797014564257 / 16000000000000) 1 (IntervalRat.scale (743 / 8) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (49701903896 / 1000000000000) (49701903897 / 1000000000000), orderedInterval (24276645707 / 1000000000000) (24276645708 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 1) <| besselDerivativeNearFromState (1918417750820953 / 16000000000000) 1 (IntervalRat.scale (743 / 8) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (70306409702 / 1000000000000) (70306409704 / 1000000000000), orderedInterval (18851251830 / 1000000000000) (18851251831 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 1) <| besselDerivativeNearFromState (3404265963847277 / 16000000000000) 1 (IntervalRat.scale (743 / 8) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-4200491054 / 1000000000000) (-4200491045 / 1000000000000), orderedInterval (54548551038 / 1000000000000) (54548551047 / 1000000000000)))) (orderedInterval (9921999413 / 1000000000000) (9921999494 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 1) <| besselDerivativeNearFromState (3180706853192513 / 16000000000000) 1 (IntervalRat.scale (743 / 8) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-56371668985 / 1000000000000) (-56371668755 / 1000000000000), orderedInterval (5104795486 / 1000000000000) (5104795716 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 1) <| besselDerivativeNearFromState (2269902494234129 / 16000000000000) 1 (IntervalRat.scale (743 / 8) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-64208865503 / 1000000000000) (-64208865502 / 1000000000000), orderedInterval (-18867653709 / 1000000000000) (-18867653707 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 1) <| besselDerivativeNearFromState (2573827500046791 / 16000000000000) 1 (IntervalRat.scale (743 / 8) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-62264750272 / 1000000000000) (-62264750266 / 1000000000000), orderedInterval (-8783118244 / 1000000000000) (-8783118238 / 1000000000000)))) (orderedInterval (-2845651522 / 1000000000000) (-2845651494 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 1) <| besselDerivativeNearFromState (2145789034533079 / 16000000000000) 1 (IntervalRat.scale (743 / 8) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (13160992527 / 1000000000000) (13160992620 / 1000000000000), orderedInterval (-67678584256 / 1000000000000) (-67678584163 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 1) <| besselDerivativeNearFromState (1895869687262659 / 16000000000000) 1 (IntervalRat.scale (743 / 8) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-7632770228 / 1000000000000) (-7632770199 / 1000000000000), orderedInterval (72932657541 / 1000000000000) (72932657570 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 1) <| besselDerivativeNearFromState (549496930439241 / 3200000000000) 1 (IntervalRat.scale (743 / 8) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (17126991395 / 1000000000000) (17126991650 / 1000000000000), orderedInterval (-58479656154 / 1000000000000) (-58479655898 / 1000000000000)))) (orderedInterval (-9221813221 / 1000000000000) (-9221813191 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate211_chunkChecks1_2 :
    compactCertificate211.chunkChecks (1 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 1) <| besselDerivativeNearFromState (1519937428034027 / 16000000000000) 1 (IntervalRat.scale (743 / 8) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (81801985280 / 1000000000000) (81801985297 / 1000000000000), orderedInterval (2712593240 / 1000000000000) (2712593258 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 1) <| besselDerivativeNearFromState (1288467790590547 / 16000000000000) 1 (IntervalRat.scale (743 / 8) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-32013047148 / 1000000000000) (-32013045889 / 1000000000000), orderedInterval (83148903894 / 1000000000000) (83148905153 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 1) <| besselDerivativeNearFromState (806263317873841 / 16000000000000) 1 (IntervalRat.scale (743 / 8) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (88660657470 / 1000000000000) (88660657471 / 1000000000000), orderedInterval (68204532765 / 1000000000000) (68204532766 / 1000000000000)))) (orderedInterval (-3319522063 / 1000000000000) (-3319521976 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 1) <| besselDerivativeNearFromState (433611093863247 / 16000000000000) 1 (IntervalRat.scale (743 / 8) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (58669506303 / 1000000000000) (58669508499 / 1000000000000), orderedInterval (-142685786790 / 1000000000000) (-142685784595 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 1) <| besselDerivativeNearFromState (1177338469210741 / 16000000000000) 1 (IntervalRat.scale (743 / 8) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-79781711172 / 1000000000000) (-79781693062 / 1000000000000), orderedInterval (48358734786 / 1000000000000) (48358752896 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 1) <| besselDerivativeNearFromState (1607555025945557 / 16000000000000) 1 (IntervalRat.scale (743 / 8) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (52808284243 / 1000000000000) (52808284244 / 1000000000000), orderedInterval (59298712159 / 1000000000000) (59298712160 / 1000000000000)))) (orderedInterval (-5016757103 / 1000000000000) (-5016756754 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 1) <| besselDerivativeNearFromState (679736682126159 / 16000000000000) 1 (IntervalRat.scale (743 / 8) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-80373631006 / 1000000000000) (-80373580116 / 1000000000000), orderedInterval (93278425903 / 1000000000000) (93278476793 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 1) <| besselDerivativeNearFromState (2763091874990639 / 16000000000000) 1 (IntervalRat.scale (743 / 8) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-38662852876 / 1000000000000) (-38662852875 / 1000000000000), orderedInterval (-46702656555 / 1000000000000) (-46702656554 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 1) <| besselDerivativeNearFromState (1845617319588001 / 16000000000000) 1 (IntervalRat.scale (743 / 8) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (7677540276 / 1000000000000) (7677540305 / 1000000000000), orderedInterval (-73925641917 / 1000000000000) (-73925641888 / 1000000000000)))) (orderedInterval (24553220257 / 1000000000000) (24553220442 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate211_chunkChecks1 :
    compactCertificate211.chunkChecks (1 : Fin 5) 0 9 = true :=
  compactCertificate211.chunkChecks_nine_of_three (1 : Fin 5) compactCertificate211_chunkChecks1_0
    compactCertificate211_chunkChecks1_1 compactCertificate211_chunkChecks1_2

theorem compactCertificate211_chunkChecks2_0 :
    compactCertificate211.chunkChecks (2 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 2) <| besselDerivativeNearFromState (743 / 8) 2 (IntervalRat.scale (743 / 8) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-45974559471 / 1000000000000) (-45974547009 / 1000000000000), orderedInterval (69102163628 / 1000000000000) (69102176090 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 2) <| besselDerivativeNearFromState (1094580874290443 / 16000000000000) 2 (IntervalRat.scale (743 / 8) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (7693350261 / 1000000000000) (7693350264 / 1000000000000), orderedInterval (96104193910 / 1000000000000) (96104193912 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 2) <| besselDerivativeNearFromState (353964965162219 / 3200000000000) 2 (IntervalRat.scale (743 / 8) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-75240715940 / 1000000000000) (-75240715935 / 1000000000000), orderedInterval (-9360541327 / 1000000000000) (-9360541322 / 1000000000000)))) (orderedInterval (24151722595 / 1000000000000) (24151727597 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 2) <| besselDerivativeNearFromState (319395969194401 / 16000000000000) 2 (IntervalRat.scale (743 / 8) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (169430443842 / 1000000000000) (169430445281 / 1000000000000), orderedInterval (-60601871452 / 1000000000000) (-60601870013 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 2) <| besselDerivativeNearFromState (857942500015597 / 16000000000000) 2 (IntervalRat.scale (743 / 8) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-91532045086 / 1000000000000) (-91532045085 / 1000000000000), orderedInterval (-58258038378 / 1000000000000) (-58258038377 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 2) <| besselDerivativeNearFromState (2329480781126649 / 16000000000000) 2 (IntervalRat.scale (743 / 8) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (63306803712 / 1000000000000) (63306805747 / 1000000000000), orderedInterval (-19318176442 / 1000000000000) (-19318174407 / 1000000000000)))) (orderedInterval (12246987753 / 1000000000000) (12246988130 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 2) <| besselDerivativeNearFromState (1715885000031937 / 16000000000000) 2 (IntervalRat.scale (743 / 8) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (72164489234 / 1000000000000) (72164489235 / 1000000000000), orderedInterval (26654002551 / 1000000000000) (26654002552 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 2) <| besselDerivativeNearFromState (2940198193877701 / 16000000000000) 2 (IntervalRat.scale (743 / 8) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (42503017289 / 1000000000000) (42503078517 / 1000000000000), orderedInterval (-40832430052 / 1000000000000) (-40832368824 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 2) <| besselDerivativeNearFromState (2165736682126159 / 16000000000000) 2 (IntervalRat.scale (743 / 8) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-59641724524 / 1000000000000) (-59641724523 / 1000000000000), orderedInterval (-33633188119 / 1000000000000) (-33633188118 / 1000000000000)))) (orderedInterval (8179871268 / 1000000000000) (8179878719 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate211_chunkChecks2_1 :
    compactCertificate211.chunkChecks (2 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 2) <| besselDerivativeNearFromState (3322797014564257 / 16000000000000) 2 (IntervalRat.scale (743 / 8) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (49701903896 / 1000000000000) (49701903897 / 1000000000000), orderedInterval (24276645707 / 1000000000000) (24276645708 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 2) <| besselDerivativeNearFromState (1918417750820953 / 16000000000000) 2 (IntervalRat.scale (743 / 8) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (70306409702 / 1000000000000) (70306409704 / 1000000000000), orderedInterval (18851251830 / 1000000000000) (18851251831 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 2) <| besselDerivativeNearFromState (3404265963847277 / 16000000000000) 2 (IntervalRat.scale (743 / 8) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-4200491054 / 1000000000000) (-4200491045 / 1000000000000), orderedInterval (54548551038 / 1000000000000) (54548551047 / 1000000000000)))) (orderedInterval (38502253558 / 1000000000000) (38502253730 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 2) <| besselDerivativeNearFromState (3180706853192513 / 16000000000000) 2 (IntervalRat.scale (743 / 8) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-56371668985 / 1000000000000) (-56371668755 / 1000000000000), orderedInterval (5104795486 / 1000000000000) (5104795716 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 2) <| besselDerivativeNearFromState (2269902494234129 / 16000000000000) 2 (IntervalRat.scale (743 / 8) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-64208865503 / 1000000000000) (-64208865502 / 1000000000000), orderedInterval (-18867653709 / 1000000000000) (-18867653707 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 2) <| besselDerivativeNearFromState (2573827500046791 / 16000000000000) 2 (IntervalRat.scale (743 / 8) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-62264750272 / 1000000000000) (-62264750266 / 1000000000000), orderedInterval (-8783118244 / 1000000000000) (-8783118238 / 1000000000000)))) (orderedInterval (8590292509 / 1000000000000) (8590292559 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 2) <| besselDerivativeNearFromState (2145789034533079 / 16000000000000) 2 (IntervalRat.scale (743 / 8) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (13160992527 / 1000000000000) (13160992620 / 1000000000000), orderedInterval (-67678584256 / 1000000000000) (-67678584163 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 2) <| besselDerivativeNearFromState (1895869687262659 / 16000000000000) 2 (IntervalRat.scale (743 / 8) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-7632770228 / 1000000000000) (-7632770199 / 1000000000000), orderedInterval (72932657541 / 1000000000000) (72932657570 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 2) <| besselDerivativeNearFromState (549496930439241 / 3200000000000) 2 (IntervalRat.scale (743 / 8) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (17126991395 / 1000000000000) (17126991650 / 1000000000000), orderedInterval (-58479656154 / 1000000000000) (-58479655898 / 1000000000000)))) (orderedInterval (-2427656417 / 1000000000000) (-2427656370 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate211_chunkChecks2_2 :
    compactCertificate211.chunkChecks (2 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 2) <| besselDerivativeNearFromState (1519937428034027 / 16000000000000) 2 (IntervalRat.scale (743 / 8) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (81801985280 / 1000000000000) (81801985297 / 1000000000000), orderedInterval (2712593240 / 1000000000000) (2712593258 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 2) <| besselDerivativeNearFromState (1288467790590547 / 16000000000000) 2 (IntervalRat.scale (743 / 8) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-32013047148 / 1000000000000) (-32013045889 / 1000000000000), orderedInterval (83148903894 / 1000000000000) (83148905153 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 2) <| besselDerivativeNearFromState (806263317873841 / 16000000000000) 2 (IntervalRat.scale (743 / 8) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (88660657470 / 1000000000000) (88660657471 / 1000000000000), orderedInterval (68204532765 / 1000000000000) (68204532766 / 1000000000000)))) (orderedInterval (11507563566 / 1000000000000) (11507563644 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 2) <| besselDerivativeNearFromState (433611093863247 / 16000000000000) 2 (IntervalRat.scale (743 / 8) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (58669506303 / 1000000000000) (58669508499 / 1000000000000), orderedInterval (-142685786790 / 1000000000000) (-142685784595 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 2) <| besselDerivativeNearFromState (1177338469210741 / 16000000000000) 2 (IntervalRat.scale (743 / 8) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-79781711172 / 1000000000000) (-79781693062 / 1000000000000), orderedInterval (48358734786 / 1000000000000) (48358752896 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 2) <| besselDerivativeNearFromState (1607555025945557 / 16000000000000) 2 (IntervalRat.scale (743 / 8) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (52808284243 / 1000000000000) (52808284244 / 1000000000000), orderedInterval (59298712159 / 1000000000000) (59298712160 / 1000000000000)))) (orderedInterval (3746454966 / 1000000000000) (3746455242 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 2) <| besselDerivativeNearFromState (679736682126159 / 16000000000000) 2 (IntervalRat.scale (743 / 8) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-80373631006 / 1000000000000) (-80373580116 / 1000000000000), orderedInterval (93278425903 / 1000000000000) (93278476793 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 2) <| besselDerivativeNearFromState (2763091874990639 / 16000000000000) 2 (IntervalRat.scale (743 / 8) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-38662852876 / 1000000000000) (-38662852875 / 1000000000000), orderedInterval (-46702656555 / 1000000000000) (-46702656554 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 2) <| besselDerivativeNearFromState (1845617319588001 / 16000000000000) 2 (IntervalRat.scale (743 / 8) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (7677540276 / 1000000000000) (7677540305 / 1000000000000), orderedInterval (-73925641917 / 1000000000000) (-73925641888 / 1000000000000)))) (orderedInterval (-8822196855 / 1000000000000) (-8822196726 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate211_chunkChecks2 :
    compactCertificate211.chunkChecks (2 : Fin 5) 0 9 = true :=
  compactCertificate211.chunkChecks_nine_of_three (2 : Fin 5) compactCertificate211_chunkChecks2_0
    compactCertificate211_chunkChecks2_1 compactCertificate211_chunkChecks2_2

theorem compactCertificate211_chunkChecks3_0 :
    compactCertificate211.chunkChecks (3 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 3) <| besselDerivativeNearFromState (743 / 8) 3 (IntervalRat.scale (743 / 8) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-45974559471 / 1000000000000) (-45974547009 / 1000000000000), orderedInterval (69102163628 / 1000000000000) (69102176090 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 3) <| besselDerivativeNearFromState (1094580874290443 / 16000000000000) 3 (IntervalRat.scale (743 / 8) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (7693350261 / 1000000000000) (7693350264 / 1000000000000), orderedInterval (96104193910 / 1000000000000) (96104193912 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 3) <| besselDerivativeNearFromState (353964965162219 / 3200000000000) 3 (IntervalRat.scale (743 / 8) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-75240715940 / 1000000000000) (-75240715935 / 1000000000000), orderedInterval (-9360541327 / 1000000000000) (-9360541322 / 1000000000000)))) (orderedInterval (-27076477587 / 1000000000000) (-27076472585 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 3) <| besselDerivativeNearFromState (319395969194401 / 16000000000000) 3 (IntervalRat.scale (743 / 8) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (169430443842 / 1000000000000) (169430445281 / 1000000000000), orderedInterval (-60601871452 / 1000000000000) (-60601870013 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 3) <| besselDerivativeNearFromState (857942500015597 / 16000000000000) 3 (IntervalRat.scale (743 / 8) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-91532045086 / 1000000000000) (-91532045085 / 1000000000000), orderedInterval (-58258038378 / 1000000000000) (-58258038377 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 3) <| besselDerivativeNearFromState (2329480781126649 / 16000000000000) 3 (IntervalRat.scale (743 / 8) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (63306803712 / 1000000000000) (63306805747 / 1000000000000), orderedInterval (-19318176442 / 1000000000000) (-19318174407 / 1000000000000)))) (orderedInterval (-5019368958 / 1000000000000) (-5019368370 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 3) <| besselDerivativeNearFromState (1715885000031937 / 16000000000000) 3 (IntervalRat.scale (743 / 8) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (72164489234 / 1000000000000) (72164489235 / 1000000000000), orderedInterval (26654002551 / 1000000000000) (26654002552 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 3) <| besselDerivativeNearFromState (2940198193877701 / 16000000000000) 3 (IntervalRat.scale (743 / 8) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (42503017289 / 1000000000000) (42503078517 / 1000000000000), orderedInterval (-40832430052 / 1000000000000) (-40832368824 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 3) <| besselDerivativeNearFromState (2165736682126159 / 16000000000000) 3 (IntervalRat.scale (743 / 8) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-59641724524 / 1000000000000) (-59641724523 / 1000000000000), orderedInterval (-33633188119 / 1000000000000) (-33633188118 / 1000000000000)))) (orderedInterval (-7327075322 / 1000000000000) (-7327060585 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate211_chunkChecks3_1 :
    compactCertificate211.chunkChecks (3 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 3) <| besselDerivativeNearFromState (3322797014564257 / 16000000000000) 3 (IntervalRat.scale (743 / 8) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (49701903896 / 1000000000000) (49701903897 / 1000000000000), orderedInterval (24276645707 / 1000000000000) (24276645708 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 3) <| besselDerivativeNearFromState (1918417750820953 / 16000000000000) 3 (IntervalRat.scale (743 / 8) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (70306409702 / 1000000000000) (70306409704 / 1000000000000), orderedInterval (18851251830 / 1000000000000) (18851251831 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 3) <| besselDerivativeNearFromState (3404265963847277 / 16000000000000) 3 (IntervalRat.scale (743 / 8) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-4200491054 / 1000000000000) (-4200491045 / 1000000000000), orderedInterval (54548551038 / 1000000000000) (54548551047 / 1000000000000)))) (orderedInterval (-48421795256 / 1000000000000) (-48421794879 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 3) <| besselDerivativeNearFromState (3180706853192513 / 16000000000000) 3 (IntervalRat.scale (743 / 8) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-56371668985 / 1000000000000) (-56371668755 / 1000000000000), orderedInterval (5104795486 / 1000000000000) (5104795716 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 3) <| besselDerivativeNearFromState (2269902494234129 / 16000000000000) 3 (IntervalRat.scale (743 / 8) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-64208865503 / 1000000000000) (-64208865502 / 1000000000000), orderedInterval (-18867653709 / 1000000000000) (-18867653707 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 3) <| besselDerivativeNearFromState (2573827500046791 / 16000000000000) 3 (IntervalRat.scale (743 / 8) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-62264750272 / 1000000000000) (-62264750266 / 1000000000000), orderedInterval (-8783118244 / 1000000000000) (-8783118238 / 1000000000000)))) (orderedInterval (6939179801 / 1000000000000) (6939179894 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 3) <| besselDerivativeNearFromState (2145789034533079 / 16000000000000) 3 (IntervalRat.scale (743 / 8) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (13160992527 / 1000000000000) (13160992620 / 1000000000000), orderedInterval (-67678584256 / 1000000000000) (-67678584163 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 3) <| besselDerivativeNearFromState (1895869687262659 / 16000000000000) 3 (IntervalRat.scale (743 / 8) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-7632770228 / 1000000000000) (-7632770199 / 1000000000000), orderedInterval (72932657541 / 1000000000000) (72932657570 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 3) <| besselDerivativeNearFromState (549496930439241 / 3200000000000) 3 (IntervalRat.scale (743 / 8) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (17126991395 / 1000000000000) (17126991650 / 1000000000000), orderedInterval (-58479656154 / 1000000000000) (-58479655898 / 1000000000000)))) (orderedInterval (20509342912 / 1000000000000) (20509342991 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate211_chunkChecks3_2 :
    compactCertificate211.chunkChecks (3 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 3) <| besselDerivativeNearFromState (1519937428034027 / 16000000000000) 3 (IntervalRat.scale (743 / 8) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (81801985280 / 1000000000000) (81801985297 / 1000000000000), orderedInterval (2712593240 / 1000000000000) (2712593258 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 3) <| besselDerivativeNearFromState (1288467790590547 / 16000000000000) 3 (IntervalRat.scale (743 / 8) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-32013047148 / 1000000000000) (-32013045889 / 1000000000000), orderedInterval (83148903894 / 1000000000000) (83148905153 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 3) <| besselDerivativeNearFromState (806263317873841 / 16000000000000) 3 (IntervalRat.scale (743 / 8) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (88660657470 / 1000000000000) (88660657471 / 1000000000000), orderedInterval (68204532765 / 1000000000000) (68204532766 / 1000000000000)))) (orderedInterval (3053046947 / 1000000000000) (3053047018 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 3) <| besselDerivativeNearFromState (433611093863247 / 16000000000000) 3 (IntervalRat.scale (743 / 8) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (58669506303 / 1000000000000) (58669508499 / 1000000000000), orderedInterval (-142685786790 / 1000000000000) (-142685784595 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 3) <| besselDerivativeNearFromState (1177338469210741 / 16000000000000) 3 (IntervalRat.scale (743 / 8) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-79781711172 / 1000000000000) (-79781693062 / 1000000000000), orderedInterval (48358734786 / 1000000000000) (48358752896 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 3) <| besselDerivativeNearFromState (1607555025945557 / 16000000000000) 3 (IntervalRat.scale (743 / 8) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (52808284243 / 1000000000000) (52808284244 / 1000000000000), orderedInterval (59298712159 / 1000000000000) (59298712160 / 1000000000000)))) (orderedInterval (6192792239 / 1000000000000) (6192792458 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 3) <| besselDerivativeNearFromState (679736682126159 / 16000000000000) 3 (IntervalRat.scale (743 / 8) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-80373631006 / 1000000000000) (-80373580116 / 1000000000000), orderedInterval (93278425903 / 1000000000000) (93278476793 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 3) <| besselDerivativeNearFromState (2763091874990639 / 16000000000000) 3 (IntervalRat.scale (743 / 8) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-38662852876 / 1000000000000) (-38662852875 / 1000000000000), orderedInterval (-46702656555 / 1000000000000) (-46702656554 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 3) <| besselDerivativeNearFromState (1845617319588001 / 16000000000000) 3 (IntervalRat.scale (743 / 8) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (7677540276 / 1000000000000) (7677540305 / 1000000000000), orderedInterval (-73925641917 / 1000000000000) (-73925641888 / 1000000000000)))) (orderedInterval (-50970256954 / 1000000000000) (-50970256830 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate211_chunkChecks3 :
    compactCertificate211.chunkChecks (3 : Fin 5) 0 9 = true :=
  compactCertificate211.chunkChecks_nine_of_three (3 : Fin 5) compactCertificate211_chunkChecks3_0
    compactCertificate211_chunkChecks3_1 compactCertificate211_chunkChecks3_2

theorem compactCertificate211_chunkChecks4_0 :
    compactCertificate211.chunkChecks (4 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 4) <| besselDerivativeNearFromState (743 / 8) 4 (IntervalRat.scale (743 / 8) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-45974559471 / 1000000000000) (-45974547009 / 1000000000000), orderedInterval (69102163628 / 1000000000000) (69102176090 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 4) <| besselDerivativeNearFromState (1094580874290443 / 16000000000000) 4 (IntervalRat.scale (743 / 8) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (7693350261 / 1000000000000) (7693350264 / 1000000000000), orderedInterval (96104193910 / 1000000000000) (96104193912 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 4) <| besselDerivativeNearFromState (353964965162219 / 3200000000000) 4 (IntervalRat.scale (743 / 8) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-75240715940 / 1000000000000) (-75240715935 / 1000000000000), orderedInterval (-9360541327 / 1000000000000) (-9360541322 / 1000000000000)))) (orderedInterval (-26499534127 / 1000000000000) (-26499529070 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 4) <| besselDerivativeNearFromState (319395969194401 / 16000000000000) 4 (IntervalRat.scale (743 / 8) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (169430443842 / 1000000000000) (169430445281 / 1000000000000), orderedInterval (-60601871452 / 1000000000000) (-60601870013 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 4) <| besselDerivativeNearFromState (857942500015597 / 16000000000000) 4 (IntervalRat.scale (743 / 8) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-91532045086 / 1000000000000) (-91532045085 / 1000000000000), orderedInterval (-58258038378 / 1000000000000) (-58258038377 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 4) <| besselDerivativeNearFromState (2329480781126649 / 16000000000000) 4 (IntervalRat.scale (743 / 8) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (63306803712 / 1000000000000) (63306805747 / 1000000000000), orderedInterval (-19318176442 / 1000000000000) (-19318174407 / 1000000000000)))) (orderedInterval (-27443781114 / 1000000000000) (-27443780187 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 4) <| besselDerivativeNearFromState (1715885000031937 / 16000000000000) 4 (IntervalRat.scale (743 / 8) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (72164489234 / 1000000000000) (72164489235 / 1000000000000), orderedInterval (26654002551 / 1000000000000) (26654002552 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 4) <| besselDerivativeNearFromState (2940198193877701 / 16000000000000) 4 (IntervalRat.scale (743 / 8) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (42503017289 / 1000000000000) (42503078517 / 1000000000000), orderedInterval (-40832430052 / 1000000000000) (-40832368824 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 4) <| besselDerivativeNearFromState (2165736682126159 / 16000000000000) 4 (IntervalRat.scale (743 / 8) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-59641724524 / 1000000000000) (-59641724523 / 1000000000000), orderedInterval (-33633188119 / 1000000000000) (-33633188118 / 1000000000000)))) (orderedInterval (-26436603590 / 1000000000000) (-26436574279 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate211_chunkChecks4_1 :
    compactCertificate211.chunkChecks (4 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 4) <| besselDerivativeNearFromState (3322797014564257 / 16000000000000) 4 (IntervalRat.scale (743 / 8) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (49701903896 / 1000000000000) (49701903897 / 1000000000000), orderedInterval (24276645707 / 1000000000000) (24276645708 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 4) <| besselDerivativeNearFromState (1918417750820953 / 16000000000000) 4 (IntervalRat.scale (743 / 8) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (70306409702 / 1000000000000) (70306409704 / 1000000000000), orderedInterval (18851251830 / 1000000000000) (18851251831 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 4) <| besselDerivativeNearFromState (3404265963847277 / 16000000000000) 4 (IntervalRat.scale (743 / 8) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-4200491054 / 1000000000000) (-4200491045 / 1000000000000), orderedInterval (54548551038 / 1000000000000) (54548551047 / 1000000000000)))) (orderedInterval (-221715612394 / 1000000000000) (-221715611557 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 4) <| besselDerivativeNearFromState (3180706853192513 / 16000000000000) 4 (IntervalRat.scale (743 / 8) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-56371668985 / 1000000000000) (-56371668755 / 1000000000000), orderedInterval (5104795486 / 1000000000000) (5104795716 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 4) <| besselDerivativeNearFromState (2269902494234129 / 16000000000000) 4 (IntervalRat.scale (743 / 8) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-64208865503 / 1000000000000) (-64208865502 / 1000000000000), orderedInterval (-18867653709 / 1000000000000) (-18867653707 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 4) <| besselDerivativeNearFromState (2573827500046791 / 16000000000000) 4 (IntervalRat.scale (743 / 8) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-62264750272 / 1000000000000) (-62264750266 / 1000000000000), orderedInterval (-8783118244 / 1000000000000) (-8783118238 / 1000000000000)))) (orderedInterval (-9008512786 / 1000000000000) (-9008512609 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 4) <| besselDerivativeNearFromState (2145789034533079 / 16000000000000) 4 (IntervalRat.scale (743 / 8) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (13160992527 / 1000000000000) (13160992620 / 1000000000000), orderedInterval (-67678584256 / 1000000000000) (-67678584163 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 4) <| besselDerivativeNearFromState (1895869687262659 / 16000000000000) 4 (IntervalRat.scale (743 / 8) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-7632770228 / 1000000000000) (-7632770199 / 1000000000000), orderedInterval (72932657541 / 1000000000000) (72932657570 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 4) <| besselDerivativeNearFromState (549496930439241 / 3200000000000) 4 (IntervalRat.scale (743 / 8) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (17126991395 / 1000000000000) (17126991650 / 1000000000000), orderedInterval (-58479656154 / 1000000000000) (-58479655898 / 1000000000000)))) (orderedInterval (6500664769 / 1000000000000) (6500664903 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate211_chunkChecks4_2 :
    compactCertificate211.chunkChecks (4 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 4) <| besselDerivativeNearFromState (1519937428034027 / 16000000000000) 4 (IntervalRat.scale (743 / 8) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (81801985280 / 1000000000000) (81801985297 / 1000000000000), orderedInterval (2712593240 / 1000000000000) (2712593258 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 4) <| besselDerivativeNearFromState (1288467790590547 / 16000000000000) 4 (IntervalRat.scale (743 / 8) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-32013047148 / 1000000000000) (-32013045889 / 1000000000000), orderedInterval (83148903894 / 1000000000000) (83148905153 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 4) <| besselDerivativeNearFromState (806263317873841 / 16000000000000) 4 (IntervalRat.scale (743 / 8) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (88660657470 / 1000000000000) (88660657471 / 1000000000000), orderedInterval (68204532765 / 1000000000000) (68204532766 / 1000000000000)))) (orderedInterval (-13106043486 / 1000000000000) (-13106043422 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 4) <| besselDerivativeNearFromState (433611093863247 / 16000000000000) 4 (IntervalRat.scale (743 / 8) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (58669506303 / 1000000000000) (58669508499 / 1000000000000), orderedInterval (-142685786790 / 1000000000000) (-142685784595 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 4) <| besselDerivativeNearFromState (1177338469210741 / 16000000000000) 4 (IntervalRat.scale (743 / 8) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-79781711172 / 1000000000000) (-79781693062 / 1000000000000), orderedInterval (48358734786 / 1000000000000) (48358752896 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 4) <| besselDerivativeNearFromState (1607555025945557 / 16000000000000) 4 (IntervalRat.scale (743 / 8) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (52808284243 / 1000000000000) (52808284244 / 1000000000000), orderedInterval (59298712159 / 1000000000000) (59298712160 / 1000000000000)))) (orderedInterval (-4970505658 / 1000000000000) (-4970505480 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 4) <| besselDerivativeNearFromState (679736682126159 / 16000000000000) 4 (IntervalRat.scale (743 / 8) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-80373631006 / 1000000000000) (-80373580116 / 1000000000000), orderedInterval (93278425903 / 1000000000000) (93278476793 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 4) <| besselDerivativeNearFromState (2763091874990639 / 16000000000000) 4 (IntervalRat.scale (743 / 8) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-38662852876 / 1000000000000) (-38662852875 / 1000000000000), orderedInterval (-46702656555 / 1000000000000) (-46702656554 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 4) <| besselDerivativeNearFromState (1845617319588001 / 16000000000000) 4 (IntervalRat.scale (743 / 8) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (7677540276 / 1000000000000) (7677540305 / 1000000000000), orderedInterval (-73925641917 / 1000000000000) (-73925641888 / 1000000000000)))) (orderedInterval (35268908916 / 1000000000000) (35268909077 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate211_chunkChecks4 :
    compactCertificate211.chunkChecks (4 : Fin 5) 0 9 = true :=
  compactCertificate211.chunkChecks_nine_of_three (4 : Fin 5) compactCertificate211_chunkChecks4_0
    compactCertificate211_chunkChecks4_1 compactCertificate211_chunkChecks4_2

theorem compactCertificate211_chunks :
    ∀ r : Fin 5, ∀ b, compactCertificate211.chunkCheck r b = true :=
  compactCertificate211.chunkChecks_all (by
    intro r
    fin_cases r
    · exact compactCertificate211_chunkChecks0
    · exact compactCertificate211_chunkChecks1
    · exact compactCertificate211_chunkChecks2
    · exact compactCertificate211_chunkChecks3
    · exact compactCertificate211_chunkChecks4)

theorem compactCertificate211_coefficient0 :
    compactCertificate211.coefficientCheck (0 : Fin 5) = true := by
  norm_num [CompactCertificate.coefficientCheck, intervalFinSumHull,
    compactCertificate211, rationalIntervalSubset, orderedInterval, Fin.sum_univ_succ]

theorem compactCertificate211_coefficient1 :
    compactCertificate211.coefficientCheck (1 : Fin 5) = true := by
  norm_num [CompactCertificate.coefficientCheck, intervalFinSumHull,
    compactCertificate211, rationalIntervalSubset, orderedInterval, Fin.sum_univ_succ]

theorem compactCertificate211_coefficient2 :
    compactCertificate211.coefficientCheck (2 : Fin 5) = true := by
  norm_num [CompactCertificate.coefficientCheck, intervalFinSumHull,
    compactCertificate211, rationalIntervalSubset, orderedInterval, Fin.sum_univ_succ]

theorem compactCertificate211_coefficient3 :
    compactCertificate211.coefficientCheck (3 : Fin 5) = true := by
  norm_num [CompactCertificate.coefficientCheck, intervalFinSumHull,
    compactCertificate211, rationalIntervalSubset, orderedInterval, Fin.sum_univ_succ]

theorem compactCertificate211_coefficient4 :
    compactCertificate211.coefficientCheck (4 : Fin 5) = true := by
  norm_num [CompactCertificate.coefficientCheck, intervalFinSumHull,
    compactCertificate211, rationalIntervalSubset, orderedInterval, Fin.sum_univ_succ]

theorem compactCertificate211_coefficients : ∀ r : Fin 5,
    compactCertificate211.coefficientCheck r = true := by
  intro r
  fin_cases r
  · exact compactCertificate211_coefficient0
  · exact compactCertificate211_coefficient1
  · exact compactCertificate211_coefficient2
  · exact compactCertificate211_coefficient3
  · exact compactCertificate211_coefficient4

theorem compactCertificate211_lower : (1 : ℚ) ≤ compactCertificate211.output.lo := by
  norm_num [CompactCertificate.output, CompactCertificate.interval,
    CompactCertificate.coefficientTargetNat, compactCertificate211, dualConstant,
    intervalTaylorSum, intervalPow, intervalSub, intervalMaxAbs, widenInterval,
    rationalErrorInterval, orderedInterval, IntervalRat.add, IntervalRat.mul, IntervalRat.scale,
    IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4]

theorem compactCertificate211_proves {t : ℝ} (ht : t ∈ compactCertificate211.interval) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t :=
  compactCertificate211.proves compactCertificate211_states compactCertificate211_chunks
    compactCertificate211_coefficients compactCertificate211_lower ht

end Erdos232
