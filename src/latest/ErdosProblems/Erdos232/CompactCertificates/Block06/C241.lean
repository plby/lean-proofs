/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, OpenAI Codex
-/
import ErdosProblems.Erdos232.CompactBase

open LeanCert.Core
namespace Erdos232

def compactCertificate241 : CompactCertificate where
  left := 117
  right := 235 / 2
  center := 469 / 4
  grid := fun i =>
    match i.val with
    | 0 => 37
    | 1 => 28
    | 2 => 44
    | 3 => 8
    | 4 => 22
    | 5 => 59
    | 6 => 43
    | 7 => 74
    | 8 => 54
    | 9 => 83
    | 10 => 48
    | 11 => 86
    | 12 => 80
    | 13 => 57
    | 14 => 65
    | 15 => 54
    | 16 => 48
    | 17 => 69
    | 18 => 38
    | 19 => 32
    | 20 => 20
    | 21 => 11
    | 22 => 30
    | 23 => 40
    | 24 => 17
    | 25 => 69
    | _ => 46
  point := fun i =>
    match i.val with
    | 0 => 469 / 4
    | 1 => 690926554565569 / 8000000000000
    | 2 => 223431451764577 / 1600000000000
    | 3 => 201610645426883 / 8000000000000
    | 4 => 541554552499751 / 8000000000000
    | 5 => 1470425957400267 / 8000000000000
    | 6 => 1083109104999971 / 8000000000000
    | 7 => 1855925912420783 / 8000000000000
    | 8 => 1367066627075597 / 8000000000000
    | 9 => 2097431762894531 / 8000000000000
    | 10 => 1210952792913899 / 8000000000000
    | 11 => 2148856981217191 / 8000000000000
    | 12 => 2007740934249379 / 8000000000000
    | 13 => 1432818667289107 / 8000000000000
    | 14 => 1624663657499253 / 8000000000000
    | 15 => 1354475177921957 / 8000000000000
    | 16 => 1196719896805097 / 8000000000000
    | 17 => 346856070492603 / 1600000000000
    | 18 => 959422145017441 / 8000000000000
    | 19 => 813312777640601 / 8000000000000
    | 20 => 508933372924403 / 8000000000000
    | 21 => 273706060594701 / 8000000000000
    | 22 => 743165197927103 / 8000000000000
    | 23 => 1014728542622431 / 8000000000000
    | 24 => 429066627075597 / 8000000000000
    | 25 => 1744132017995437 / 8000000000000
    | _ => 1164999357855683 / 8000000000000
  state := fun i =>
    match i.val with
    | 0 => (orderedInterval (-71834575289 / 1000000000000) (-71834574514 / 1000000000000), orderedInterval (16717976852 / 1000000000000) (16717977627 / 1000000000000))
    | 1 => (orderedInterval (-62468548698 / 1000000000000) (-62468449553 / 1000000000000), orderedInterval (59258780335 / 1000000000000) (59258879480 / 1000000000000))
    | 2 => (orderedInterval (54625291902 / 1000000000000) (54625346591 / 1000000000000), orderedInterval (-39880878792 / 1000000000000) (-39880824104 / 1000000000000))
    | 3 => (orderedInterval (119293817231 / 1000000000000) (119293817232 / 1000000000000), orderedInterval (102656545249 / 1000000000000) (102656545250 / 1000000000000))
    | 4 => (orderedInterval (-57692249859 / 1000000000000) (-57692227555 / 1000000000000), orderedInterval (78374861401 / 1000000000000) (78374883705 / 1000000000000))
    | 5 => (orderedInterval (40799895873 / 1000000000000) (40799938608 / 1000000000000), orderedInterval (-42525167427 / 1000000000000) (-42525124692 / 1000000000000))
    | 6 => (orderedInterval (-60626660719 / 1000000000000) (-60626660718 / 1000000000000), orderedInterval (-31816007143 / 1000000000000) (-31816007142 / 1000000000000))
    | 7 => (orderedInterval (15367690333 / 1000000000000) (15367690334 / 1000000000000), orderedInterval (50046811458 / 1000000000000) (50046811459 / 1000000000000))
    | 8 => (orderedInterval (54928313613 / 1000000000000) (54928325873 / 1000000000000), orderedInterval (-26775273283 / 1000000000000) (-26775261024 / 1000000000000))
    | 9 => (orderedInterval (-39497948482 / 1000000000000) (-39497845290 / 1000000000000), orderedInterval (29538852155 / 1000000000000) (29538955347 / 1000000000000))
    | 10 => (orderedInterval (63378109711 / 1000000000000) (63378109713 / 1000000000000), orderedInterval (13536158732 / 1000000000000) (13536158734 / 1000000000000))
    | 11 => (orderedInterval (-34407666540 / 1000000000000) (-34407632067 / 1000000000000), orderedInterval (34505159899 / 1000000000000) (34505194372 / 1000000000000))
    | 12 => (orderedInterval (20771428297 / 1000000000000) (20771428298 / 1000000000000), orderedInterval (45841208016 / 1000000000000) (45841208017 / 1000000000000))
    | 13 => (orderedInterval (-43437840982 / 1000000000000) (-43437840981 / 1000000000000), orderedInterval (-40715680390 / 1000000000000) (-40715680389 / 1000000000000))
    | 14 => (orderedInterval (18448832376 / 1000000000000) (18448832778 / 1000000000000), orderedInterval (-52907742628 / 1000000000000) (-52907742227 / 1000000000000))
    | 15 => (orderedInterval (26564359556 / 1000000000000) (26564359557 / 1000000000000), orderedInterval (55188559186 / 1000000000000) (55188559187 / 1000000000000))
    | 16 => (orderedInterval (-26713669106 / 1000000000000) (-26713667531 / 1000000000000), orderedInterval (59605338814 / 1000000000000) (59605340388 / 1000000000000))
    | 17 => (orderedInterval (-38872997033 / 1000000000000) (-38872997032 / 1000000000000), orderedInterval (-37666541012 / 1000000000000) (-37666541011 / 1000000000000))
    | 18 => (orderedInterval (70783864637 / 1000000000000) (70783864639 / 1000000000000), orderedInterval (16966516860 / 1000000000000) (16966516861 / 1000000000000))
    | 19 => (orderedInterval (74429084428 / 1000000000000) (74429087319 / 1000000000000), orderedInterval (-27240662708 / 1000000000000) (-27240659818 / 1000000000000))
    | 20 => (orderedInterval (100033733928 / 1000000000000) (100033733952 / 1000000000000), orderedInterval (-531653808 / 1000000000000) (-531653783 / 1000000000000))
    | 21 => (orderedInterval (-57788248642 / 1000000000000) (-57788248641 / 1000000000000), orderedInterval (-122724215794 / 1000000000000) (-122724215793 / 1000000000000))
    | 22 => (orderedInterval (-44538075517 / 1000000000000) (-44538065357 / 1000000000000), orderedInterval (70021263502 / 1000000000000) (70021273662 / 1000000000000))
    | 23 => (orderedInterval (65498687655 / 1000000000000) (65498692978 / 1000000000000), orderedInterval (-27256875476 / 1000000000000) (-27256870153 / 1000000000000))
    | 24 => (orderedInterval (-92220007043 / 1000000000000) (-92220007042 / 1000000000000), orderedInterval (-57149838440 / 1000000000000) (-57149838439 / 1000000000000))
    | 25 => (orderedInterval (-48405088901 / 1000000000000) (-48405071987 / 1000000000000), orderedInterval (24131757707 / 1000000000000) (24131774621 / 1000000000000))
    | _ => (orderedInterval (62648471524 / 1000000000000) (62648474440 / 1000000000000), orderedInterval (-21352476854 / 1000000000000) (-21352473937 / 1000000000000))
  chunkTarget := fun r b =>
    match r.val with
    | 0 =>
      match b.val with
      | 0 => orderedInterval (-25849322219 / 1000000000000) (-25849317770 / 1000000000000)
      | 1 => orderedInterval (-6301151107 / 1000000000000) (-6301147239 / 1000000000000)
      | 2 => orderedInterval (853507907 / 1000000000000) (853508210 / 1000000000000)
      | 3 => orderedInterval (6822834050 / 1000000000000) (6822857334 / 1000000000000)
      | 4 => orderedInterval (-4575956845 / 1000000000000) (-4575956828 / 1000000000000)
      | 5 => orderedInterval (840188603 / 1000000000000) (840188705 / 1000000000000)
      | 6 => orderedInterval (-12273862737 / 1000000000000) (-12273862542 / 1000000000000)
      | 7 => orderedInterval (-2942250109 / 1000000000000) (-2942249456 / 1000000000000)
      | _ => orderedInterval (-8370189273 / 1000000000000) (-8370187316 / 1000000000000)
    | 1 =>
      match b.val with
      | 0 => orderedInterval (4245909387 / 1000000000000) (4245914206 / 1000000000000)
      | 1 => orderedInterval (6151821689 / 1000000000000) (6151826938 / 1000000000000)
      | 2 => orderedInterval (-3997361509 / 1000000000000) (-3997361065 / 1000000000000)
      | 3 => orderedInterval (795359198 / 1000000000000) (795411522 / 1000000000000)
      | 4 => orderedInterval (-7188901419 / 1000000000000) (-7188901392 / 1000000000000)
      | 5 => orderedInterval (-5214696530 / 1000000000000) (-5214696398 / 1000000000000)
      | 6 => orderedInterval (-1447296545 / 1000000000000) (-1447296374 / 1000000000000)
      | 7 => orderedInterval (1662460493 / 1000000000000) (1662461131 / 1000000000000)
      | _ => orderedInterval (1165655919 / 1000000000000) (1165659205 / 1000000000000)
    | 2 =>
      match b.val with
      | 0 => orderedInterval (24205418490 / 1000000000000) (24205423903 / 1000000000000)
      | 1 => orderedInterval (7837116350 / 1000000000000) (7837124155 / 1000000000000)
      | 2 => orderedInterval (-930016507 / 1000000000000) (-930015853 / 1000000000000)
      | 3 => orderedInterval (-17254469151 / 1000000000000) (-17254351099 / 1000000000000)
      | 4 => orderedInterval (11643830545 / 1000000000000) (11643830590 / 1000000000000)
      | 5 => orderedInterval (318913390 / 1000000000000) (318913563 / 1000000000000)
      | 6 => orderedInterval (14061450963 / 1000000000000) (14061451114 / 1000000000000)
      | 7 => orderedInterval (5135265449 / 1000000000000) (5135266090 / 1000000000000)
      | _ => orderedInterval (4615415169 / 1000000000000) (4615420869 / 1000000000000)
    | 3 =>
      match b.val with
      | 0 => orderedInterval (-3099596989 / 1000000000000) (-3099590833 / 1000000000000)
      | 1 => orderedInterval (-12251957558 / 1000000000000) (-12251945599 / 1000000000000)
      | 2 => orderedInterval (13967845195 / 1000000000000) (13967846155 / 1000000000000)
      | 3 => orderedInterval (-2302876131 / 1000000000000) (-2302610763 / 1000000000000)
      | 4 => orderedInterval (20347508849 / 1000000000000) (20347508924 / 1000000000000)
      | 5 => orderedInterval (11257137028 / 1000000000000) (11257137254 / 1000000000000)
      | 6 => orderedInterval (1780620036 / 1000000000000) (1780620170 / 1000000000000)
      | 7 => orderedInterval (-1954572123 / 1000000000000) (-1954571473 / 1000000000000)
      | _ => orderedInterval (4946636187 / 1000000000000) (4946646239 / 1000000000000)
    | _ =>
      match b.val with
      | 0 => orderedInterval (-22139758299 / 1000000000000) (-22139751145 / 1000000000000)
      | 1 => orderedInterval (-17542941762 / 1000000000000) (-17542923073 / 1000000000000)
      | 2 => orderedInterval (-1513481564 / 1000000000000) (-1513480142 / 1000000000000)
      | 3 => orderedInterval (53817075276 / 1000000000000) (53817674136 / 1000000000000)
      | 4 => orderedInterval (-31421251042 / 1000000000000) (-31421250911 / 1000000000000)
      | 5 => orderedInterval (-6439035925 / 1000000000000) (-6439035623 / 1000000000000)
      | 6 => orderedInterval (-14515897378 / 1000000000000) (-14515897258 / 1000000000000)
      | 7 => orderedInterval (-6435366477 / 1000000000000) (-6435365802 / 1000000000000)
      | _ => orderedInterval (19022457055 / 1000000000000) (19022475150 / 1000000000000)
  coefficientTarget := fun i =>
    match i.val with
    | 0 => orderedInterval (-51796201730 / 1000000000000) (-51796166902 / 1000000000000)
    | 1 => orderedInterval (-3827049317 / 1000000000000) (-3826982227 / 1000000000000)
    | 2 => orderedInterval (49632924698 / 1000000000000) (49633063332 / 1000000000000)
    | 3 => orderedInterval (32690744494 / 1000000000000) (32691040074 / 1000000000000)
    | _ => orderedInterval (-27168200116 / 1000000000000) (-27167554668 / 1000000000000)

theorem compactCertificate241_stateChecks0 :
    compactCertificate241.stateChecks 0 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 37 12 (469 / 4)) (orderedInterval (-71834575289 / 1000000000000) (-71834574514 / 1000000000000), orderedInterval (16717976852 / 1000000000000) (16717977627 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 28 12 (690926554565569 / 8000000000000)) (orderedInterval (-62468548698 / 1000000000000) (-62468449553 / 1000000000000), orderedInterval (59258780335 / 1000000000000) (59258879480 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 44 12 (223431451764577 / 1600000000000)) (orderedInterval (54625291902 / 1000000000000) (54625346591 / 1000000000000), orderedInterval (-39880878792 / 1000000000000) (-39880824104 / 1000000000000))) = true
  norm_num [besselStateAtRationalPoint, besselIntervalStepZero,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, besselZeroTransition,
    besselInitial, besselGridStateAt, besselGridStateBlock00, besselGridStateBlock01,
    besselGridStateBlock02, besselGridStateBlock03, besselGridStateBlock04,
    besselGridStateBlock05, besselGridStateBlock06, besselGridStateBlock07,
    besselGridStateBlock08, besselGridStateBlock09, besselGridStateBlock10,
    besselGridStateBlock11, besselGridStateBlock12, besselGridStateBlock13,
    besselGridStateBlock14, besselGridState008, besselGridState011, besselGridState017, besselGridState020, besselGridState022, besselGridState028, besselGridState030, besselGridState032, besselGridState037, besselGridState038, besselGridState040, besselGridState043, besselGridState044, besselGridState046, besselGridState048, besselGridState054, besselGridState057, besselGridState059, besselGridState065, besselGridState069, besselGridState074, besselGridState080, besselGridState083, besselGridState086, besselStateSubset, linearInterval, widenInterval,
    rationalErrorInterval, rationalIntervalSubset, orderedInterval, Finset.sum_range_succ,
    IntervalRat.add, IntervalRat.mul, IntervalRat.scale, IntervalRat.singleton]

theorem compactCertificate241_stateChecks1 :
    compactCertificate241.stateChecks 3 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 8 12 (201610645426883 / 8000000000000)) (orderedInterval (119293817231 / 1000000000000) (119293817232 / 1000000000000), orderedInterval (102656545249 / 1000000000000) (102656545250 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 22 12 (541554552499751 / 8000000000000)) (orderedInterval (-57692249859 / 1000000000000) (-57692227555 / 1000000000000), orderedInterval (78374861401 / 1000000000000) (78374883705 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 59 12 (1470425957400267 / 8000000000000)) (orderedInterval (40799895873 / 1000000000000) (40799938608 / 1000000000000), orderedInterval (-42525167427 / 1000000000000) (-42525124692 / 1000000000000))) = true
  norm_num [besselStateAtRationalPoint, besselIntervalStepZero,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, besselZeroTransition,
    besselInitial, besselGridStateAt, besselGridStateBlock00, besselGridStateBlock01,
    besselGridStateBlock02, besselGridStateBlock03, besselGridStateBlock04,
    besselGridStateBlock05, besselGridStateBlock06, besselGridStateBlock07,
    besselGridStateBlock08, besselGridStateBlock09, besselGridStateBlock10,
    besselGridStateBlock11, besselGridStateBlock12, besselGridStateBlock13,
    besselGridStateBlock14, besselGridState008, besselGridState011, besselGridState017, besselGridState020, besselGridState022, besselGridState028, besselGridState030, besselGridState032, besselGridState037, besselGridState038, besselGridState040, besselGridState043, besselGridState044, besselGridState046, besselGridState048, besselGridState054, besselGridState057, besselGridState059, besselGridState065, besselGridState069, besselGridState074, besselGridState080, besselGridState083, besselGridState086, besselStateSubset, linearInterval, widenInterval,
    rationalErrorInterval, rationalIntervalSubset, orderedInterval, Finset.sum_range_succ,
    IntervalRat.add, IntervalRat.mul, IntervalRat.scale, IntervalRat.singleton]

theorem compactCertificate241_stateChecks2 :
    compactCertificate241.stateChecks 6 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 43 12 (1083109104999971 / 8000000000000)) (orderedInterval (-60626660719 / 1000000000000) (-60626660718 / 1000000000000), orderedInterval (-31816007143 / 1000000000000) (-31816007142 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 74 12 (1855925912420783 / 8000000000000)) (orderedInterval (15367690333 / 1000000000000) (15367690334 / 1000000000000), orderedInterval (50046811458 / 1000000000000) (50046811459 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 54 12 (1367066627075597 / 8000000000000)) (orderedInterval (54928313613 / 1000000000000) (54928325873 / 1000000000000), orderedInterval (-26775273283 / 1000000000000) (-26775261024 / 1000000000000))) = true
  norm_num [besselStateAtRationalPoint, besselIntervalStepZero,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, besselZeroTransition,
    besselInitial, besselGridStateAt, besselGridStateBlock00, besselGridStateBlock01,
    besselGridStateBlock02, besselGridStateBlock03, besselGridStateBlock04,
    besselGridStateBlock05, besselGridStateBlock06, besselGridStateBlock07,
    besselGridStateBlock08, besselGridStateBlock09, besselGridStateBlock10,
    besselGridStateBlock11, besselGridStateBlock12, besselGridStateBlock13,
    besselGridStateBlock14, besselGridState008, besselGridState011, besselGridState017, besselGridState020, besselGridState022, besselGridState028, besselGridState030, besselGridState032, besselGridState037, besselGridState038, besselGridState040, besselGridState043, besselGridState044, besselGridState046, besselGridState048, besselGridState054, besselGridState057, besselGridState059, besselGridState065, besselGridState069, besselGridState074, besselGridState080, besselGridState083, besselGridState086, besselStateSubset, linearInterval, widenInterval,
    rationalErrorInterval, rationalIntervalSubset, orderedInterval, Finset.sum_range_succ,
    IntervalRat.add, IntervalRat.mul, IntervalRat.scale, IntervalRat.singleton]

theorem compactCertificate241_stateChecks3 :
    compactCertificate241.stateChecks 9 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 83 12 (2097431762894531 / 8000000000000)) (orderedInterval (-39497948482 / 1000000000000) (-39497845290 / 1000000000000), orderedInterval (29538852155 / 1000000000000) (29538955347 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 48 12 (1210952792913899 / 8000000000000)) (orderedInterval (63378109711 / 1000000000000) (63378109713 / 1000000000000), orderedInterval (13536158732 / 1000000000000) (13536158734 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 86 12 (2148856981217191 / 8000000000000)) (orderedInterval (-34407666540 / 1000000000000) (-34407632067 / 1000000000000), orderedInterval (34505159899 / 1000000000000) (34505194372 / 1000000000000))) = true
  norm_num [besselStateAtRationalPoint, besselIntervalStepZero,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, besselZeroTransition,
    besselInitial, besselGridStateAt, besselGridStateBlock00, besselGridStateBlock01,
    besselGridStateBlock02, besselGridStateBlock03, besselGridStateBlock04,
    besselGridStateBlock05, besselGridStateBlock06, besselGridStateBlock07,
    besselGridStateBlock08, besselGridStateBlock09, besselGridStateBlock10,
    besselGridStateBlock11, besselGridStateBlock12, besselGridStateBlock13,
    besselGridStateBlock14, besselGridState008, besselGridState011, besselGridState017, besselGridState020, besselGridState022, besselGridState028, besselGridState030, besselGridState032, besselGridState037, besselGridState038, besselGridState040, besselGridState043, besselGridState044, besselGridState046, besselGridState048, besselGridState054, besselGridState057, besselGridState059, besselGridState065, besselGridState069, besselGridState074, besselGridState080, besselGridState083, besselGridState086, besselStateSubset, linearInterval, widenInterval,
    rationalErrorInterval, rationalIntervalSubset, orderedInterval, Finset.sum_range_succ,
    IntervalRat.add, IntervalRat.mul, IntervalRat.scale, IntervalRat.singleton]

theorem compactCertificate241_stateChecks4 :
    compactCertificate241.stateChecks 12 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 80 12 (2007740934249379 / 8000000000000)) (orderedInterval (20771428297 / 1000000000000) (20771428298 / 1000000000000), orderedInterval (45841208016 / 1000000000000) (45841208017 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 57 12 (1432818667289107 / 8000000000000)) (orderedInterval (-43437840982 / 1000000000000) (-43437840981 / 1000000000000), orderedInterval (-40715680390 / 1000000000000) (-40715680389 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 65 12 (1624663657499253 / 8000000000000)) (orderedInterval (18448832376 / 1000000000000) (18448832778 / 1000000000000), orderedInterval (-52907742628 / 1000000000000) (-52907742227 / 1000000000000))) = true
  norm_num [besselStateAtRationalPoint, besselIntervalStepZero,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, besselZeroTransition,
    besselInitial, besselGridStateAt, besselGridStateBlock00, besselGridStateBlock01,
    besselGridStateBlock02, besselGridStateBlock03, besselGridStateBlock04,
    besselGridStateBlock05, besselGridStateBlock06, besselGridStateBlock07,
    besselGridStateBlock08, besselGridStateBlock09, besselGridStateBlock10,
    besselGridStateBlock11, besselGridStateBlock12, besselGridStateBlock13,
    besselGridStateBlock14, besselGridState008, besselGridState011, besselGridState017, besselGridState020, besselGridState022, besselGridState028, besselGridState030, besselGridState032, besselGridState037, besselGridState038, besselGridState040, besselGridState043, besselGridState044, besselGridState046, besselGridState048, besselGridState054, besselGridState057, besselGridState059, besselGridState065, besselGridState069, besselGridState074, besselGridState080, besselGridState083, besselGridState086, besselStateSubset, linearInterval, widenInterval,
    rationalErrorInterval, rationalIntervalSubset, orderedInterval, Finset.sum_range_succ,
    IntervalRat.add, IntervalRat.mul, IntervalRat.scale, IntervalRat.singleton]

theorem compactCertificate241_stateChecks5 :
    compactCertificate241.stateChecks 15 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 54 12 (1354475177921957 / 8000000000000)) (orderedInterval (26564359556 / 1000000000000) (26564359557 / 1000000000000), orderedInterval (55188559186 / 1000000000000) (55188559187 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 48 12 (1196719896805097 / 8000000000000)) (orderedInterval (-26713669106 / 1000000000000) (-26713667531 / 1000000000000), orderedInterval (59605338814 / 1000000000000) (59605340388 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 69 12 (346856070492603 / 1600000000000)) (orderedInterval (-38872997033 / 1000000000000) (-38872997032 / 1000000000000), orderedInterval (-37666541012 / 1000000000000) (-37666541011 / 1000000000000))) = true
  norm_num [besselStateAtRationalPoint, besselIntervalStepZero,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, besselZeroTransition,
    besselInitial, besselGridStateAt, besselGridStateBlock00, besselGridStateBlock01,
    besselGridStateBlock02, besselGridStateBlock03, besselGridStateBlock04,
    besselGridStateBlock05, besselGridStateBlock06, besselGridStateBlock07,
    besselGridStateBlock08, besselGridStateBlock09, besselGridStateBlock10,
    besselGridStateBlock11, besselGridStateBlock12, besselGridStateBlock13,
    besselGridStateBlock14, besselGridState008, besselGridState011, besselGridState017, besselGridState020, besselGridState022, besselGridState028, besselGridState030, besselGridState032, besselGridState037, besselGridState038, besselGridState040, besselGridState043, besselGridState044, besselGridState046, besselGridState048, besselGridState054, besselGridState057, besselGridState059, besselGridState065, besselGridState069, besselGridState074, besselGridState080, besselGridState083, besselGridState086, besselStateSubset, linearInterval, widenInterval,
    rationalErrorInterval, rationalIntervalSubset, orderedInterval, Finset.sum_range_succ,
    IntervalRat.add, IntervalRat.mul, IntervalRat.scale, IntervalRat.singleton]

theorem compactCertificate241_stateChecks6 :
    compactCertificate241.stateChecks 18 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 38 12 (959422145017441 / 8000000000000)) (orderedInterval (70783864637 / 1000000000000) (70783864639 / 1000000000000), orderedInterval (16966516860 / 1000000000000) (16966516861 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 32 12 (813312777640601 / 8000000000000)) (orderedInterval (74429084428 / 1000000000000) (74429087319 / 1000000000000), orderedInterval (-27240662708 / 1000000000000) (-27240659818 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 20 12 (508933372924403 / 8000000000000)) (orderedInterval (100033733928 / 1000000000000) (100033733952 / 1000000000000), orderedInterval (-531653808 / 1000000000000) (-531653783 / 1000000000000))) = true
  norm_num [besselStateAtRationalPoint, besselIntervalStepZero,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, besselZeroTransition,
    besselInitial, besselGridStateAt, besselGridStateBlock00, besselGridStateBlock01,
    besselGridStateBlock02, besselGridStateBlock03, besselGridStateBlock04,
    besselGridStateBlock05, besselGridStateBlock06, besselGridStateBlock07,
    besselGridStateBlock08, besselGridStateBlock09, besselGridStateBlock10,
    besselGridStateBlock11, besselGridStateBlock12, besselGridStateBlock13,
    besselGridStateBlock14, besselGridState008, besselGridState011, besselGridState017, besselGridState020, besselGridState022, besselGridState028, besselGridState030, besselGridState032, besselGridState037, besselGridState038, besselGridState040, besselGridState043, besselGridState044, besselGridState046, besselGridState048, besselGridState054, besselGridState057, besselGridState059, besselGridState065, besselGridState069, besselGridState074, besselGridState080, besselGridState083, besselGridState086, besselStateSubset, linearInterval, widenInterval,
    rationalErrorInterval, rationalIntervalSubset, orderedInterval, Finset.sum_range_succ,
    IntervalRat.add, IntervalRat.mul, IntervalRat.scale, IntervalRat.singleton]

theorem compactCertificate241_stateChecks7 :
    compactCertificate241.stateChecks 21 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 11 12 (273706060594701 / 8000000000000)) (orderedInterval (-57788248642 / 1000000000000) (-57788248641 / 1000000000000), orderedInterval (-122724215794 / 1000000000000) (-122724215793 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 30 12 (743165197927103 / 8000000000000)) (orderedInterval (-44538075517 / 1000000000000) (-44538065357 / 1000000000000), orderedInterval (70021263502 / 1000000000000) (70021273662 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 40 12 (1014728542622431 / 8000000000000)) (orderedInterval (65498687655 / 1000000000000) (65498692978 / 1000000000000), orderedInterval (-27256875476 / 1000000000000) (-27256870153 / 1000000000000))) = true
  norm_num [besselStateAtRationalPoint, besselIntervalStepZero,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, besselZeroTransition,
    besselInitial, besselGridStateAt, besselGridStateBlock00, besselGridStateBlock01,
    besselGridStateBlock02, besselGridStateBlock03, besselGridStateBlock04,
    besselGridStateBlock05, besselGridStateBlock06, besselGridStateBlock07,
    besselGridStateBlock08, besselGridStateBlock09, besselGridStateBlock10,
    besselGridStateBlock11, besselGridStateBlock12, besselGridStateBlock13,
    besselGridStateBlock14, besselGridState008, besselGridState011, besselGridState017, besselGridState020, besselGridState022, besselGridState028, besselGridState030, besselGridState032, besselGridState037, besselGridState038, besselGridState040, besselGridState043, besselGridState044, besselGridState046, besselGridState048, besselGridState054, besselGridState057, besselGridState059, besselGridState065, besselGridState069, besselGridState074, besselGridState080, besselGridState083, besselGridState086, besselStateSubset, linearInterval, widenInterval,
    rationalErrorInterval, rationalIntervalSubset, orderedInterval, Finset.sum_range_succ,
    IntervalRat.add, IntervalRat.mul, IntervalRat.scale, IntervalRat.singleton]

theorem compactCertificate241_stateChecks8 :
    compactCertificate241.stateChecks 24 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 17 12 (429066627075597 / 8000000000000)) (orderedInterval (-92220007043 / 1000000000000) (-92220007042 / 1000000000000), orderedInterval (-57149838440 / 1000000000000) (-57149838439 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 69 12 (1744132017995437 / 8000000000000)) (orderedInterval (-48405088901 / 1000000000000) (-48405071987 / 1000000000000), orderedInterval (24131757707 / 1000000000000) (24131774621 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 46 12 (1164999357855683 / 8000000000000)) (orderedInterval (62648471524 / 1000000000000) (62648474440 / 1000000000000), orderedInterval (-21352476854 / 1000000000000) (-21352473937 / 1000000000000))) = true
  norm_num [besselStateAtRationalPoint, besselIntervalStepZero,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, besselZeroTransition,
    besselInitial, besselGridStateAt, besselGridStateBlock00, besselGridStateBlock01,
    besselGridStateBlock02, besselGridStateBlock03, besselGridStateBlock04,
    besselGridStateBlock05, besselGridStateBlock06, besselGridStateBlock07,
    besselGridStateBlock08, besselGridStateBlock09, besselGridStateBlock10,
    besselGridStateBlock11, besselGridStateBlock12, besselGridStateBlock13,
    besselGridStateBlock14, besselGridState008, besselGridState011, besselGridState017, besselGridState020, besselGridState022, besselGridState028, besselGridState030, besselGridState032, besselGridState037, besselGridState038, besselGridState040, besselGridState043, besselGridState044, besselGridState046, besselGridState048, besselGridState054, besselGridState057, besselGridState059, besselGridState065, besselGridState069, besselGridState074, besselGridState080, besselGridState083, besselGridState086, besselStateSubset, linearInterval, widenInterval,
    rationalErrorInterval, rationalIntervalSubset, orderedInterval, Finset.sum_range_succ,
    IntervalRat.add, IntervalRat.mul, IntervalRat.scale, IntervalRat.singleton]

theorem compactCertificate241_states : ∀ j,
    BesselStateValid (compactCertificate241.point j) (compactCertificate241.state j) :=
  compactCertificate241.statesValid_of_checks3 compactCertificate241_stateChecks0
    compactCertificate241_stateChecks1 compactCertificate241_stateChecks2
    compactCertificate241_stateChecks3 compactCertificate241_stateChecks4
    compactCertificate241_stateChecks5 compactCertificate241_stateChecks6
    compactCertificate241_stateChecks7 compactCertificate241_stateChecks8

theorem compactCertificate241_chunkChecks0_0 :
    compactCertificate241.chunkChecks (0 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 0) <| besselDerivativeNearFromState (469 / 4) 0 (IntervalRat.scale (469 / 4) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-71834575289 / 1000000000000) (-71834574514 / 1000000000000), orderedInterval (16717976852 / 1000000000000) (16717977627 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 0) <| besselDerivativeNearFromState (690926554565569 / 8000000000000) 0 (IntervalRat.scale (469 / 4) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-62468548698 / 1000000000000) (-62468449553 / 1000000000000), orderedInterval (59258780335 / 1000000000000) (59258879480 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 0) <| besselDerivativeNearFromState (223431451764577 / 1600000000000) 0 (IntervalRat.scale (469 / 4) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (54625291902 / 1000000000000) (54625346591 / 1000000000000), orderedInterval (-39880878792 / 1000000000000) (-39880824104 / 1000000000000)))) (orderedInterval (-25849322219 / 1000000000000) (-25849317770 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 0) <| besselDerivativeNearFromState (201610645426883 / 8000000000000) 0 (IntervalRat.scale (469 / 4) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (119293817231 / 1000000000000) (119293817232 / 1000000000000), orderedInterval (102656545249 / 1000000000000) (102656545250 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 0) <| besselDerivativeNearFromState (541554552499751 / 8000000000000) 0 (IntervalRat.scale (469 / 4) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-57692249859 / 1000000000000) (-57692227555 / 1000000000000), orderedInterval (78374861401 / 1000000000000) (78374883705 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 0) <| besselDerivativeNearFromState (1470425957400267 / 8000000000000) 0 (IntervalRat.scale (469 / 4) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (40799895873 / 1000000000000) (40799938608 / 1000000000000), orderedInterval (-42525167427 / 1000000000000) (-42525124692 / 1000000000000)))) (orderedInterval (-6301151107 / 1000000000000) (-6301147239 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 0) <| besselDerivativeNearFromState (1083109104999971 / 8000000000000) 0 (IntervalRat.scale (469 / 4) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-60626660719 / 1000000000000) (-60626660718 / 1000000000000), orderedInterval (-31816007143 / 1000000000000) (-31816007142 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 0) <| besselDerivativeNearFromState (1855925912420783 / 8000000000000) 0 (IntervalRat.scale (469 / 4) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (15367690333 / 1000000000000) (15367690334 / 1000000000000), orderedInterval (50046811458 / 1000000000000) (50046811459 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 0) <| besselDerivativeNearFromState (1367066627075597 / 8000000000000) 0 (IntervalRat.scale (469 / 4) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (54928313613 / 1000000000000) (54928325873 / 1000000000000), orderedInterval (-26775273283 / 1000000000000) (-26775261024 / 1000000000000)))) (orderedInterval (853507907 / 1000000000000) (853508210 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate241_chunkChecks0_1 :
    compactCertificate241.chunkChecks (0 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 0) <| besselDerivativeNearFromState (2097431762894531 / 8000000000000) 0 (IntervalRat.scale (469 / 4) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-39497948482 / 1000000000000) (-39497845290 / 1000000000000), orderedInterval (29538852155 / 1000000000000) (29538955347 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 0) <| besselDerivativeNearFromState (1210952792913899 / 8000000000000) 0 (IntervalRat.scale (469 / 4) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (63378109711 / 1000000000000) (63378109713 / 1000000000000), orderedInterval (13536158732 / 1000000000000) (13536158734 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 0) <| besselDerivativeNearFromState (2148856981217191 / 8000000000000) 0 (IntervalRat.scale (469 / 4) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-34407666540 / 1000000000000) (-34407632067 / 1000000000000), orderedInterval (34505159899 / 1000000000000) (34505194372 / 1000000000000)))) (orderedInterval (6822834050 / 1000000000000) (6822857334 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 0) <| besselDerivativeNearFromState (2007740934249379 / 8000000000000) 0 (IntervalRat.scale (469 / 4) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (20771428297 / 1000000000000) (20771428298 / 1000000000000), orderedInterval (45841208016 / 1000000000000) (45841208017 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 0) <| besselDerivativeNearFromState (1432818667289107 / 8000000000000) 0 (IntervalRat.scale (469 / 4) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-43437840982 / 1000000000000) (-43437840981 / 1000000000000), orderedInterval (-40715680390 / 1000000000000) (-40715680389 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 0) <| besselDerivativeNearFromState (1624663657499253 / 8000000000000) 0 (IntervalRat.scale (469 / 4) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (18448832376 / 1000000000000) (18448832778 / 1000000000000), orderedInterval (-52907742628 / 1000000000000) (-52907742227 / 1000000000000)))) (orderedInterval (-4575956845 / 1000000000000) (-4575956828 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 0) <| besselDerivativeNearFromState (1354475177921957 / 8000000000000) 0 (IntervalRat.scale (469 / 4) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (26564359556 / 1000000000000) (26564359557 / 1000000000000), orderedInterval (55188559186 / 1000000000000) (55188559187 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 0) <| besselDerivativeNearFromState (1196719896805097 / 8000000000000) 0 (IntervalRat.scale (469 / 4) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-26713669106 / 1000000000000) (-26713667531 / 1000000000000), orderedInterval (59605338814 / 1000000000000) (59605340388 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 0) <| besselDerivativeNearFromState (346856070492603 / 1600000000000) 0 (IntervalRat.scale (469 / 4) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-38872997033 / 1000000000000) (-38872997032 / 1000000000000), orderedInterval (-37666541012 / 1000000000000) (-37666541011 / 1000000000000)))) (orderedInterval (840188603 / 1000000000000) (840188705 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate241_chunkChecks0_2 :
    compactCertificate241.chunkChecks (0 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 0) <| besselDerivativeNearFromState (959422145017441 / 8000000000000) 0 (IntervalRat.scale (469 / 4) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (70783864637 / 1000000000000) (70783864639 / 1000000000000), orderedInterval (16966516860 / 1000000000000) (16966516861 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 0) <| besselDerivativeNearFromState (813312777640601 / 8000000000000) 0 (IntervalRat.scale (469 / 4) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (74429084428 / 1000000000000) (74429087319 / 1000000000000), orderedInterval (-27240662708 / 1000000000000) (-27240659818 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 0) <| besselDerivativeNearFromState (508933372924403 / 8000000000000) 0 (IntervalRat.scale (469 / 4) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (100033733928 / 1000000000000) (100033733952 / 1000000000000), orderedInterval (-531653808 / 1000000000000) (-531653783 / 1000000000000)))) (orderedInterval (-12273862737 / 1000000000000) (-12273862542 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 0) <| besselDerivativeNearFromState (273706060594701 / 8000000000000) 0 (IntervalRat.scale (469 / 4) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-57788248642 / 1000000000000) (-57788248641 / 1000000000000), orderedInterval (-122724215794 / 1000000000000) (-122724215793 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 0) <| besselDerivativeNearFromState (743165197927103 / 8000000000000) 0 (IntervalRat.scale (469 / 4) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-44538075517 / 1000000000000) (-44538065357 / 1000000000000), orderedInterval (70021263502 / 1000000000000) (70021273662 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 0) <| besselDerivativeNearFromState (1014728542622431 / 8000000000000) 0 (IntervalRat.scale (469 / 4) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (65498687655 / 1000000000000) (65498692978 / 1000000000000), orderedInterval (-27256875476 / 1000000000000) (-27256870153 / 1000000000000)))) (orderedInterval (-2942250109 / 1000000000000) (-2942249456 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 0) <| besselDerivativeNearFromState (429066627075597 / 8000000000000) 0 (IntervalRat.scale (469 / 4) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-92220007043 / 1000000000000) (-92220007042 / 1000000000000), orderedInterval (-57149838440 / 1000000000000) (-57149838439 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 0) <| besselDerivativeNearFromState (1744132017995437 / 8000000000000) 0 (IntervalRat.scale (469 / 4) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-48405088901 / 1000000000000) (-48405071987 / 1000000000000), orderedInterval (24131757707 / 1000000000000) (24131774621 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 0) <| besselDerivativeNearFromState (1164999357855683 / 8000000000000) 0 (IntervalRat.scale (469 / 4) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (62648471524 / 1000000000000) (62648474440 / 1000000000000), orderedInterval (-21352476854 / 1000000000000) (-21352473937 / 1000000000000)))) (orderedInterval (-8370189273 / 1000000000000) (-8370187316 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate241_chunkChecks0 :
    compactCertificate241.chunkChecks (0 : Fin 5) 0 9 = true :=
  compactCertificate241.chunkChecks_nine_of_three (0 : Fin 5) compactCertificate241_chunkChecks0_0
    compactCertificate241_chunkChecks0_1 compactCertificate241_chunkChecks0_2

theorem compactCertificate241_chunkChecks1_0 :
    compactCertificate241.chunkChecks (1 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 1) <| besselDerivativeNearFromState (469 / 4) 1 (IntervalRat.scale (469 / 4) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-71834575289 / 1000000000000) (-71834574514 / 1000000000000), orderedInterval (16717976852 / 1000000000000) (16717977627 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 1) <| besselDerivativeNearFromState (690926554565569 / 8000000000000) 1 (IntervalRat.scale (469 / 4) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-62468548698 / 1000000000000) (-62468449553 / 1000000000000), orderedInterval (59258780335 / 1000000000000) (59258879480 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 1) <| besselDerivativeNearFromState (223431451764577 / 1600000000000) 1 (IntervalRat.scale (469 / 4) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (54625291902 / 1000000000000) (54625346591 / 1000000000000), orderedInterval (-39880878792 / 1000000000000) (-39880824104 / 1000000000000)))) (orderedInterval (4245909387 / 1000000000000) (4245914206 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 1) <| besselDerivativeNearFromState (201610645426883 / 8000000000000) 1 (IntervalRat.scale (469 / 4) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (119293817231 / 1000000000000) (119293817232 / 1000000000000), orderedInterval (102656545249 / 1000000000000) (102656545250 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 1) <| besselDerivativeNearFromState (541554552499751 / 8000000000000) 1 (IntervalRat.scale (469 / 4) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-57692249859 / 1000000000000) (-57692227555 / 1000000000000), orderedInterval (78374861401 / 1000000000000) (78374883705 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 1) <| besselDerivativeNearFromState (1470425957400267 / 8000000000000) 1 (IntervalRat.scale (469 / 4) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (40799895873 / 1000000000000) (40799938608 / 1000000000000), orderedInterval (-42525167427 / 1000000000000) (-42525124692 / 1000000000000)))) (orderedInterval (6151821689 / 1000000000000) (6151826938 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 1) <| besselDerivativeNearFromState (1083109104999971 / 8000000000000) 1 (IntervalRat.scale (469 / 4) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-60626660719 / 1000000000000) (-60626660718 / 1000000000000), orderedInterval (-31816007143 / 1000000000000) (-31816007142 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 1) <| besselDerivativeNearFromState (1855925912420783 / 8000000000000) 1 (IntervalRat.scale (469 / 4) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (15367690333 / 1000000000000) (15367690334 / 1000000000000), orderedInterval (50046811458 / 1000000000000) (50046811459 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 1) <| besselDerivativeNearFromState (1367066627075597 / 8000000000000) 1 (IntervalRat.scale (469 / 4) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (54928313613 / 1000000000000) (54928325873 / 1000000000000), orderedInterval (-26775273283 / 1000000000000) (-26775261024 / 1000000000000)))) (orderedInterval (-3997361509 / 1000000000000) (-3997361065 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate241_chunkChecks1_1 :
    compactCertificate241.chunkChecks (1 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 1) <| besselDerivativeNearFromState (2097431762894531 / 8000000000000) 1 (IntervalRat.scale (469 / 4) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-39497948482 / 1000000000000) (-39497845290 / 1000000000000), orderedInterval (29538852155 / 1000000000000) (29538955347 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 1) <| besselDerivativeNearFromState (1210952792913899 / 8000000000000) 1 (IntervalRat.scale (469 / 4) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (63378109711 / 1000000000000) (63378109713 / 1000000000000), orderedInterval (13536158732 / 1000000000000) (13536158734 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 1) <| besselDerivativeNearFromState (2148856981217191 / 8000000000000) 1 (IntervalRat.scale (469 / 4) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-34407666540 / 1000000000000) (-34407632067 / 1000000000000), orderedInterval (34505159899 / 1000000000000) (34505194372 / 1000000000000)))) (orderedInterval (795359198 / 1000000000000) (795411522 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 1) <| besselDerivativeNearFromState (2007740934249379 / 8000000000000) 1 (IntervalRat.scale (469 / 4) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (20771428297 / 1000000000000) (20771428298 / 1000000000000), orderedInterval (45841208016 / 1000000000000) (45841208017 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 1) <| besselDerivativeNearFromState (1432818667289107 / 8000000000000) 1 (IntervalRat.scale (469 / 4) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-43437840982 / 1000000000000) (-43437840981 / 1000000000000), orderedInterval (-40715680390 / 1000000000000) (-40715680389 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 1) <| besselDerivativeNearFromState (1624663657499253 / 8000000000000) 1 (IntervalRat.scale (469 / 4) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (18448832376 / 1000000000000) (18448832778 / 1000000000000), orderedInterval (-52907742628 / 1000000000000) (-52907742227 / 1000000000000)))) (orderedInterval (-7188901419 / 1000000000000) (-7188901392 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 1) <| besselDerivativeNearFromState (1354475177921957 / 8000000000000) 1 (IntervalRat.scale (469 / 4) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (26564359556 / 1000000000000) (26564359557 / 1000000000000), orderedInterval (55188559186 / 1000000000000) (55188559187 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 1) <| besselDerivativeNearFromState (1196719896805097 / 8000000000000) 1 (IntervalRat.scale (469 / 4) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-26713669106 / 1000000000000) (-26713667531 / 1000000000000), orderedInterval (59605338814 / 1000000000000) (59605340388 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 1) <| besselDerivativeNearFromState (346856070492603 / 1600000000000) 1 (IntervalRat.scale (469 / 4) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-38872997033 / 1000000000000) (-38872997032 / 1000000000000), orderedInterval (-37666541012 / 1000000000000) (-37666541011 / 1000000000000)))) (orderedInterval (-5214696530 / 1000000000000) (-5214696398 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate241_chunkChecks1_2 :
    compactCertificate241.chunkChecks (1 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 1) <| besselDerivativeNearFromState (959422145017441 / 8000000000000) 1 (IntervalRat.scale (469 / 4) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (70783864637 / 1000000000000) (70783864639 / 1000000000000), orderedInterval (16966516860 / 1000000000000) (16966516861 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 1) <| besselDerivativeNearFromState (813312777640601 / 8000000000000) 1 (IntervalRat.scale (469 / 4) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (74429084428 / 1000000000000) (74429087319 / 1000000000000), orderedInterval (-27240662708 / 1000000000000) (-27240659818 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 1) <| besselDerivativeNearFromState (508933372924403 / 8000000000000) 1 (IntervalRat.scale (469 / 4) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (100033733928 / 1000000000000) (100033733952 / 1000000000000), orderedInterval (-531653808 / 1000000000000) (-531653783 / 1000000000000)))) (orderedInterval (-1447296545 / 1000000000000) (-1447296374 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 1) <| besselDerivativeNearFromState (273706060594701 / 8000000000000) 1 (IntervalRat.scale (469 / 4) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-57788248642 / 1000000000000) (-57788248641 / 1000000000000), orderedInterval (-122724215794 / 1000000000000) (-122724215793 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 1) <| besselDerivativeNearFromState (743165197927103 / 8000000000000) 1 (IntervalRat.scale (469 / 4) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-44538075517 / 1000000000000) (-44538065357 / 1000000000000), orderedInterval (70021263502 / 1000000000000) (70021273662 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 1) <| besselDerivativeNearFromState (1014728542622431 / 8000000000000) 1 (IntervalRat.scale (469 / 4) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (65498687655 / 1000000000000) (65498692978 / 1000000000000), orderedInterval (-27256875476 / 1000000000000) (-27256870153 / 1000000000000)))) (orderedInterval (1662460493 / 1000000000000) (1662461131 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 1) <| besselDerivativeNearFromState (429066627075597 / 8000000000000) 1 (IntervalRat.scale (469 / 4) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-92220007043 / 1000000000000) (-92220007042 / 1000000000000), orderedInterval (-57149838440 / 1000000000000) (-57149838439 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 1) <| besselDerivativeNearFromState (1744132017995437 / 8000000000000) 1 (IntervalRat.scale (469 / 4) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-48405088901 / 1000000000000) (-48405071987 / 1000000000000), orderedInterval (24131757707 / 1000000000000) (24131774621 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 1) <| besselDerivativeNearFromState (1164999357855683 / 8000000000000) 1 (IntervalRat.scale (469 / 4) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (62648471524 / 1000000000000) (62648474440 / 1000000000000), orderedInterval (-21352476854 / 1000000000000) (-21352473937 / 1000000000000)))) (orderedInterval (1165655919 / 1000000000000) (1165659205 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate241_chunkChecks1 :
    compactCertificate241.chunkChecks (1 : Fin 5) 0 9 = true :=
  compactCertificate241.chunkChecks_nine_of_three (1 : Fin 5) compactCertificate241_chunkChecks1_0
    compactCertificate241_chunkChecks1_1 compactCertificate241_chunkChecks1_2

theorem compactCertificate241_chunkChecks2_0 :
    compactCertificate241.chunkChecks (2 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 2) <| besselDerivativeNearFromState (469 / 4) 2 (IntervalRat.scale (469 / 4) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-71834575289 / 1000000000000) (-71834574514 / 1000000000000), orderedInterval (16717976852 / 1000000000000) (16717977627 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 2) <| besselDerivativeNearFromState (690926554565569 / 8000000000000) 2 (IntervalRat.scale (469 / 4) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-62468548698 / 1000000000000) (-62468449553 / 1000000000000), orderedInterval (59258780335 / 1000000000000) (59258879480 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 2) <| besselDerivativeNearFromState (223431451764577 / 1600000000000) 2 (IntervalRat.scale (469 / 4) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (54625291902 / 1000000000000) (54625346591 / 1000000000000), orderedInterval (-39880878792 / 1000000000000) (-39880824104 / 1000000000000)))) (orderedInterval (24205418490 / 1000000000000) (24205423903 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 2) <| besselDerivativeNearFromState (201610645426883 / 8000000000000) 2 (IntervalRat.scale (469 / 4) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (119293817231 / 1000000000000) (119293817232 / 1000000000000), orderedInterval (102656545249 / 1000000000000) (102656545250 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 2) <| besselDerivativeNearFromState (541554552499751 / 8000000000000) 2 (IntervalRat.scale (469 / 4) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-57692249859 / 1000000000000) (-57692227555 / 1000000000000), orderedInterval (78374861401 / 1000000000000) (78374883705 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 2) <| besselDerivativeNearFromState (1470425957400267 / 8000000000000) 2 (IntervalRat.scale (469 / 4) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (40799895873 / 1000000000000) (40799938608 / 1000000000000), orderedInterval (-42525167427 / 1000000000000) (-42525124692 / 1000000000000)))) (orderedInterval (7837116350 / 1000000000000) (7837124155 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 2) <| besselDerivativeNearFromState (1083109104999971 / 8000000000000) 2 (IntervalRat.scale (469 / 4) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-60626660719 / 1000000000000) (-60626660718 / 1000000000000), orderedInterval (-31816007143 / 1000000000000) (-31816007142 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 2) <| besselDerivativeNearFromState (1855925912420783 / 8000000000000) 2 (IntervalRat.scale (469 / 4) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (15367690333 / 1000000000000) (15367690334 / 1000000000000), orderedInterval (50046811458 / 1000000000000) (50046811459 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 2) <| besselDerivativeNearFromState (1367066627075597 / 8000000000000) 2 (IntervalRat.scale (469 / 4) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (54928313613 / 1000000000000) (54928325873 / 1000000000000), orderedInterval (-26775273283 / 1000000000000) (-26775261024 / 1000000000000)))) (orderedInterval (-930016507 / 1000000000000) (-930015853 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate241_chunkChecks2_1 :
    compactCertificate241.chunkChecks (2 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 2) <| besselDerivativeNearFromState (2097431762894531 / 8000000000000) 2 (IntervalRat.scale (469 / 4) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-39497948482 / 1000000000000) (-39497845290 / 1000000000000), orderedInterval (29538852155 / 1000000000000) (29538955347 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 2) <| besselDerivativeNearFromState (1210952792913899 / 8000000000000) 2 (IntervalRat.scale (469 / 4) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (63378109711 / 1000000000000) (63378109713 / 1000000000000), orderedInterval (13536158732 / 1000000000000) (13536158734 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 2) <| besselDerivativeNearFromState (2148856981217191 / 8000000000000) 2 (IntervalRat.scale (469 / 4) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-34407666540 / 1000000000000) (-34407632067 / 1000000000000), orderedInterval (34505159899 / 1000000000000) (34505194372 / 1000000000000)))) (orderedInterval (-17254469151 / 1000000000000) (-17254351099 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 2) <| besselDerivativeNearFromState (2007740934249379 / 8000000000000) 2 (IntervalRat.scale (469 / 4) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (20771428297 / 1000000000000) (20771428298 / 1000000000000), orderedInterval (45841208016 / 1000000000000) (45841208017 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 2) <| besselDerivativeNearFromState (1432818667289107 / 8000000000000) 2 (IntervalRat.scale (469 / 4) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-43437840982 / 1000000000000) (-43437840981 / 1000000000000), orderedInterval (-40715680390 / 1000000000000) (-40715680389 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 2) <| besselDerivativeNearFromState (1624663657499253 / 8000000000000) 2 (IntervalRat.scale (469 / 4) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (18448832376 / 1000000000000) (18448832778 / 1000000000000), orderedInterval (-52907742628 / 1000000000000) (-52907742227 / 1000000000000)))) (orderedInterval (11643830545 / 1000000000000) (11643830590 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 2) <| besselDerivativeNearFromState (1354475177921957 / 8000000000000) 2 (IntervalRat.scale (469 / 4) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (26564359556 / 1000000000000) (26564359557 / 1000000000000), orderedInterval (55188559186 / 1000000000000) (55188559187 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 2) <| besselDerivativeNearFromState (1196719896805097 / 8000000000000) 2 (IntervalRat.scale (469 / 4) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-26713669106 / 1000000000000) (-26713667531 / 1000000000000), orderedInterval (59605338814 / 1000000000000) (59605340388 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 2) <| besselDerivativeNearFromState (346856070492603 / 1600000000000) 2 (IntervalRat.scale (469 / 4) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-38872997033 / 1000000000000) (-38872997032 / 1000000000000), orderedInterval (-37666541012 / 1000000000000) (-37666541011 / 1000000000000)))) (orderedInterval (318913390 / 1000000000000) (318913563 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate241_chunkChecks2_2 :
    compactCertificate241.chunkChecks (2 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 2) <| besselDerivativeNearFromState (959422145017441 / 8000000000000) 2 (IntervalRat.scale (469 / 4) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (70783864637 / 1000000000000) (70783864639 / 1000000000000), orderedInterval (16966516860 / 1000000000000) (16966516861 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 2) <| besselDerivativeNearFromState (813312777640601 / 8000000000000) 2 (IntervalRat.scale (469 / 4) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (74429084428 / 1000000000000) (74429087319 / 1000000000000), orderedInterval (-27240662708 / 1000000000000) (-27240659818 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 2) <| besselDerivativeNearFromState (508933372924403 / 8000000000000) 2 (IntervalRat.scale (469 / 4) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (100033733928 / 1000000000000) (100033733952 / 1000000000000), orderedInterval (-531653808 / 1000000000000) (-531653783 / 1000000000000)))) (orderedInterval (14061450963 / 1000000000000) (14061451114 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 2) <| besselDerivativeNearFromState (273706060594701 / 8000000000000) 2 (IntervalRat.scale (469 / 4) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-57788248642 / 1000000000000) (-57788248641 / 1000000000000), orderedInterval (-122724215794 / 1000000000000) (-122724215793 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 2) <| besselDerivativeNearFromState (743165197927103 / 8000000000000) 2 (IntervalRat.scale (469 / 4) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-44538075517 / 1000000000000) (-44538065357 / 1000000000000), orderedInterval (70021263502 / 1000000000000) (70021273662 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 2) <| besselDerivativeNearFromState (1014728542622431 / 8000000000000) 2 (IntervalRat.scale (469 / 4) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (65498687655 / 1000000000000) (65498692978 / 1000000000000), orderedInterval (-27256875476 / 1000000000000) (-27256870153 / 1000000000000)))) (orderedInterval (5135265449 / 1000000000000) (5135266090 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 2) <| besselDerivativeNearFromState (429066627075597 / 8000000000000) 2 (IntervalRat.scale (469 / 4) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-92220007043 / 1000000000000) (-92220007042 / 1000000000000), orderedInterval (-57149838440 / 1000000000000) (-57149838439 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 2) <| besselDerivativeNearFromState (1744132017995437 / 8000000000000) 2 (IntervalRat.scale (469 / 4) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-48405088901 / 1000000000000) (-48405071987 / 1000000000000), orderedInterval (24131757707 / 1000000000000) (24131774621 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 2) <| besselDerivativeNearFromState (1164999357855683 / 8000000000000) 2 (IntervalRat.scale (469 / 4) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (62648471524 / 1000000000000) (62648474440 / 1000000000000), orderedInterval (-21352476854 / 1000000000000) (-21352473937 / 1000000000000)))) (orderedInterval (4615415169 / 1000000000000) (4615420869 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate241_chunkChecks2 :
    compactCertificate241.chunkChecks (2 : Fin 5) 0 9 = true :=
  compactCertificate241.chunkChecks_nine_of_three (2 : Fin 5) compactCertificate241_chunkChecks2_0
    compactCertificate241_chunkChecks2_1 compactCertificate241_chunkChecks2_2

theorem compactCertificate241_chunkChecks3_0 :
    compactCertificate241.chunkChecks (3 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 3) <| besselDerivativeNearFromState (469 / 4) 3 (IntervalRat.scale (469 / 4) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-71834575289 / 1000000000000) (-71834574514 / 1000000000000), orderedInterval (16717976852 / 1000000000000) (16717977627 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 3) <| besselDerivativeNearFromState (690926554565569 / 8000000000000) 3 (IntervalRat.scale (469 / 4) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-62468548698 / 1000000000000) (-62468449553 / 1000000000000), orderedInterval (59258780335 / 1000000000000) (59258879480 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 3) <| besselDerivativeNearFromState (223431451764577 / 1600000000000) 3 (IntervalRat.scale (469 / 4) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (54625291902 / 1000000000000) (54625346591 / 1000000000000), orderedInterval (-39880878792 / 1000000000000) (-39880824104 / 1000000000000)))) (orderedInterval (-3099596989 / 1000000000000) (-3099590833 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 3) <| besselDerivativeNearFromState (201610645426883 / 8000000000000) 3 (IntervalRat.scale (469 / 4) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (119293817231 / 1000000000000) (119293817232 / 1000000000000), orderedInterval (102656545249 / 1000000000000) (102656545250 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 3) <| besselDerivativeNearFromState (541554552499751 / 8000000000000) 3 (IntervalRat.scale (469 / 4) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-57692249859 / 1000000000000) (-57692227555 / 1000000000000), orderedInterval (78374861401 / 1000000000000) (78374883705 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 3) <| besselDerivativeNearFromState (1470425957400267 / 8000000000000) 3 (IntervalRat.scale (469 / 4) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (40799895873 / 1000000000000) (40799938608 / 1000000000000), orderedInterval (-42525167427 / 1000000000000) (-42525124692 / 1000000000000)))) (orderedInterval (-12251957558 / 1000000000000) (-12251945599 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 3) <| besselDerivativeNearFromState (1083109104999971 / 8000000000000) 3 (IntervalRat.scale (469 / 4) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-60626660719 / 1000000000000) (-60626660718 / 1000000000000), orderedInterval (-31816007143 / 1000000000000) (-31816007142 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 3) <| besselDerivativeNearFromState (1855925912420783 / 8000000000000) 3 (IntervalRat.scale (469 / 4) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (15367690333 / 1000000000000) (15367690334 / 1000000000000), orderedInterval (50046811458 / 1000000000000) (50046811459 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 3) <| besselDerivativeNearFromState (1367066627075597 / 8000000000000) 3 (IntervalRat.scale (469 / 4) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (54928313613 / 1000000000000) (54928325873 / 1000000000000), orderedInterval (-26775273283 / 1000000000000) (-26775261024 / 1000000000000)))) (orderedInterval (13967845195 / 1000000000000) (13967846155 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate241_chunkChecks3_1 :
    compactCertificate241.chunkChecks (3 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 3) <| besselDerivativeNearFromState (2097431762894531 / 8000000000000) 3 (IntervalRat.scale (469 / 4) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-39497948482 / 1000000000000) (-39497845290 / 1000000000000), orderedInterval (29538852155 / 1000000000000) (29538955347 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 3) <| besselDerivativeNearFromState (1210952792913899 / 8000000000000) 3 (IntervalRat.scale (469 / 4) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (63378109711 / 1000000000000) (63378109713 / 1000000000000), orderedInterval (13536158732 / 1000000000000) (13536158734 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 3) <| besselDerivativeNearFromState (2148856981217191 / 8000000000000) 3 (IntervalRat.scale (469 / 4) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-34407666540 / 1000000000000) (-34407632067 / 1000000000000), orderedInterval (34505159899 / 1000000000000) (34505194372 / 1000000000000)))) (orderedInterval (-2302876131 / 1000000000000) (-2302610763 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 3) <| besselDerivativeNearFromState (2007740934249379 / 8000000000000) 3 (IntervalRat.scale (469 / 4) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (20771428297 / 1000000000000) (20771428298 / 1000000000000), orderedInterval (45841208016 / 1000000000000) (45841208017 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 3) <| besselDerivativeNearFromState (1432818667289107 / 8000000000000) 3 (IntervalRat.scale (469 / 4) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-43437840982 / 1000000000000) (-43437840981 / 1000000000000), orderedInterval (-40715680390 / 1000000000000) (-40715680389 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 3) <| besselDerivativeNearFromState (1624663657499253 / 8000000000000) 3 (IntervalRat.scale (469 / 4) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (18448832376 / 1000000000000) (18448832778 / 1000000000000), orderedInterval (-52907742628 / 1000000000000) (-52907742227 / 1000000000000)))) (orderedInterval (20347508849 / 1000000000000) (20347508924 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 3) <| besselDerivativeNearFromState (1354475177921957 / 8000000000000) 3 (IntervalRat.scale (469 / 4) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (26564359556 / 1000000000000) (26564359557 / 1000000000000), orderedInterval (55188559186 / 1000000000000) (55188559187 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 3) <| besselDerivativeNearFromState (1196719896805097 / 8000000000000) 3 (IntervalRat.scale (469 / 4) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-26713669106 / 1000000000000) (-26713667531 / 1000000000000), orderedInterval (59605338814 / 1000000000000) (59605340388 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 3) <| besselDerivativeNearFromState (346856070492603 / 1600000000000) 3 (IntervalRat.scale (469 / 4) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-38872997033 / 1000000000000) (-38872997032 / 1000000000000), orderedInterval (-37666541012 / 1000000000000) (-37666541011 / 1000000000000)))) (orderedInterval (11257137028 / 1000000000000) (11257137254 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate241_chunkChecks3_2 :
    compactCertificate241.chunkChecks (3 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 3) <| besselDerivativeNearFromState (959422145017441 / 8000000000000) 3 (IntervalRat.scale (469 / 4) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (70783864637 / 1000000000000) (70783864639 / 1000000000000), orderedInterval (16966516860 / 1000000000000) (16966516861 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 3) <| besselDerivativeNearFromState (813312777640601 / 8000000000000) 3 (IntervalRat.scale (469 / 4) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (74429084428 / 1000000000000) (74429087319 / 1000000000000), orderedInterval (-27240662708 / 1000000000000) (-27240659818 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 3) <| besselDerivativeNearFromState (508933372924403 / 8000000000000) 3 (IntervalRat.scale (469 / 4) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (100033733928 / 1000000000000) (100033733952 / 1000000000000), orderedInterval (-531653808 / 1000000000000) (-531653783 / 1000000000000)))) (orderedInterval (1780620036 / 1000000000000) (1780620170 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 3) <| besselDerivativeNearFromState (273706060594701 / 8000000000000) 3 (IntervalRat.scale (469 / 4) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-57788248642 / 1000000000000) (-57788248641 / 1000000000000), orderedInterval (-122724215794 / 1000000000000) (-122724215793 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 3) <| besselDerivativeNearFromState (743165197927103 / 8000000000000) 3 (IntervalRat.scale (469 / 4) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-44538075517 / 1000000000000) (-44538065357 / 1000000000000), orderedInterval (70021263502 / 1000000000000) (70021273662 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 3) <| besselDerivativeNearFromState (1014728542622431 / 8000000000000) 3 (IntervalRat.scale (469 / 4) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (65498687655 / 1000000000000) (65498692978 / 1000000000000), orderedInterval (-27256875476 / 1000000000000) (-27256870153 / 1000000000000)))) (orderedInterval (-1954572123 / 1000000000000) (-1954571473 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 3) <| besselDerivativeNearFromState (429066627075597 / 8000000000000) 3 (IntervalRat.scale (469 / 4) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-92220007043 / 1000000000000) (-92220007042 / 1000000000000), orderedInterval (-57149838440 / 1000000000000) (-57149838439 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 3) <| besselDerivativeNearFromState (1744132017995437 / 8000000000000) 3 (IntervalRat.scale (469 / 4) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-48405088901 / 1000000000000) (-48405071987 / 1000000000000), orderedInterval (24131757707 / 1000000000000) (24131774621 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 3) <| besselDerivativeNearFromState (1164999357855683 / 8000000000000) 3 (IntervalRat.scale (469 / 4) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (62648471524 / 1000000000000) (62648474440 / 1000000000000), orderedInterval (-21352476854 / 1000000000000) (-21352473937 / 1000000000000)))) (orderedInterval (4946636187 / 1000000000000) (4946646239 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate241_chunkChecks3 :
    compactCertificate241.chunkChecks (3 : Fin 5) 0 9 = true :=
  compactCertificate241.chunkChecks_nine_of_three (3 : Fin 5) compactCertificate241_chunkChecks3_0
    compactCertificate241_chunkChecks3_1 compactCertificate241_chunkChecks3_2

theorem compactCertificate241_chunkChecks4_0 :
    compactCertificate241.chunkChecks (4 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 4) <| besselDerivativeNearFromState (469 / 4) 4 (IntervalRat.scale (469 / 4) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-71834575289 / 1000000000000) (-71834574514 / 1000000000000), orderedInterval (16717976852 / 1000000000000) (16717977627 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 4) <| besselDerivativeNearFromState (690926554565569 / 8000000000000) 4 (IntervalRat.scale (469 / 4) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-62468548698 / 1000000000000) (-62468449553 / 1000000000000), orderedInterval (59258780335 / 1000000000000) (59258879480 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 4) <| besselDerivativeNearFromState (223431451764577 / 1600000000000) 4 (IntervalRat.scale (469 / 4) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (54625291902 / 1000000000000) (54625346591 / 1000000000000), orderedInterval (-39880878792 / 1000000000000) (-39880824104 / 1000000000000)))) (orderedInterval (-22139758299 / 1000000000000) (-22139751145 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 4) <| besselDerivativeNearFromState (201610645426883 / 8000000000000) 4 (IntervalRat.scale (469 / 4) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (119293817231 / 1000000000000) (119293817232 / 1000000000000), orderedInterval (102656545249 / 1000000000000) (102656545250 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 4) <| besselDerivativeNearFromState (541554552499751 / 8000000000000) 4 (IntervalRat.scale (469 / 4) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-57692249859 / 1000000000000) (-57692227555 / 1000000000000), orderedInterval (78374861401 / 1000000000000) (78374883705 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 4) <| besselDerivativeNearFromState (1470425957400267 / 8000000000000) 4 (IntervalRat.scale (469 / 4) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (40799895873 / 1000000000000) (40799938608 / 1000000000000), orderedInterval (-42525167427 / 1000000000000) (-42525124692 / 1000000000000)))) (orderedInterval (-17542941762 / 1000000000000) (-17542923073 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 4) <| besselDerivativeNearFromState (1083109104999971 / 8000000000000) 4 (IntervalRat.scale (469 / 4) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-60626660719 / 1000000000000) (-60626660718 / 1000000000000), orderedInterval (-31816007143 / 1000000000000) (-31816007142 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 4) <| besselDerivativeNearFromState (1855925912420783 / 8000000000000) 4 (IntervalRat.scale (469 / 4) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (15367690333 / 1000000000000) (15367690334 / 1000000000000), orderedInterval (50046811458 / 1000000000000) (50046811459 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 4) <| besselDerivativeNearFromState (1367066627075597 / 8000000000000) 4 (IntervalRat.scale (469 / 4) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (54928313613 / 1000000000000) (54928325873 / 1000000000000), orderedInterval (-26775273283 / 1000000000000) (-26775261024 / 1000000000000)))) (orderedInterval (-1513481564 / 1000000000000) (-1513480142 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate241_chunkChecks4_1 :
    compactCertificate241.chunkChecks (4 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 4) <| besselDerivativeNearFromState (2097431762894531 / 8000000000000) 4 (IntervalRat.scale (469 / 4) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-39497948482 / 1000000000000) (-39497845290 / 1000000000000), orderedInterval (29538852155 / 1000000000000) (29538955347 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 4) <| besselDerivativeNearFromState (1210952792913899 / 8000000000000) 4 (IntervalRat.scale (469 / 4) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (63378109711 / 1000000000000) (63378109713 / 1000000000000), orderedInterval (13536158732 / 1000000000000) (13536158734 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 4) <| besselDerivativeNearFromState (2148856981217191 / 8000000000000) 4 (IntervalRat.scale (469 / 4) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-34407666540 / 1000000000000) (-34407632067 / 1000000000000), orderedInterval (34505159899 / 1000000000000) (34505194372 / 1000000000000)))) (orderedInterval (53817075276 / 1000000000000) (53817674136 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 4) <| besselDerivativeNearFromState (2007740934249379 / 8000000000000) 4 (IntervalRat.scale (469 / 4) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (20771428297 / 1000000000000) (20771428298 / 1000000000000), orderedInterval (45841208016 / 1000000000000) (45841208017 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 4) <| besselDerivativeNearFromState (1432818667289107 / 8000000000000) 4 (IntervalRat.scale (469 / 4) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-43437840982 / 1000000000000) (-43437840981 / 1000000000000), orderedInterval (-40715680390 / 1000000000000) (-40715680389 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 4) <| besselDerivativeNearFromState (1624663657499253 / 8000000000000) 4 (IntervalRat.scale (469 / 4) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (18448832376 / 1000000000000) (18448832778 / 1000000000000), orderedInterval (-52907742628 / 1000000000000) (-52907742227 / 1000000000000)))) (orderedInterval (-31421251042 / 1000000000000) (-31421250911 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 4) <| besselDerivativeNearFromState (1354475177921957 / 8000000000000) 4 (IntervalRat.scale (469 / 4) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (26564359556 / 1000000000000) (26564359557 / 1000000000000), orderedInterval (55188559186 / 1000000000000) (55188559187 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 4) <| besselDerivativeNearFromState (1196719896805097 / 8000000000000) 4 (IntervalRat.scale (469 / 4) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-26713669106 / 1000000000000) (-26713667531 / 1000000000000), orderedInterval (59605338814 / 1000000000000) (59605340388 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 4) <| besselDerivativeNearFromState (346856070492603 / 1600000000000) 4 (IntervalRat.scale (469 / 4) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-38872997033 / 1000000000000) (-38872997032 / 1000000000000), orderedInterval (-37666541012 / 1000000000000) (-37666541011 / 1000000000000)))) (orderedInterval (-6439035925 / 1000000000000) (-6439035623 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate241_chunkChecks4_2 :
    compactCertificate241.chunkChecks (4 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 4) <| besselDerivativeNearFromState (959422145017441 / 8000000000000) 4 (IntervalRat.scale (469 / 4) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (70783864637 / 1000000000000) (70783864639 / 1000000000000), orderedInterval (16966516860 / 1000000000000) (16966516861 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 4) <| besselDerivativeNearFromState (813312777640601 / 8000000000000) 4 (IntervalRat.scale (469 / 4) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (74429084428 / 1000000000000) (74429087319 / 1000000000000), orderedInterval (-27240662708 / 1000000000000) (-27240659818 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 4) <| besselDerivativeNearFromState (508933372924403 / 8000000000000) 4 (IntervalRat.scale (469 / 4) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (100033733928 / 1000000000000) (100033733952 / 1000000000000), orderedInterval (-531653808 / 1000000000000) (-531653783 / 1000000000000)))) (orderedInterval (-14515897378 / 1000000000000) (-14515897258 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 4) <| besselDerivativeNearFromState (273706060594701 / 8000000000000) 4 (IntervalRat.scale (469 / 4) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-57788248642 / 1000000000000) (-57788248641 / 1000000000000), orderedInterval (-122724215794 / 1000000000000) (-122724215793 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 4) <| besselDerivativeNearFromState (743165197927103 / 8000000000000) 4 (IntervalRat.scale (469 / 4) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-44538075517 / 1000000000000) (-44538065357 / 1000000000000), orderedInterval (70021263502 / 1000000000000) (70021273662 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 4) <| besselDerivativeNearFromState (1014728542622431 / 8000000000000) 4 (IntervalRat.scale (469 / 4) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (65498687655 / 1000000000000) (65498692978 / 1000000000000), orderedInterval (-27256875476 / 1000000000000) (-27256870153 / 1000000000000)))) (orderedInterval (-6435366477 / 1000000000000) (-6435365802 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 4) <| besselDerivativeNearFromState (429066627075597 / 8000000000000) 4 (IntervalRat.scale (469 / 4) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-92220007043 / 1000000000000) (-92220007042 / 1000000000000), orderedInterval (-57149838440 / 1000000000000) (-57149838439 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 4) <| besselDerivativeNearFromState (1744132017995437 / 8000000000000) 4 (IntervalRat.scale (469 / 4) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-48405088901 / 1000000000000) (-48405071987 / 1000000000000), orderedInterval (24131757707 / 1000000000000) (24131774621 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 4) <| besselDerivativeNearFromState (1164999357855683 / 8000000000000) 4 (IntervalRat.scale (469 / 4) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (62648471524 / 1000000000000) (62648474440 / 1000000000000), orderedInterval (-21352476854 / 1000000000000) (-21352473937 / 1000000000000)))) (orderedInterval (19022457055 / 1000000000000) (19022475150 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate241_chunkChecks4 :
    compactCertificate241.chunkChecks (4 : Fin 5) 0 9 = true :=
  compactCertificate241.chunkChecks_nine_of_three (4 : Fin 5) compactCertificate241_chunkChecks4_0
    compactCertificate241_chunkChecks4_1 compactCertificate241_chunkChecks4_2

theorem compactCertificate241_chunks :
    ∀ r : Fin 5, ∀ b, compactCertificate241.chunkCheck r b = true :=
  compactCertificate241.chunkChecks_all (by
    intro r
    fin_cases r
    · exact compactCertificate241_chunkChecks0
    · exact compactCertificate241_chunkChecks1
    · exact compactCertificate241_chunkChecks2
    · exact compactCertificate241_chunkChecks3
    · exact compactCertificate241_chunkChecks4)

theorem compactCertificate241_coefficient0 :
    compactCertificate241.coefficientCheck (0 : Fin 5) = true := by
  norm_num [CompactCertificate.coefficientCheck, intervalFinSumHull,
    compactCertificate241, rationalIntervalSubset, orderedInterval, Fin.sum_univ_succ]

theorem compactCertificate241_coefficient1 :
    compactCertificate241.coefficientCheck (1 : Fin 5) = true := by
  norm_num [CompactCertificate.coefficientCheck, intervalFinSumHull,
    compactCertificate241, rationalIntervalSubset, orderedInterval, Fin.sum_univ_succ]

theorem compactCertificate241_coefficient2 :
    compactCertificate241.coefficientCheck (2 : Fin 5) = true := by
  norm_num [CompactCertificate.coefficientCheck, intervalFinSumHull,
    compactCertificate241, rationalIntervalSubset, orderedInterval, Fin.sum_univ_succ]

theorem compactCertificate241_coefficient3 :
    compactCertificate241.coefficientCheck (3 : Fin 5) = true := by
  norm_num [CompactCertificate.coefficientCheck, intervalFinSumHull,
    compactCertificate241, rationalIntervalSubset, orderedInterval, Fin.sum_univ_succ]

theorem compactCertificate241_coefficient4 :
    compactCertificate241.coefficientCheck (4 : Fin 5) = true := by
  norm_num [CompactCertificate.coefficientCheck, intervalFinSumHull,
    compactCertificate241, rationalIntervalSubset, orderedInterval, Fin.sum_univ_succ]

theorem compactCertificate241_coefficients : ∀ r : Fin 5,
    compactCertificate241.coefficientCheck r = true := by
  intro r
  fin_cases r
  · exact compactCertificate241_coefficient0
  · exact compactCertificate241_coefficient1
  · exact compactCertificate241_coefficient2
  · exact compactCertificate241_coefficient3
  · exact compactCertificate241_coefficient4

theorem compactCertificate241_lower : (1 : ℚ) ≤ compactCertificate241.output.lo := by
  norm_num [CompactCertificate.output, CompactCertificate.interval,
    CompactCertificate.coefficientTargetNat, compactCertificate241, dualConstant,
    intervalTaylorSum, intervalPow, intervalSub, intervalMaxAbs, widenInterval,
    rationalErrorInterval, orderedInterval, IntervalRat.add, IntervalRat.mul, IntervalRat.scale,
    IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4]

theorem compactCertificate241_proves {t : ℝ} (ht : t ∈ compactCertificate241.interval) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t :=
  compactCertificate241.proves compactCertificate241_states compactCertificate241_chunks
    compactCertificate241_coefficients compactCertificate241_lower ht

end Erdos232
