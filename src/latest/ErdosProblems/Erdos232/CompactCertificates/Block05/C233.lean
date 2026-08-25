/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, OpenAI Codex
-/
import ErdosProblems.Erdos232.CompactBase

open LeanCert.Core
namespace Erdos232

def compactCertificate233 : CompactCertificate where
  left := 110
  right := 111
  center := 221 / 2
  grid := fun i =>
    match i.val with
    | 0 => 35
    | 1 => 26
    | 2 => 42
    | 3 => 8
    | 4 => 20
    | 5 => 55
    | 6 => 41
    | 7 => 70
    | 8 => 51
    | 9 => 79
    | 10 => 45
    | 11 => 81
    | 12 => 75
    | 13 => 54
    | 14 => 61
    | 15 => 51
    | 16 => 45
    | 17 => 65
    | 18 => 36
    | 19 => 31
    | 20 => 19
    | 21 => 10
    | 22 => 28
    | 23 => 38
    | 24 => 16
    | 25 => 65
    | _ => 44
  point := fun i =>
    match i.val with
    | 0 => 221 / 2
    | 1 => 325575199486121 / 4000000000000
    | 2 => 105284330149193 / 800000000000
    | 3 => 95002031213947 / 4000000000000
    | 4 => 255188818981759 / 4000000000000
    | 5 => 692887284830403 / 4000000000000
    | 6 => 510377637963739 / 4000000000000
    | 7 => 874540781759047 / 4000000000000
    | 8 => 644182781628373 / 4000000000000
    | 9 => 988342046054779 / 4000000000000
    | 10 => 570619546341091 / 4000000000000
    | 11 => 1012574398398719 / 4000000000000
    | 12 => 946078350680411 / 4000000000000
    | 13 => 675166152389963 / 4000000000000
    | 14 => 765566456945277 / 4000000000000
    | 15 => 638249497485613 / 4000000000000
    | 16 => 563912787193873 / 4000000000000
    | 17 => 163443905285427 / 800000000000
    | 18 => 452094443600969 / 4000000000000
    | 19 => 383245466649409 / 4000000000000
    | 20 => 239817218371627 / 4000000000000
    | 21 => 128974497636309 / 4000000000000
    | 22 => 350190850195927 / 4000000000000
    | 23 => 478155667205879 / 4000000000000
    | 24 => 202182781628373 / 4000000000000
    | 25 => 821861782466933 / 4000000000000
    | _ => 548965582273147 / 4000000000000
  state := fun i =>
    match i.val with
    | 0 => (orderedInterval (-73685899654 / 1000000000000) (-73685899653 / 1000000000000), orderedInterval (-17876499077 / 1000000000000) (-17876499076 / 1000000000000))
    | 1 => (orderedInterval (42108495392 / 1000000000000) (42108495393 / 1000000000000), orderedInterval (77513008893 / 1000000000000) (77513008894 / 1000000000000))
    | 2 => (orderedInterval (29811131399 / 1000000000000) (29811131400 / 1000000000000), orderedInterval (62725073027 / 1000000000000) (62725073028 / 1000000000000))
    | 3 => (orderedInterval (-92716106700 / 1000000000000) (-92716087555 / 1000000000000), orderedInterval (136896619544 / 1000000000000) (136896638688 / 1000000000000))
    | 4 => (orderedInterval (98314204580 / 1000000000000) (98314204891 / 1000000000000), orderedInterval (-18457575300 / 1000000000000) (-18457574989 / 1000000000000))
    | 5 => (orderedInterval (-56908164397 / 1000000000000) (-56908164396 / 1000000000000), orderedInterval (-20731189509 / 1000000000000) (-20731189508 / 1000000000000))
    | 6 => (orderedInterval (29219068658 / 1000000000000) (29219070539 / 1000000000000), orderedInterval (-64423696834 / 1000000000000) (-64423694953 / 1000000000000))
    | 7 => (orderedInterval (-25465083330 / 1000000000000) (-25465080995 / 1000000000000), orderedInterval (47632637688 / 1000000000000) (47632640022 / 1000000000000))
    | 8 => (orderedInterval (-62826941252 / 1000000000000) (-62826941162 / 1000000000000), orderedInterval (2602250683 / 1000000000000) (2602250773 / 1000000000000))
    | 9 => (orderedInterval (15746148157 / 1000000000000) (15746148387 / 1000000000000), orderedInterval (-48287216490 / 1000000000000) (-48287216259 / 1000000000000))
    | 10 => (orderedInterval (-58722718730 / 1000000000000) (-58722702076 / 1000000000000), orderedInterval (32053649395 / 1000000000000) (32053666049 / 1000000000000))
    | 11 => (orderedInterval (25804585649 / 1000000000000) (25804588955 / 1000000000000), orderedInterval (-43050758792 / 1000000000000) (-43050755486 / 1000000000000))
    | 12 => (orderedInterval (-51542714936 / 1000000000000) (-51542714521 / 1000000000000), orderedInterval (6021500359 / 1000000000000) (6021500773 / 1000000000000))
    | 13 => (orderedInterval (-4283645862 / 1000000000000) (-4283645851 / 1000000000000), orderedInterval (61276870945 / 1000000000000) (61276870957 / 1000000000000))
    | 14 => (orderedInterval (-29612912999 / 1000000000000) (-29612912998 / 1000000000000), orderedInterval (-49413532493 / 1000000000000) (-49413532492 / 1000000000000))
    | 15 => (orderedInterval (-7922897631 / 1000000000000) (-7922897630 / 1000000000000), orderedInterval (-62641216288 / 1000000000000) (-62641216287 / 1000000000000))
    | 16 => (orderedInterval (-25612833633 / 1000000000000) (-25612833632 / 1000000000000), orderedInterval (-62035927231 / 1000000000000) (-62035927230 / 1000000000000))
    | 17 => (orderedInterval (-43241414920 / 1000000000000) (-43241414919 / 1000000000000), orderedInterval (-35195823162 / 1000000000000) (-35195823161 / 1000000000000))
    | 18 => (orderedInterval (48952721370 / 1000000000000) (48952721371 / 1000000000000), orderedInterval (56671630188 / 1000000000000) (56671630189 / 1000000000000))
    | 19 => (orderedInterval (58127211027 / 1000000000000) (58127290955 / 1000000000000), orderedInterval (-57449962543 / 1000000000000) (-57449882616 / 1000000000000))
    | 20 => (orderedInterval (-89246894548 / 1000000000000) (-89246894547 / 1000000000000), orderedInterval (-50765212243 / 1000000000000) (-50765212242 / 1000000000000))
    | 21 => (orderedInterval (140401379816 / 1000000000000) (140401379852 / 1000000000000), orderedInterval (-7574889266 / 1000000000000) (-7574889229 / 1000000000000))
    | 22 => (orderedInterval (30604630057 / 1000000000000) (30604630058 / 1000000000000), orderedInterval (79418772617 / 1000000000000) (79418772618 / 1000000000000))
    | 23 => (orderedInterval (59050901862 / 1000000000000) (59050901863 / 1000000000000), orderedInterval (42631959464 / 1000000000000) (42631959465 / 1000000000000))
    | 24 => (orderedInterval (98071297108 / 1000000000000) (98071297109 / 1000000000000), orderedInterval (53588483392 / 1000000000000) (53588483393 / 1000000000000))
    | 25 => (orderedInterval (-49477743758 / 1000000000000) (-49477725336 / 1000000000000), orderedInterval (25622861365 / 1000000000000) (25622879787 / 1000000000000))
    | _ => (orderedInterval (-13810723259 / 1000000000000) (-13810723152 / 1000000000000), orderedInterval (66743480855 / 1000000000000) (66743480963 / 1000000000000))
  chunkTarget := fun r b =>
    match r.val with
    | 0 =>
      match b.val with
      | 0 => orderedInterval (-27064790443 / 1000000000000) (-27064790434 / 1000000000000)
      | 1 => orderedInterval (8641108050 / 1000000000000) (8641108283 / 1000000000000)
      | 2 => orderedInterval (-732958232 / 1000000000000) (-732958151 / 1000000000000)
      | 3 => orderedInterval (-3480496810 / 1000000000000) (-3480495020 / 1000000000000)
      | 4 => orderedInterval (675289618 / 1000000000000) (675289641 / 1000000000000)
      | 5 => orderedInterval (267095319 / 1000000000000) (267095330 / 1000000000000)
      | 6 => orderedInterval (-14022629125 / 1000000000000) (-14022624573 / 1000000000000)
      | 7 => orderedInterval (-7812445323 / 1000000000000) (-7812445308 / 1000000000000)
      | _ => orderedInterval (7210038715 / 1000000000000) (7210040266 / 1000000000000)
    | 1 =>
      match b.val with
      | 0 => orderedInterval (-2169792352 / 1000000000000) (-2169792342 / 1000000000000)
      | 1 => orderedInterval (1601995525 / 1000000000000) (1601995592 / 1000000000000)
      | 2 => orderedInterval (-2815261097 / 1000000000000) (-2815260940 / 1000000000000)
      | 3 => orderedInterval (8231509256 / 1000000000000) (8231512109 / 1000000000000)
      | 4 => orderedInterval (9051707391 / 1000000000000) (9051707431 / 1000000000000)
      | 5 => orderedInterval (1818617870 / 1000000000000) (1818617886 / 1000000000000)
      | 6 => orderedInterval (-7345585151 / 1000000000000) (-7345581202 / 1000000000000)
      | 7 => orderedInterval (-4921227100 / 1000000000000) (-4921227087 / 1000000000000)
      | _ => orderedInterval (-19283922819 / 1000000000000) (-19283919962 / 1000000000000)
    | 2 =>
      match b.val with
      | 0 => orderedInterval (26531840066 / 1000000000000) (26531840077 / 1000000000000)
      | 1 => orderedInterval (-11199229708 / 1000000000000) (-11199229672 / 1000000000000)
      | 2 => orderedInterval (175805383 / 1000000000000) (175805691 / 1000000000000)
      | 3 => orderedInterval (1914665123 / 1000000000000) (1914670070 / 1000000000000)
      | 4 => orderedInterval (-3849447234 / 1000000000000) (-3849447161 / 1000000000000)
      | 5 => orderedInterval (1573278585 / 1000000000000) (1573278609 / 1000000000000)
      | 6 => orderedInterval (11584029056 / 1000000000000) (11584032518 / 1000000000000)
      | 7 => orderedInterval (5997383295 / 1000000000000) (5997383308 / 1000000000000)
      | _ => orderedInterval (-17871444354 / 1000000000000) (-17871439048 / 1000000000000)
    | 3 =>
      match b.val with
      | 0 => orderedInterval (338337826 / 1000000000000) (338337839 / 1000000000000)
      | 1 => orderedInterval (-5431501287 / 1000000000000) (-5431501250 / 1000000000000)
      | 2 => orderedInterval (11183654689 / 1000000000000) (11183655292 / 1000000000000)
      | 3 => orderedInterval (-27474608000 / 1000000000000) (-27474598766 / 1000000000000)
      | 4 => orderedInterval (-20850707603 / 1000000000000) (-20850707464 / 1000000000000)
      | 5 => orderedInterval (487189892 / 1000000000000) (487189928 / 1000000000000)
      | 6 => orderedInterval (7735346082 / 1000000000000) (7735349086 / 1000000000000)
      | 7 => orderedInterval (4974351833 / 1000000000000) (4974351846 / 1000000000000)
      | _ => orderedInterval (37530355251 / 1000000000000) (37530365076 / 1000000000000)
    | _ =>
      match b.val with
      | 0 => orderedInterval (-25575112746 / 1000000000000) (-25575112731 / 1000000000000)
      | 1 => orderedInterval (24929436279 / 1000000000000) (24929436330 / 1000000000000)
      | 2 => orderedInterval (4984700093 / 1000000000000) (4984701282 / 1000000000000)
      | 3 => orderedInterval (19501167379 / 1000000000000) (19501185878 / 1000000000000)
      | 4 => orderedInterval (19052001533 / 1000000000000) (19052001802 / 1000000000000)
      | 5 => orderedInterval (-9461220010 / 1000000000000) (-9461219953 / 1000000000000)
      | 6 => orderedInterval (-10817499632 / 1000000000000) (-10817496998 / 1000000000000)
      | 7 => orderedInterval (-6580092863 / 1000000000000) (-6580092849 / 1000000000000)
      | _ => orderedInterval (53655962868 / 1000000000000) (53655981174 / 1000000000000)
  coefficientTarget := fun i =>
    match i.val with
    | 0 => orderedInterval (-36319788231 / 1000000000000) (-36319779966 / 1000000000000)
    | 1 => orderedInterval (-15831958477 / 1000000000000) (-15831948515 / 1000000000000)
    | 2 => orderedInterval (14856880212 / 1000000000000) (14856894392 / 1000000000000)
    | 3 => orderedInterval (8492418683 / 1000000000000) (8492441587 / 1000000000000)
    | _ => orderedInterval (69689342901 / 1000000000000) (69689383935 / 1000000000000)

theorem compactCertificate233_stateChecks0 :
    compactCertificate233.stateChecks 0 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 35 12 (221 / 2)) (orderedInterval (-73685899654 / 1000000000000) (-73685899653 / 1000000000000), orderedInterval (-17876499077 / 1000000000000) (-17876499076 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 26 12 (325575199486121 / 4000000000000)) (orderedInterval (42108495392 / 1000000000000) (42108495393 / 1000000000000), orderedInterval (77513008893 / 1000000000000) (77513008894 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 42 12 (105284330149193 / 800000000000)) (orderedInterval (29811131399 / 1000000000000) (29811131400 / 1000000000000), orderedInterval (62725073027 / 1000000000000) (62725073028 / 1000000000000))) = true
  norm_num [besselStateAtRationalPoint, besselIntervalStepZero,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, besselZeroTransition,
    besselInitial, besselGridStateAt, besselGridStateBlock00, besselGridStateBlock01,
    besselGridStateBlock02, besselGridStateBlock03, besselGridStateBlock04,
    besselGridStateBlock05, besselGridStateBlock06, besselGridStateBlock07,
    besselGridStateBlock08, besselGridStateBlock09, besselGridStateBlock10,
    besselGridStateBlock11, besselGridStateBlock12, besselGridStateBlock13,
    besselGridStateBlock14, besselGridState008, besselGridState010, besselGridState016, besselGridState019, besselGridState020, besselGridState026, besselGridState028, besselGridState031, besselGridState035, besselGridState036, besselGridState038, besselGridState041, besselGridState042, besselGridState044, besselGridState045, besselGridState051, besselGridState054, besselGridState055, besselGridState061, besselGridState065, besselGridState070, besselGridState075, besselGridState079, besselGridState081, besselStateSubset, linearInterval, widenInterval,
    rationalErrorInterval, rationalIntervalSubset, orderedInterval, Finset.sum_range_succ,
    IntervalRat.add, IntervalRat.mul, IntervalRat.scale, IntervalRat.singleton]

theorem compactCertificate233_stateChecks1 :
    compactCertificate233.stateChecks 3 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 8 12 (95002031213947 / 4000000000000)) (orderedInterval (-92716106700 / 1000000000000) (-92716087555 / 1000000000000), orderedInterval (136896619544 / 1000000000000) (136896638688 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 20 12 (255188818981759 / 4000000000000)) (orderedInterval (98314204580 / 1000000000000) (98314204891 / 1000000000000), orderedInterval (-18457575300 / 1000000000000) (-18457574989 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 55 12 (692887284830403 / 4000000000000)) (orderedInterval (-56908164397 / 1000000000000) (-56908164396 / 1000000000000), orderedInterval (-20731189509 / 1000000000000) (-20731189508 / 1000000000000))) = true
  norm_num [besselStateAtRationalPoint, besselIntervalStepZero,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, besselZeroTransition,
    besselInitial, besselGridStateAt, besselGridStateBlock00, besselGridStateBlock01,
    besselGridStateBlock02, besselGridStateBlock03, besselGridStateBlock04,
    besselGridStateBlock05, besselGridStateBlock06, besselGridStateBlock07,
    besselGridStateBlock08, besselGridStateBlock09, besselGridStateBlock10,
    besselGridStateBlock11, besselGridStateBlock12, besselGridStateBlock13,
    besselGridStateBlock14, besselGridState008, besselGridState010, besselGridState016, besselGridState019, besselGridState020, besselGridState026, besselGridState028, besselGridState031, besselGridState035, besselGridState036, besselGridState038, besselGridState041, besselGridState042, besselGridState044, besselGridState045, besselGridState051, besselGridState054, besselGridState055, besselGridState061, besselGridState065, besselGridState070, besselGridState075, besselGridState079, besselGridState081, besselStateSubset, linearInterval, widenInterval,
    rationalErrorInterval, rationalIntervalSubset, orderedInterval, Finset.sum_range_succ,
    IntervalRat.add, IntervalRat.mul, IntervalRat.scale, IntervalRat.singleton]

theorem compactCertificate233_stateChecks2 :
    compactCertificate233.stateChecks 6 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 41 12 (510377637963739 / 4000000000000)) (orderedInterval (29219068658 / 1000000000000) (29219070539 / 1000000000000), orderedInterval (-64423696834 / 1000000000000) (-64423694953 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 70 12 (874540781759047 / 4000000000000)) (orderedInterval (-25465083330 / 1000000000000) (-25465080995 / 1000000000000), orderedInterval (47632637688 / 1000000000000) (47632640022 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 51 12 (644182781628373 / 4000000000000)) (orderedInterval (-62826941252 / 1000000000000) (-62826941162 / 1000000000000), orderedInterval (2602250683 / 1000000000000) (2602250773 / 1000000000000))) = true
  norm_num [besselStateAtRationalPoint, besselIntervalStepZero,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, besselZeroTransition,
    besselInitial, besselGridStateAt, besselGridStateBlock00, besselGridStateBlock01,
    besselGridStateBlock02, besselGridStateBlock03, besselGridStateBlock04,
    besselGridStateBlock05, besselGridStateBlock06, besselGridStateBlock07,
    besselGridStateBlock08, besselGridStateBlock09, besselGridStateBlock10,
    besselGridStateBlock11, besselGridStateBlock12, besselGridStateBlock13,
    besselGridStateBlock14, besselGridState008, besselGridState010, besselGridState016, besselGridState019, besselGridState020, besselGridState026, besselGridState028, besselGridState031, besselGridState035, besselGridState036, besselGridState038, besselGridState041, besselGridState042, besselGridState044, besselGridState045, besselGridState051, besselGridState054, besselGridState055, besselGridState061, besselGridState065, besselGridState070, besselGridState075, besselGridState079, besselGridState081, besselStateSubset, linearInterval, widenInterval,
    rationalErrorInterval, rationalIntervalSubset, orderedInterval, Finset.sum_range_succ,
    IntervalRat.add, IntervalRat.mul, IntervalRat.scale, IntervalRat.singleton]

theorem compactCertificate233_stateChecks3 :
    compactCertificate233.stateChecks 9 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 79 12 (988342046054779 / 4000000000000)) (orderedInterval (15746148157 / 1000000000000) (15746148387 / 1000000000000), orderedInterval (-48287216490 / 1000000000000) (-48287216259 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 45 12 (570619546341091 / 4000000000000)) (orderedInterval (-58722718730 / 1000000000000) (-58722702076 / 1000000000000), orderedInterval (32053649395 / 1000000000000) (32053666049 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 81 12 (1012574398398719 / 4000000000000)) (orderedInterval (25804585649 / 1000000000000) (25804588955 / 1000000000000), orderedInterval (-43050758792 / 1000000000000) (-43050755486 / 1000000000000))) = true
  norm_num [besselStateAtRationalPoint, besselIntervalStepZero,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, besselZeroTransition,
    besselInitial, besselGridStateAt, besselGridStateBlock00, besselGridStateBlock01,
    besselGridStateBlock02, besselGridStateBlock03, besselGridStateBlock04,
    besselGridStateBlock05, besselGridStateBlock06, besselGridStateBlock07,
    besselGridStateBlock08, besselGridStateBlock09, besselGridStateBlock10,
    besselGridStateBlock11, besselGridStateBlock12, besselGridStateBlock13,
    besselGridStateBlock14, besselGridState008, besselGridState010, besselGridState016, besselGridState019, besselGridState020, besselGridState026, besselGridState028, besselGridState031, besselGridState035, besselGridState036, besselGridState038, besselGridState041, besselGridState042, besselGridState044, besselGridState045, besselGridState051, besselGridState054, besselGridState055, besselGridState061, besselGridState065, besselGridState070, besselGridState075, besselGridState079, besselGridState081, besselStateSubset, linearInterval, widenInterval,
    rationalErrorInterval, rationalIntervalSubset, orderedInterval, Finset.sum_range_succ,
    IntervalRat.add, IntervalRat.mul, IntervalRat.scale, IntervalRat.singleton]

theorem compactCertificate233_stateChecks4 :
    compactCertificate233.stateChecks 12 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 75 12 (946078350680411 / 4000000000000)) (orderedInterval (-51542714936 / 1000000000000) (-51542714521 / 1000000000000), orderedInterval (6021500359 / 1000000000000) (6021500773 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 54 12 (675166152389963 / 4000000000000)) (orderedInterval (-4283645862 / 1000000000000) (-4283645851 / 1000000000000), orderedInterval (61276870945 / 1000000000000) (61276870957 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 61 12 (765566456945277 / 4000000000000)) (orderedInterval (-29612912999 / 1000000000000) (-29612912998 / 1000000000000), orderedInterval (-49413532493 / 1000000000000) (-49413532492 / 1000000000000))) = true
  norm_num [besselStateAtRationalPoint, besselIntervalStepZero,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, besselZeroTransition,
    besselInitial, besselGridStateAt, besselGridStateBlock00, besselGridStateBlock01,
    besselGridStateBlock02, besselGridStateBlock03, besselGridStateBlock04,
    besselGridStateBlock05, besselGridStateBlock06, besselGridStateBlock07,
    besselGridStateBlock08, besselGridStateBlock09, besselGridStateBlock10,
    besselGridStateBlock11, besselGridStateBlock12, besselGridStateBlock13,
    besselGridStateBlock14, besselGridState008, besselGridState010, besselGridState016, besselGridState019, besselGridState020, besselGridState026, besselGridState028, besselGridState031, besselGridState035, besselGridState036, besselGridState038, besselGridState041, besselGridState042, besselGridState044, besselGridState045, besselGridState051, besselGridState054, besselGridState055, besselGridState061, besselGridState065, besselGridState070, besselGridState075, besselGridState079, besselGridState081, besselStateSubset, linearInterval, widenInterval,
    rationalErrorInterval, rationalIntervalSubset, orderedInterval, Finset.sum_range_succ,
    IntervalRat.add, IntervalRat.mul, IntervalRat.scale, IntervalRat.singleton]

theorem compactCertificate233_stateChecks5 :
    compactCertificate233.stateChecks 15 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 51 12 (638249497485613 / 4000000000000)) (orderedInterval (-7922897631 / 1000000000000) (-7922897630 / 1000000000000), orderedInterval (-62641216288 / 1000000000000) (-62641216287 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 45 12 (563912787193873 / 4000000000000)) (orderedInterval (-25612833633 / 1000000000000) (-25612833632 / 1000000000000), orderedInterval (-62035927231 / 1000000000000) (-62035927230 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 65 12 (163443905285427 / 800000000000)) (orderedInterval (-43241414920 / 1000000000000) (-43241414919 / 1000000000000), orderedInterval (-35195823162 / 1000000000000) (-35195823161 / 1000000000000))) = true
  norm_num [besselStateAtRationalPoint, besselIntervalStepZero,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, besselZeroTransition,
    besselInitial, besselGridStateAt, besselGridStateBlock00, besselGridStateBlock01,
    besselGridStateBlock02, besselGridStateBlock03, besselGridStateBlock04,
    besselGridStateBlock05, besselGridStateBlock06, besselGridStateBlock07,
    besselGridStateBlock08, besselGridStateBlock09, besselGridStateBlock10,
    besselGridStateBlock11, besselGridStateBlock12, besselGridStateBlock13,
    besselGridStateBlock14, besselGridState008, besselGridState010, besselGridState016, besselGridState019, besselGridState020, besselGridState026, besselGridState028, besselGridState031, besselGridState035, besselGridState036, besselGridState038, besselGridState041, besselGridState042, besselGridState044, besselGridState045, besselGridState051, besselGridState054, besselGridState055, besselGridState061, besselGridState065, besselGridState070, besselGridState075, besselGridState079, besselGridState081, besselStateSubset, linearInterval, widenInterval,
    rationalErrorInterval, rationalIntervalSubset, orderedInterval, Finset.sum_range_succ,
    IntervalRat.add, IntervalRat.mul, IntervalRat.scale, IntervalRat.singleton]

theorem compactCertificate233_stateChecks6 :
    compactCertificate233.stateChecks 18 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 36 12 (452094443600969 / 4000000000000)) (orderedInterval (48952721370 / 1000000000000) (48952721371 / 1000000000000), orderedInterval (56671630188 / 1000000000000) (56671630189 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 31 12 (383245466649409 / 4000000000000)) (orderedInterval (58127211027 / 1000000000000) (58127290955 / 1000000000000), orderedInterval (-57449962543 / 1000000000000) (-57449882616 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 19 12 (239817218371627 / 4000000000000)) (orderedInterval (-89246894548 / 1000000000000) (-89246894547 / 1000000000000), orderedInterval (-50765212243 / 1000000000000) (-50765212242 / 1000000000000))) = true
  norm_num [besselStateAtRationalPoint, besselIntervalStepZero,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, besselZeroTransition,
    besselInitial, besselGridStateAt, besselGridStateBlock00, besselGridStateBlock01,
    besselGridStateBlock02, besselGridStateBlock03, besselGridStateBlock04,
    besselGridStateBlock05, besselGridStateBlock06, besselGridStateBlock07,
    besselGridStateBlock08, besselGridStateBlock09, besselGridStateBlock10,
    besselGridStateBlock11, besselGridStateBlock12, besselGridStateBlock13,
    besselGridStateBlock14, besselGridState008, besselGridState010, besselGridState016, besselGridState019, besselGridState020, besselGridState026, besselGridState028, besselGridState031, besselGridState035, besselGridState036, besselGridState038, besselGridState041, besselGridState042, besselGridState044, besselGridState045, besselGridState051, besselGridState054, besselGridState055, besselGridState061, besselGridState065, besselGridState070, besselGridState075, besselGridState079, besselGridState081, besselStateSubset, linearInterval, widenInterval,
    rationalErrorInterval, rationalIntervalSubset, orderedInterval, Finset.sum_range_succ,
    IntervalRat.add, IntervalRat.mul, IntervalRat.scale, IntervalRat.singleton]

theorem compactCertificate233_stateChecks7 :
    compactCertificate233.stateChecks 21 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 10 12 (128974497636309 / 4000000000000)) (orderedInterval (140401379816 / 1000000000000) (140401379852 / 1000000000000), orderedInterval (-7574889266 / 1000000000000) (-7574889229 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 28 12 (350190850195927 / 4000000000000)) (orderedInterval (30604630057 / 1000000000000) (30604630058 / 1000000000000), orderedInterval (79418772617 / 1000000000000) (79418772618 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 38 12 (478155667205879 / 4000000000000)) (orderedInterval (59050901862 / 1000000000000) (59050901863 / 1000000000000), orderedInterval (42631959464 / 1000000000000) (42631959465 / 1000000000000))) = true
  norm_num [besselStateAtRationalPoint, besselIntervalStepZero,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, besselZeroTransition,
    besselInitial, besselGridStateAt, besselGridStateBlock00, besselGridStateBlock01,
    besselGridStateBlock02, besselGridStateBlock03, besselGridStateBlock04,
    besselGridStateBlock05, besselGridStateBlock06, besselGridStateBlock07,
    besselGridStateBlock08, besselGridStateBlock09, besselGridStateBlock10,
    besselGridStateBlock11, besselGridStateBlock12, besselGridStateBlock13,
    besselGridStateBlock14, besselGridState008, besselGridState010, besselGridState016, besselGridState019, besselGridState020, besselGridState026, besselGridState028, besselGridState031, besselGridState035, besselGridState036, besselGridState038, besselGridState041, besselGridState042, besselGridState044, besselGridState045, besselGridState051, besselGridState054, besselGridState055, besselGridState061, besselGridState065, besselGridState070, besselGridState075, besselGridState079, besselGridState081, besselStateSubset, linearInterval, widenInterval,
    rationalErrorInterval, rationalIntervalSubset, orderedInterval, Finset.sum_range_succ,
    IntervalRat.add, IntervalRat.mul, IntervalRat.scale, IntervalRat.singleton]

theorem compactCertificate233_stateChecks8 :
    compactCertificate233.stateChecks 24 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 16 12 (202182781628373 / 4000000000000)) (orderedInterval (98071297108 / 1000000000000) (98071297109 / 1000000000000), orderedInterval (53588483392 / 1000000000000) (53588483393 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 65 12 (821861782466933 / 4000000000000)) (orderedInterval (-49477743758 / 1000000000000) (-49477725336 / 1000000000000), orderedInterval (25622861365 / 1000000000000) (25622879787 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 44 12 (548965582273147 / 4000000000000)) (orderedInterval (-13810723259 / 1000000000000) (-13810723152 / 1000000000000), orderedInterval (66743480855 / 1000000000000) (66743480963 / 1000000000000))) = true
  norm_num [besselStateAtRationalPoint, besselIntervalStepZero,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, besselZeroTransition,
    besselInitial, besselGridStateAt, besselGridStateBlock00, besselGridStateBlock01,
    besselGridStateBlock02, besselGridStateBlock03, besselGridStateBlock04,
    besselGridStateBlock05, besselGridStateBlock06, besselGridStateBlock07,
    besselGridStateBlock08, besselGridStateBlock09, besselGridStateBlock10,
    besselGridStateBlock11, besselGridStateBlock12, besselGridStateBlock13,
    besselGridStateBlock14, besselGridState008, besselGridState010, besselGridState016, besselGridState019, besselGridState020, besselGridState026, besselGridState028, besselGridState031, besselGridState035, besselGridState036, besselGridState038, besselGridState041, besselGridState042, besselGridState044, besselGridState045, besselGridState051, besselGridState054, besselGridState055, besselGridState061, besselGridState065, besselGridState070, besselGridState075, besselGridState079, besselGridState081, besselStateSubset, linearInterval, widenInterval,
    rationalErrorInterval, rationalIntervalSubset, orderedInterval, Finset.sum_range_succ,
    IntervalRat.add, IntervalRat.mul, IntervalRat.scale, IntervalRat.singleton]

theorem compactCertificate233_states : ∀ j,
    BesselStateValid (compactCertificate233.point j) (compactCertificate233.state j) :=
  compactCertificate233.statesValid_of_checks3 compactCertificate233_stateChecks0
    compactCertificate233_stateChecks1 compactCertificate233_stateChecks2
    compactCertificate233_stateChecks3 compactCertificate233_stateChecks4
    compactCertificate233_stateChecks5 compactCertificate233_stateChecks6
    compactCertificate233_stateChecks7 compactCertificate233_stateChecks8

theorem compactCertificate233_chunkChecks0_0 :
    compactCertificate233.chunkChecks (0 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 0) <| besselDerivativeNearFromState (221 / 2) 0 (IntervalRat.scale (221 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-73685899654 / 1000000000000) (-73685899653 / 1000000000000), orderedInterval (-17876499077 / 1000000000000) (-17876499076 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 0) <| besselDerivativeNearFromState (325575199486121 / 4000000000000) 0 (IntervalRat.scale (221 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (42108495392 / 1000000000000) (42108495393 / 1000000000000), orderedInterval (77513008893 / 1000000000000) (77513008894 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 0) <| besselDerivativeNearFromState (105284330149193 / 800000000000) 0 (IntervalRat.scale (221 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (29811131399 / 1000000000000) (29811131400 / 1000000000000), orderedInterval (62725073027 / 1000000000000) (62725073028 / 1000000000000)))) (orderedInterval (-27064790443 / 1000000000000) (-27064790434 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 0) <| besselDerivativeNearFromState (95002031213947 / 4000000000000) 0 (IntervalRat.scale (221 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-92716106700 / 1000000000000) (-92716087555 / 1000000000000), orderedInterval (136896619544 / 1000000000000) (136896638688 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 0) <| besselDerivativeNearFromState (255188818981759 / 4000000000000) 0 (IntervalRat.scale (221 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (98314204580 / 1000000000000) (98314204891 / 1000000000000), orderedInterval (-18457575300 / 1000000000000) (-18457574989 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 0) <| besselDerivativeNearFromState (692887284830403 / 4000000000000) 0 (IntervalRat.scale (221 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-56908164397 / 1000000000000) (-56908164396 / 1000000000000), orderedInterval (-20731189509 / 1000000000000) (-20731189508 / 1000000000000)))) (orderedInterval (8641108050 / 1000000000000) (8641108283 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 0) <| besselDerivativeNearFromState (510377637963739 / 4000000000000) 0 (IntervalRat.scale (221 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (29219068658 / 1000000000000) (29219070539 / 1000000000000), orderedInterval (-64423696834 / 1000000000000) (-64423694953 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 0) <| besselDerivativeNearFromState (874540781759047 / 4000000000000) 0 (IntervalRat.scale (221 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-25465083330 / 1000000000000) (-25465080995 / 1000000000000), orderedInterval (47632637688 / 1000000000000) (47632640022 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 0) <| besselDerivativeNearFromState (644182781628373 / 4000000000000) 0 (IntervalRat.scale (221 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-62826941252 / 1000000000000) (-62826941162 / 1000000000000), orderedInterval (2602250683 / 1000000000000) (2602250773 / 1000000000000)))) (orderedInterval (-732958232 / 1000000000000) (-732958151 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate233_chunkChecks0_1 :
    compactCertificate233.chunkChecks (0 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 0) <| besselDerivativeNearFromState (988342046054779 / 4000000000000) 0 (IntervalRat.scale (221 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (15746148157 / 1000000000000) (15746148387 / 1000000000000), orderedInterval (-48287216490 / 1000000000000) (-48287216259 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 0) <| besselDerivativeNearFromState (570619546341091 / 4000000000000) 0 (IntervalRat.scale (221 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-58722718730 / 1000000000000) (-58722702076 / 1000000000000), orderedInterval (32053649395 / 1000000000000) (32053666049 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 0) <| besselDerivativeNearFromState (1012574398398719 / 4000000000000) 0 (IntervalRat.scale (221 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (25804585649 / 1000000000000) (25804588955 / 1000000000000), orderedInterval (-43050758792 / 1000000000000) (-43050755486 / 1000000000000)))) (orderedInterval (-3480496810 / 1000000000000) (-3480495020 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 0) <| besselDerivativeNearFromState (946078350680411 / 4000000000000) 0 (IntervalRat.scale (221 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-51542714936 / 1000000000000) (-51542714521 / 1000000000000), orderedInterval (6021500359 / 1000000000000) (6021500773 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 0) <| besselDerivativeNearFromState (675166152389963 / 4000000000000) 0 (IntervalRat.scale (221 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-4283645862 / 1000000000000) (-4283645851 / 1000000000000), orderedInterval (61276870945 / 1000000000000) (61276870957 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 0) <| besselDerivativeNearFromState (765566456945277 / 4000000000000) 0 (IntervalRat.scale (221 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-29612912999 / 1000000000000) (-29612912998 / 1000000000000), orderedInterval (-49413532493 / 1000000000000) (-49413532492 / 1000000000000)))) (orderedInterval (675289618 / 1000000000000) (675289641 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 0) <| besselDerivativeNearFromState (638249497485613 / 4000000000000) 0 (IntervalRat.scale (221 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-7922897631 / 1000000000000) (-7922897630 / 1000000000000), orderedInterval (-62641216288 / 1000000000000) (-62641216287 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 0) <| besselDerivativeNearFromState (563912787193873 / 4000000000000) 0 (IntervalRat.scale (221 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-25612833633 / 1000000000000) (-25612833632 / 1000000000000), orderedInterval (-62035927231 / 1000000000000) (-62035927230 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 0) <| besselDerivativeNearFromState (163443905285427 / 800000000000) 0 (IntervalRat.scale (221 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-43241414920 / 1000000000000) (-43241414919 / 1000000000000), orderedInterval (-35195823162 / 1000000000000) (-35195823161 / 1000000000000)))) (orderedInterval (267095319 / 1000000000000) (267095330 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate233_chunkChecks0_2 :
    compactCertificate233.chunkChecks (0 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 0) <| besselDerivativeNearFromState (452094443600969 / 4000000000000) 0 (IntervalRat.scale (221 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (48952721370 / 1000000000000) (48952721371 / 1000000000000), orderedInterval (56671630188 / 1000000000000) (56671630189 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 0) <| besselDerivativeNearFromState (383245466649409 / 4000000000000) 0 (IntervalRat.scale (221 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (58127211027 / 1000000000000) (58127290955 / 1000000000000), orderedInterval (-57449962543 / 1000000000000) (-57449882616 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 0) <| besselDerivativeNearFromState (239817218371627 / 4000000000000) 0 (IntervalRat.scale (221 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-89246894548 / 1000000000000) (-89246894547 / 1000000000000), orderedInterval (-50765212243 / 1000000000000) (-50765212242 / 1000000000000)))) (orderedInterval (-14022629125 / 1000000000000) (-14022624573 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 0) <| besselDerivativeNearFromState (128974497636309 / 4000000000000) 0 (IntervalRat.scale (221 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (140401379816 / 1000000000000) (140401379852 / 1000000000000), orderedInterval (-7574889266 / 1000000000000) (-7574889229 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 0) <| besselDerivativeNearFromState (350190850195927 / 4000000000000) 0 (IntervalRat.scale (221 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (30604630057 / 1000000000000) (30604630058 / 1000000000000), orderedInterval (79418772617 / 1000000000000) (79418772618 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 0) <| besselDerivativeNearFromState (478155667205879 / 4000000000000) 0 (IntervalRat.scale (221 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (59050901862 / 1000000000000) (59050901863 / 1000000000000), orderedInterval (42631959464 / 1000000000000) (42631959465 / 1000000000000)))) (orderedInterval (-7812445323 / 1000000000000) (-7812445308 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 0) <| besselDerivativeNearFromState (202182781628373 / 4000000000000) 0 (IntervalRat.scale (221 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (98071297108 / 1000000000000) (98071297109 / 1000000000000), orderedInterval (53588483392 / 1000000000000) (53588483393 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 0) <| besselDerivativeNearFromState (821861782466933 / 4000000000000) 0 (IntervalRat.scale (221 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-49477743758 / 1000000000000) (-49477725336 / 1000000000000), orderedInterval (25622861365 / 1000000000000) (25622879787 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 0) <| besselDerivativeNearFromState (548965582273147 / 4000000000000) 0 (IntervalRat.scale (221 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-13810723259 / 1000000000000) (-13810723152 / 1000000000000), orderedInterval (66743480855 / 1000000000000) (66743480963 / 1000000000000)))) (orderedInterval (7210038715 / 1000000000000) (7210040266 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate233_chunkChecks0 :
    compactCertificate233.chunkChecks (0 : Fin 5) 0 9 = true :=
  compactCertificate233.chunkChecks_nine_of_three (0 : Fin 5) compactCertificate233_chunkChecks0_0
    compactCertificate233_chunkChecks0_1 compactCertificate233_chunkChecks0_2

theorem compactCertificate233_chunkChecks1_0 :
    compactCertificate233.chunkChecks (1 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 1) <| besselDerivativeNearFromState (221 / 2) 1 (IntervalRat.scale (221 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-73685899654 / 1000000000000) (-73685899653 / 1000000000000), orderedInterval (-17876499077 / 1000000000000) (-17876499076 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 1) <| besselDerivativeNearFromState (325575199486121 / 4000000000000) 1 (IntervalRat.scale (221 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (42108495392 / 1000000000000) (42108495393 / 1000000000000), orderedInterval (77513008893 / 1000000000000) (77513008894 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 1) <| besselDerivativeNearFromState (105284330149193 / 800000000000) 1 (IntervalRat.scale (221 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (29811131399 / 1000000000000) (29811131400 / 1000000000000), orderedInterval (62725073027 / 1000000000000) (62725073028 / 1000000000000)))) (orderedInterval (-2169792352 / 1000000000000) (-2169792342 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 1) <| besselDerivativeNearFromState (95002031213947 / 4000000000000) 1 (IntervalRat.scale (221 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-92716106700 / 1000000000000) (-92716087555 / 1000000000000), orderedInterval (136896619544 / 1000000000000) (136896638688 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 1) <| besselDerivativeNearFromState (255188818981759 / 4000000000000) 1 (IntervalRat.scale (221 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (98314204580 / 1000000000000) (98314204891 / 1000000000000), orderedInterval (-18457575300 / 1000000000000) (-18457574989 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 1) <| besselDerivativeNearFromState (692887284830403 / 4000000000000) 1 (IntervalRat.scale (221 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-56908164397 / 1000000000000) (-56908164396 / 1000000000000), orderedInterval (-20731189509 / 1000000000000) (-20731189508 / 1000000000000)))) (orderedInterval (1601995525 / 1000000000000) (1601995592 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 1) <| besselDerivativeNearFromState (510377637963739 / 4000000000000) 1 (IntervalRat.scale (221 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (29219068658 / 1000000000000) (29219070539 / 1000000000000), orderedInterval (-64423696834 / 1000000000000) (-64423694953 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 1) <| besselDerivativeNearFromState (874540781759047 / 4000000000000) 1 (IntervalRat.scale (221 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-25465083330 / 1000000000000) (-25465080995 / 1000000000000), orderedInterval (47632637688 / 1000000000000) (47632640022 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 1) <| besselDerivativeNearFromState (644182781628373 / 4000000000000) 1 (IntervalRat.scale (221 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-62826941252 / 1000000000000) (-62826941162 / 1000000000000), orderedInterval (2602250683 / 1000000000000) (2602250773 / 1000000000000)))) (orderedInterval (-2815261097 / 1000000000000) (-2815260940 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate233_chunkChecks1_1 :
    compactCertificate233.chunkChecks (1 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 1) <| besselDerivativeNearFromState (988342046054779 / 4000000000000) 1 (IntervalRat.scale (221 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (15746148157 / 1000000000000) (15746148387 / 1000000000000), orderedInterval (-48287216490 / 1000000000000) (-48287216259 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 1) <| besselDerivativeNearFromState (570619546341091 / 4000000000000) 1 (IntervalRat.scale (221 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-58722718730 / 1000000000000) (-58722702076 / 1000000000000), orderedInterval (32053649395 / 1000000000000) (32053666049 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 1) <| besselDerivativeNearFromState (1012574398398719 / 4000000000000) 1 (IntervalRat.scale (221 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (25804585649 / 1000000000000) (25804588955 / 1000000000000), orderedInterval (-43050758792 / 1000000000000) (-43050755486 / 1000000000000)))) (orderedInterval (8231509256 / 1000000000000) (8231512109 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 1) <| besselDerivativeNearFromState (946078350680411 / 4000000000000) 1 (IntervalRat.scale (221 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-51542714936 / 1000000000000) (-51542714521 / 1000000000000), orderedInterval (6021500359 / 1000000000000) (6021500773 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 1) <| besselDerivativeNearFromState (675166152389963 / 4000000000000) 1 (IntervalRat.scale (221 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-4283645862 / 1000000000000) (-4283645851 / 1000000000000), orderedInterval (61276870945 / 1000000000000) (61276870957 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 1) <| besselDerivativeNearFromState (765566456945277 / 4000000000000) 1 (IntervalRat.scale (221 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-29612912999 / 1000000000000) (-29612912998 / 1000000000000), orderedInterval (-49413532493 / 1000000000000) (-49413532492 / 1000000000000)))) (orderedInterval (9051707391 / 1000000000000) (9051707431 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 1) <| besselDerivativeNearFromState (638249497485613 / 4000000000000) 1 (IntervalRat.scale (221 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-7922897631 / 1000000000000) (-7922897630 / 1000000000000), orderedInterval (-62641216288 / 1000000000000) (-62641216287 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 1) <| besselDerivativeNearFromState (563912787193873 / 4000000000000) 1 (IntervalRat.scale (221 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-25612833633 / 1000000000000) (-25612833632 / 1000000000000), orderedInterval (-62035927231 / 1000000000000) (-62035927230 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 1) <| besselDerivativeNearFromState (163443905285427 / 800000000000) 1 (IntervalRat.scale (221 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-43241414920 / 1000000000000) (-43241414919 / 1000000000000), orderedInterval (-35195823162 / 1000000000000) (-35195823161 / 1000000000000)))) (orderedInterval (1818617870 / 1000000000000) (1818617886 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate233_chunkChecks1_2 :
    compactCertificate233.chunkChecks (1 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 1) <| besselDerivativeNearFromState (452094443600969 / 4000000000000) 1 (IntervalRat.scale (221 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (48952721370 / 1000000000000) (48952721371 / 1000000000000), orderedInterval (56671630188 / 1000000000000) (56671630189 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 1) <| besselDerivativeNearFromState (383245466649409 / 4000000000000) 1 (IntervalRat.scale (221 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (58127211027 / 1000000000000) (58127290955 / 1000000000000), orderedInterval (-57449962543 / 1000000000000) (-57449882616 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 1) <| besselDerivativeNearFromState (239817218371627 / 4000000000000) 1 (IntervalRat.scale (221 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-89246894548 / 1000000000000) (-89246894547 / 1000000000000), orderedInterval (-50765212243 / 1000000000000) (-50765212242 / 1000000000000)))) (orderedInterval (-7345585151 / 1000000000000) (-7345581202 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 1) <| besselDerivativeNearFromState (128974497636309 / 4000000000000) 1 (IntervalRat.scale (221 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (140401379816 / 1000000000000) (140401379852 / 1000000000000), orderedInterval (-7574889266 / 1000000000000) (-7574889229 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 1) <| besselDerivativeNearFromState (350190850195927 / 4000000000000) 1 (IntervalRat.scale (221 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (30604630057 / 1000000000000) (30604630058 / 1000000000000), orderedInterval (79418772617 / 1000000000000) (79418772618 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 1) <| besselDerivativeNearFromState (478155667205879 / 4000000000000) 1 (IntervalRat.scale (221 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (59050901862 / 1000000000000) (59050901863 / 1000000000000), orderedInterval (42631959464 / 1000000000000) (42631959465 / 1000000000000)))) (orderedInterval (-4921227100 / 1000000000000) (-4921227087 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 1) <| besselDerivativeNearFromState (202182781628373 / 4000000000000) 1 (IntervalRat.scale (221 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (98071297108 / 1000000000000) (98071297109 / 1000000000000), orderedInterval (53588483392 / 1000000000000) (53588483393 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 1) <| besselDerivativeNearFromState (821861782466933 / 4000000000000) 1 (IntervalRat.scale (221 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-49477743758 / 1000000000000) (-49477725336 / 1000000000000), orderedInterval (25622861365 / 1000000000000) (25622879787 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 1) <| besselDerivativeNearFromState (548965582273147 / 4000000000000) 1 (IntervalRat.scale (221 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-13810723259 / 1000000000000) (-13810723152 / 1000000000000), orderedInterval (66743480855 / 1000000000000) (66743480963 / 1000000000000)))) (orderedInterval (-19283922819 / 1000000000000) (-19283919962 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate233_chunkChecks1 :
    compactCertificate233.chunkChecks (1 : Fin 5) 0 9 = true :=
  compactCertificate233.chunkChecks_nine_of_three (1 : Fin 5) compactCertificate233_chunkChecks1_0
    compactCertificate233_chunkChecks1_1 compactCertificate233_chunkChecks1_2

theorem compactCertificate233_chunkChecks2_0 :
    compactCertificate233.chunkChecks (2 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 2) <| besselDerivativeNearFromState (221 / 2) 2 (IntervalRat.scale (221 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-73685899654 / 1000000000000) (-73685899653 / 1000000000000), orderedInterval (-17876499077 / 1000000000000) (-17876499076 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 2) <| besselDerivativeNearFromState (325575199486121 / 4000000000000) 2 (IntervalRat.scale (221 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (42108495392 / 1000000000000) (42108495393 / 1000000000000), orderedInterval (77513008893 / 1000000000000) (77513008894 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 2) <| besselDerivativeNearFromState (105284330149193 / 800000000000) 2 (IntervalRat.scale (221 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (29811131399 / 1000000000000) (29811131400 / 1000000000000), orderedInterval (62725073027 / 1000000000000) (62725073028 / 1000000000000)))) (orderedInterval (26531840066 / 1000000000000) (26531840077 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 2) <| besselDerivativeNearFromState (95002031213947 / 4000000000000) 2 (IntervalRat.scale (221 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-92716106700 / 1000000000000) (-92716087555 / 1000000000000), orderedInterval (136896619544 / 1000000000000) (136896638688 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 2) <| besselDerivativeNearFromState (255188818981759 / 4000000000000) 2 (IntervalRat.scale (221 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (98314204580 / 1000000000000) (98314204891 / 1000000000000), orderedInterval (-18457575300 / 1000000000000) (-18457574989 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 2) <| besselDerivativeNearFromState (692887284830403 / 4000000000000) 2 (IntervalRat.scale (221 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-56908164397 / 1000000000000) (-56908164396 / 1000000000000), orderedInterval (-20731189509 / 1000000000000) (-20731189508 / 1000000000000)))) (orderedInterval (-11199229708 / 1000000000000) (-11199229672 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 2) <| besselDerivativeNearFromState (510377637963739 / 4000000000000) 2 (IntervalRat.scale (221 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (29219068658 / 1000000000000) (29219070539 / 1000000000000), orderedInterval (-64423696834 / 1000000000000) (-64423694953 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 2) <| besselDerivativeNearFromState (874540781759047 / 4000000000000) 2 (IntervalRat.scale (221 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-25465083330 / 1000000000000) (-25465080995 / 1000000000000), orderedInterval (47632637688 / 1000000000000) (47632640022 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 2) <| besselDerivativeNearFromState (644182781628373 / 4000000000000) 2 (IntervalRat.scale (221 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-62826941252 / 1000000000000) (-62826941162 / 1000000000000), orderedInterval (2602250683 / 1000000000000) (2602250773 / 1000000000000)))) (orderedInterval (175805383 / 1000000000000) (175805691 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate233_chunkChecks2_1 :
    compactCertificate233.chunkChecks (2 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 2) <| besselDerivativeNearFromState (988342046054779 / 4000000000000) 2 (IntervalRat.scale (221 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (15746148157 / 1000000000000) (15746148387 / 1000000000000), orderedInterval (-48287216490 / 1000000000000) (-48287216259 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 2) <| besselDerivativeNearFromState (570619546341091 / 4000000000000) 2 (IntervalRat.scale (221 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-58722718730 / 1000000000000) (-58722702076 / 1000000000000), orderedInterval (32053649395 / 1000000000000) (32053666049 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 2) <| besselDerivativeNearFromState (1012574398398719 / 4000000000000) 2 (IntervalRat.scale (221 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (25804585649 / 1000000000000) (25804588955 / 1000000000000), orderedInterval (-43050758792 / 1000000000000) (-43050755486 / 1000000000000)))) (orderedInterval (1914665123 / 1000000000000) (1914670070 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 2) <| besselDerivativeNearFromState (946078350680411 / 4000000000000) 2 (IntervalRat.scale (221 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-51542714936 / 1000000000000) (-51542714521 / 1000000000000), orderedInterval (6021500359 / 1000000000000) (6021500773 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 2) <| besselDerivativeNearFromState (675166152389963 / 4000000000000) 2 (IntervalRat.scale (221 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-4283645862 / 1000000000000) (-4283645851 / 1000000000000), orderedInterval (61276870945 / 1000000000000) (61276870957 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 2) <| besselDerivativeNearFromState (765566456945277 / 4000000000000) 2 (IntervalRat.scale (221 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-29612912999 / 1000000000000) (-29612912998 / 1000000000000), orderedInterval (-49413532493 / 1000000000000) (-49413532492 / 1000000000000)))) (orderedInterval (-3849447234 / 1000000000000) (-3849447161 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 2) <| besselDerivativeNearFromState (638249497485613 / 4000000000000) 2 (IntervalRat.scale (221 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-7922897631 / 1000000000000) (-7922897630 / 1000000000000), orderedInterval (-62641216288 / 1000000000000) (-62641216287 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 2) <| besselDerivativeNearFromState (563912787193873 / 4000000000000) 2 (IntervalRat.scale (221 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-25612833633 / 1000000000000) (-25612833632 / 1000000000000), orderedInterval (-62035927231 / 1000000000000) (-62035927230 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 2) <| besselDerivativeNearFromState (163443905285427 / 800000000000) 2 (IntervalRat.scale (221 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-43241414920 / 1000000000000) (-43241414919 / 1000000000000), orderedInterval (-35195823162 / 1000000000000) (-35195823161 / 1000000000000)))) (orderedInterval (1573278585 / 1000000000000) (1573278609 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate233_chunkChecks2_2 :
    compactCertificate233.chunkChecks (2 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 2) <| besselDerivativeNearFromState (452094443600969 / 4000000000000) 2 (IntervalRat.scale (221 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (48952721370 / 1000000000000) (48952721371 / 1000000000000), orderedInterval (56671630188 / 1000000000000) (56671630189 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 2) <| besselDerivativeNearFromState (383245466649409 / 4000000000000) 2 (IntervalRat.scale (221 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (58127211027 / 1000000000000) (58127290955 / 1000000000000), orderedInterval (-57449962543 / 1000000000000) (-57449882616 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 2) <| besselDerivativeNearFromState (239817218371627 / 4000000000000) 2 (IntervalRat.scale (221 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-89246894548 / 1000000000000) (-89246894547 / 1000000000000), orderedInterval (-50765212243 / 1000000000000) (-50765212242 / 1000000000000)))) (orderedInterval (11584029056 / 1000000000000) (11584032518 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 2) <| besselDerivativeNearFromState (128974497636309 / 4000000000000) 2 (IntervalRat.scale (221 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (140401379816 / 1000000000000) (140401379852 / 1000000000000), orderedInterval (-7574889266 / 1000000000000) (-7574889229 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 2) <| besselDerivativeNearFromState (350190850195927 / 4000000000000) 2 (IntervalRat.scale (221 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (30604630057 / 1000000000000) (30604630058 / 1000000000000), orderedInterval (79418772617 / 1000000000000) (79418772618 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 2) <| besselDerivativeNearFromState (478155667205879 / 4000000000000) 2 (IntervalRat.scale (221 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (59050901862 / 1000000000000) (59050901863 / 1000000000000), orderedInterval (42631959464 / 1000000000000) (42631959465 / 1000000000000)))) (orderedInterval (5997383295 / 1000000000000) (5997383308 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 2) <| besselDerivativeNearFromState (202182781628373 / 4000000000000) 2 (IntervalRat.scale (221 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (98071297108 / 1000000000000) (98071297109 / 1000000000000), orderedInterval (53588483392 / 1000000000000) (53588483393 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 2) <| besselDerivativeNearFromState (821861782466933 / 4000000000000) 2 (IntervalRat.scale (221 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-49477743758 / 1000000000000) (-49477725336 / 1000000000000), orderedInterval (25622861365 / 1000000000000) (25622879787 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 2) <| besselDerivativeNearFromState (548965582273147 / 4000000000000) 2 (IntervalRat.scale (221 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-13810723259 / 1000000000000) (-13810723152 / 1000000000000), orderedInterval (66743480855 / 1000000000000) (66743480963 / 1000000000000)))) (orderedInterval (-17871444354 / 1000000000000) (-17871439048 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate233_chunkChecks2 :
    compactCertificate233.chunkChecks (2 : Fin 5) 0 9 = true :=
  compactCertificate233.chunkChecks_nine_of_three (2 : Fin 5) compactCertificate233_chunkChecks2_0
    compactCertificate233_chunkChecks2_1 compactCertificate233_chunkChecks2_2

theorem compactCertificate233_chunkChecks3_0 :
    compactCertificate233.chunkChecks (3 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 3) <| besselDerivativeNearFromState (221 / 2) 3 (IntervalRat.scale (221 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-73685899654 / 1000000000000) (-73685899653 / 1000000000000), orderedInterval (-17876499077 / 1000000000000) (-17876499076 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 3) <| besselDerivativeNearFromState (325575199486121 / 4000000000000) 3 (IntervalRat.scale (221 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (42108495392 / 1000000000000) (42108495393 / 1000000000000), orderedInterval (77513008893 / 1000000000000) (77513008894 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 3) <| besselDerivativeNearFromState (105284330149193 / 800000000000) 3 (IntervalRat.scale (221 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (29811131399 / 1000000000000) (29811131400 / 1000000000000), orderedInterval (62725073027 / 1000000000000) (62725073028 / 1000000000000)))) (orderedInterval (338337826 / 1000000000000) (338337839 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 3) <| besselDerivativeNearFromState (95002031213947 / 4000000000000) 3 (IntervalRat.scale (221 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-92716106700 / 1000000000000) (-92716087555 / 1000000000000), orderedInterval (136896619544 / 1000000000000) (136896638688 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 3) <| besselDerivativeNearFromState (255188818981759 / 4000000000000) 3 (IntervalRat.scale (221 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (98314204580 / 1000000000000) (98314204891 / 1000000000000), orderedInterval (-18457575300 / 1000000000000) (-18457574989 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 3) <| besselDerivativeNearFromState (692887284830403 / 4000000000000) 3 (IntervalRat.scale (221 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-56908164397 / 1000000000000) (-56908164396 / 1000000000000), orderedInterval (-20731189509 / 1000000000000) (-20731189508 / 1000000000000)))) (orderedInterval (-5431501287 / 1000000000000) (-5431501250 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 3) <| besselDerivativeNearFromState (510377637963739 / 4000000000000) 3 (IntervalRat.scale (221 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (29219068658 / 1000000000000) (29219070539 / 1000000000000), orderedInterval (-64423696834 / 1000000000000) (-64423694953 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 3) <| besselDerivativeNearFromState (874540781759047 / 4000000000000) 3 (IntervalRat.scale (221 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-25465083330 / 1000000000000) (-25465080995 / 1000000000000), orderedInterval (47632637688 / 1000000000000) (47632640022 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 3) <| besselDerivativeNearFromState (644182781628373 / 4000000000000) 3 (IntervalRat.scale (221 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-62826941252 / 1000000000000) (-62826941162 / 1000000000000), orderedInterval (2602250683 / 1000000000000) (2602250773 / 1000000000000)))) (orderedInterval (11183654689 / 1000000000000) (11183655292 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate233_chunkChecks3_1 :
    compactCertificate233.chunkChecks (3 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 3) <| besselDerivativeNearFromState (988342046054779 / 4000000000000) 3 (IntervalRat.scale (221 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (15746148157 / 1000000000000) (15746148387 / 1000000000000), orderedInterval (-48287216490 / 1000000000000) (-48287216259 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 3) <| besselDerivativeNearFromState (570619546341091 / 4000000000000) 3 (IntervalRat.scale (221 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-58722718730 / 1000000000000) (-58722702076 / 1000000000000), orderedInterval (32053649395 / 1000000000000) (32053666049 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 3) <| besselDerivativeNearFromState (1012574398398719 / 4000000000000) 3 (IntervalRat.scale (221 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (25804585649 / 1000000000000) (25804588955 / 1000000000000), orderedInterval (-43050758792 / 1000000000000) (-43050755486 / 1000000000000)))) (orderedInterval (-27474608000 / 1000000000000) (-27474598766 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 3) <| besselDerivativeNearFromState (946078350680411 / 4000000000000) 3 (IntervalRat.scale (221 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-51542714936 / 1000000000000) (-51542714521 / 1000000000000), orderedInterval (6021500359 / 1000000000000) (6021500773 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 3) <| besselDerivativeNearFromState (675166152389963 / 4000000000000) 3 (IntervalRat.scale (221 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-4283645862 / 1000000000000) (-4283645851 / 1000000000000), orderedInterval (61276870945 / 1000000000000) (61276870957 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 3) <| besselDerivativeNearFromState (765566456945277 / 4000000000000) 3 (IntervalRat.scale (221 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-29612912999 / 1000000000000) (-29612912998 / 1000000000000), orderedInterval (-49413532493 / 1000000000000) (-49413532492 / 1000000000000)))) (orderedInterval (-20850707603 / 1000000000000) (-20850707464 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 3) <| besselDerivativeNearFromState (638249497485613 / 4000000000000) 3 (IntervalRat.scale (221 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-7922897631 / 1000000000000) (-7922897630 / 1000000000000), orderedInterval (-62641216288 / 1000000000000) (-62641216287 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 3) <| besselDerivativeNearFromState (563912787193873 / 4000000000000) 3 (IntervalRat.scale (221 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-25612833633 / 1000000000000) (-25612833632 / 1000000000000), orderedInterval (-62035927231 / 1000000000000) (-62035927230 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 3) <| besselDerivativeNearFromState (163443905285427 / 800000000000) 3 (IntervalRat.scale (221 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-43241414920 / 1000000000000) (-43241414919 / 1000000000000), orderedInterval (-35195823162 / 1000000000000) (-35195823161 / 1000000000000)))) (orderedInterval (487189892 / 1000000000000) (487189928 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate233_chunkChecks3_2 :
    compactCertificate233.chunkChecks (3 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 3) <| besselDerivativeNearFromState (452094443600969 / 4000000000000) 3 (IntervalRat.scale (221 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (48952721370 / 1000000000000) (48952721371 / 1000000000000), orderedInterval (56671630188 / 1000000000000) (56671630189 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 3) <| besselDerivativeNearFromState (383245466649409 / 4000000000000) 3 (IntervalRat.scale (221 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (58127211027 / 1000000000000) (58127290955 / 1000000000000), orderedInterval (-57449962543 / 1000000000000) (-57449882616 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 3) <| besselDerivativeNearFromState (239817218371627 / 4000000000000) 3 (IntervalRat.scale (221 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-89246894548 / 1000000000000) (-89246894547 / 1000000000000), orderedInterval (-50765212243 / 1000000000000) (-50765212242 / 1000000000000)))) (orderedInterval (7735346082 / 1000000000000) (7735349086 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 3) <| besselDerivativeNearFromState (128974497636309 / 4000000000000) 3 (IntervalRat.scale (221 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (140401379816 / 1000000000000) (140401379852 / 1000000000000), orderedInterval (-7574889266 / 1000000000000) (-7574889229 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 3) <| besselDerivativeNearFromState (350190850195927 / 4000000000000) 3 (IntervalRat.scale (221 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (30604630057 / 1000000000000) (30604630058 / 1000000000000), orderedInterval (79418772617 / 1000000000000) (79418772618 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 3) <| besselDerivativeNearFromState (478155667205879 / 4000000000000) 3 (IntervalRat.scale (221 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (59050901862 / 1000000000000) (59050901863 / 1000000000000), orderedInterval (42631959464 / 1000000000000) (42631959465 / 1000000000000)))) (orderedInterval (4974351833 / 1000000000000) (4974351846 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 3) <| besselDerivativeNearFromState (202182781628373 / 4000000000000) 3 (IntervalRat.scale (221 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (98071297108 / 1000000000000) (98071297109 / 1000000000000), orderedInterval (53588483392 / 1000000000000) (53588483393 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 3) <| besselDerivativeNearFromState (821861782466933 / 4000000000000) 3 (IntervalRat.scale (221 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-49477743758 / 1000000000000) (-49477725336 / 1000000000000), orderedInterval (25622861365 / 1000000000000) (25622879787 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 3) <| besselDerivativeNearFromState (548965582273147 / 4000000000000) 3 (IntervalRat.scale (221 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-13810723259 / 1000000000000) (-13810723152 / 1000000000000), orderedInterval (66743480855 / 1000000000000) (66743480963 / 1000000000000)))) (orderedInterval (37530355251 / 1000000000000) (37530365076 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate233_chunkChecks3 :
    compactCertificate233.chunkChecks (3 : Fin 5) 0 9 = true :=
  compactCertificate233.chunkChecks_nine_of_three (3 : Fin 5) compactCertificate233_chunkChecks3_0
    compactCertificate233_chunkChecks3_1 compactCertificate233_chunkChecks3_2

theorem compactCertificate233_chunkChecks4_0 :
    compactCertificate233.chunkChecks (4 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 4) <| besselDerivativeNearFromState (221 / 2) 4 (IntervalRat.scale (221 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-73685899654 / 1000000000000) (-73685899653 / 1000000000000), orderedInterval (-17876499077 / 1000000000000) (-17876499076 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 4) <| besselDerivativeNearFromState (325575199486121 / 4000000000000) 4 (IntervalRat.scale (221 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (42108495392 / 1000000000000) (42108495393 / 1000000000000), orderedInterval (77513008893 / 1000000000000) (77513008894 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 4) <| besselDerivativeNearFromState (105284330149193 / 800000000000) 4 (IntervalRat.scale (221 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (29811131399 / 1000000000000) (29811131400 / 1000000000000), orderedInterval (62725073027 / 1000000000000) (62725073028 / 1000000000000)))) (orderedInterval (-25575112746 / 1000000000000) (-25575112731 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 4) <| besselDerivativeNearFromState (95002031213947 / 4000000000000) 4 (IntervalRat.scale (221 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-92716106700 / 1000000000000) (-92716087555 / 1000000000000), orderedInterval (136896619544 / 1000000000000) (136896638688 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 4) <| besselDerivativeNearFromState (255188818981759 / 4000000000000) 4 (IntervalRat.scale (221 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (98314204580 / 1000000000000) (98314204891 / 1000000000000), orderedInterval (-18457575300 / 1000000000000) (-18457574989 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 4) <| besselDerivativeNearFromState (692887284830403 / 4000000000000) 4 (IntervalRat.scale (221 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-56908164397 / 1000000000000) (-56908164396 / 1000000000000), orderedInterval (-20731189509 / 1000000000000) (-20731189508 / 1000000000000)))) (orderedInterval (24929436279 / 1000000000000) (24929436330 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 4) <| besselDerivativeNearFromState (510377637963739 / 4000000000000) 4 (IntervalRat.scale (221 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (29219068658 / 1000000000000) (29219070539 / 1000000000000), orderedInterval (-64423696834 / 1000000000000) (-64423694953 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 4) <| besselDerivativeNearFromState (874540781759047 / 4000000000000) 4 (IntervalRat.scale (221 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-25465083330 / 1000000000000) (-25465080995 / 1000000000000), orderedInterval (47632637688 / 1000000000000) (47632640022 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 4) <| besselDerivativeNearFromState (644182781628373 / 4000000000000) 4 (IntervalRat.scale (221 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-62826941252 / 1000000000000) (-62826941162 / 1000000000000), orderedInterval (2602250683 / 1000000000000) (2602250773 / 1000000000000)))) (orderedInterval (4984700093 / 1000000000000) (4984701282 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate233_chunkChecks4_1 :
    compactCertificate233.chunkChecks (4 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 4) <| besselDerivativeNearFromState (988342046054779 / 4000000000000) 4 (IntervalRat.scale (221 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (15746148157 / 1000000000000) (15746148387 / 1000000000000), orderedInterval (-48287216490 / 1000000000000) (-48287216259 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 4) <| besselDerivativeNearFromState (570619546341091 / 4000000000000) 4 (IntervalRat.scale (221 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-58722718730 / 1000000000000) (-58722702076 / 1000000000000), orderedInterval (32053649395 / 1000000000000) (32053666049 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 4) <| besselDerivativeNearFromState (1012574398398719 / 4000000000000) 4 (IntervalRat.scale (221 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (25804585649 / 1000000000000) (25804588955 / 1000000000000), orderedInterval (-43050758792 / 1000000000000) (-43050755486 / 1000000000000)))) (orderedInterval (19501167379 / 1000000000000) (19501185878 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 4) <| besselDerivativeNearFromState (946078350680411 / 4000000000000) 4 (IntervalRat.scale (221 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-51542714936 / 1000000000000) (-51542714521 / 1000000000000), orderedInterval (6021500359 / 1000000000000) (6021500773 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 4) <| besselDerivativeNearFromState (675166152389963 / 4000000000000) 4 (IntervalRat.scale (221 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-4283645862 / 1000000000000) (-4283645851 / 1000000000000), orderedInterval (61276870945 / 1000000000000) (61276870957 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 4) <| besselDerivativeNearFromState (765566456945277 / 4000000000000) 4 (IntervalRat.scale (221 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-29612912999 / 1000000000000) (-29612912998 / 1000000000000), orderedInterval (-49413532493 / 1000000000000) (-49413532492 / 1000000000000)))) (orderedInterval (19052001533 / 1000000000000) (19052001802 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 4) <| besselDerivativeNearFromState (638249497485613 / 4000000000000) 4 (IntervalRat.scale (221 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-7922897631 / 1000000000000) (-7922897630 / 1000000000000), orderedInterval (-62641216288 / 1000000000000) (-62641216287 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 4) <| besselDerivativeNearFromState (563912787193873 / 4000000000000) 4 (IntervalRat.scale (221 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-25612833633 / 1000000000000) (-25612833632 / 1000000000000), orderedInterval (-62035927231 / 1000000000000) (-62035927230 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 4) <| besselDerivativeNearFromState (163443905285427 / 800000000000) 4 (IntervalRat.scale (221 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-43241414920 / 1000000000000) (-43241414919 / 1000000000000), orderedInterval (-35195823162 / 1000000000000) (-35195823161 / 1000000000000)))) (orderedInterval (-9461220010 / 1000000000000) (-9461219953 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate233_chunkChecks4_2 :
    compactCertificate233.chunkChecks (4 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 4) <| besselDerivativeNearFromState (452094443600969 / 4000000000000) 4 (IntervalRat.scale (221 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (48952721370 / 1000000000000) (48952721371 / 1000000000000), orderedInterval (56671630188 / 1000000000000) (56671630189 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 4) <| besselDerivativeNearFromState (383245466649409 / 4000000000000) 4 (IntervalRat.scale (221 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (58127211027 / 1000000000000) (58127290955 / 1000000000000), orderedInterval (-57449962543 / 1000000000000) (-57449882616 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 4) <| besselDerivativeNearFromState (239817218371627 / 4000000000000) 4 (IntervalRat.scale (221 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-89246894548 / 1000000000000) (-89246894547 / 1000000000000), orderedInterval (-50765212243 / 1000000000000) (-50765212242 / 1000000000000)))) (orderedInterval (-10817499632 / 1000000000000) (-10817496998 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 4) <| besselDerivativeNearFromState (128974497636309 / 4000000000000) 4 (IntervalRat.scale (221 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (140401379816 / 1000000000000) (140401379852 / 1000000000000), orderedInterval (-7574889266 / 1000000000000) (-7574889229 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 4) <| besselDerivativeNearFromState (350190850195927 / 4000000000000) 4 (IntervalRat.scale (221 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (30604630057 / 1000000000000) (30604630058 / 1000000000000), orderedInterval (79418772617 / 1000000000000) (79418772618 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 4) <| besselDerivativeNearFromState (478155667205879 / 4000000000000) 4 (IntervalRat.scale (221 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (59050901862 / 1000000000000) (59050901863 / 1000000000000), orderedInterval (42631959464 / 1000000000000) (42631959465 / 1000000000000)))) (orderedInterval (-6580092863 / 1000000000000) (-6580092849 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 4) <| besselDerivativeNearFromState (202182781628373 / 4000000000000) 4 (IntervalRat.scale (221 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (98071297108 / 1000000000000) (98071297109 / 1000000000000), orderedInterval (53588483392 / 1000000000000) (53588483393 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 4) <| besselDerivativeNearFromState (821861782466933 / 4000000000000) 4 (IntervalRat.scale (221 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-49477743758 / 1000000000000) (-49477725336 / 1000000000000), orderedInterval (25622861365 / 1000000000000) (25622879787 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 4) <| besselDerivativeNearFromState (548965582273147 / 4000000000000) 4 (IntervalRat.scale (221 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-13810723259 / 1000000000000) (-13810723152 / 1000000000000), orderedInterval (66743480855 / 1000000000000) (66743480963 / 1000000000000)))) (orderedInterval (53655962868 / 1000000000000) (53655981174 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate233_chunkChecks4 :
    compactCertificate233.chunkChecks (4 : Fin 5) 0 9 = true :=
  compactCertificate233.chunkChecks_nine_of_three (4 : Fin 5) compactCertificate233_chunkChecks4_0
    compactCertificate233_chunkChecks4_1 compactCertificate233_chunkChecks4_2

theorem compactCertificate233_chunks :
    ∀ r : Fin 5, ∀ b, compactCertificate233.chunkCheck r b = true :=
  compactCertificate233.chunkChecks_all (by
    intro r
    fin_cases r
    · exact compactCertificate233_chunkChecks0
    · exact compactCertificate233_chunkChecks1
    · exact compactCertificate233_chunkChecks2
    · exact compactCertificate233_chunkChecks3
    · exact compactCertificate233_chunkChecks4)

theorem compactCertificate233_coefficient0 :
    compactCertificate233.coefficientCheck (0 : Fin 5) = true := by
  norm_num [CompactCertificate.coefficientCheck, intervalFinSumHull,
    compactCertificate233, rationalIntervalSubset, orderedInterval, Fin.sum_univ_succ]

theorem compactCertificate233_coefficient1 :
    compactCertificate233.coefficientCheck (1 : Fin 5) = true := by
  norm_num [CompactCertificate.coefficientCheck, intervalFinSumHull,
    compactCertificate233, rationalIntervalSubset, orderedInterval, Fin.sum_univ_succ]

theorem compactCertificate233_coefficient2 :
    compactCertificate233.coefficientCheck (2 : Fin 5) = true := by
  norm_num [CompactCertificate.coefficientCheck, intervalFinSumHull,
    compactCertificate233, rationalIntervalSubset, orderedInterval, Fin.sum_univ_succ]

theorem compactCertificate233_coefficient3 :
    compactCertificate233.coefficientCheck (3 : Fin 5) = true := by
  norm_num [CompactCertificate.coefficientCheck, intervalFinSumHull,
    compactCertificate233, rationalIntervalSubset, orderedInterval, Fin.sum_univ_succ]

theorem compactCertificate233_coefficient4 :
    compactCertificate233.coefficientCheck (4 : Fin 5) = true := by
  norm_num [CompactCertificate.coefficientCheck, intervalFinSumHull,
    compactCertificate233, rationalIntervalSubset, orderedInterval, Fin.sum_univ_succ]

theorem compactCertificate233_coefficients : ∀ r : Fin 5,
    compactCertificate233.coefficientCheck r = true := by
  intro r
  fin_cases r
  · exact compactCertificate233_coefficient0
  · exact compactCertificate233_coefficient1
  · exact compactCertificate233_coefficient2
  · exact compactCertificate233_coefficient3
  · exact compactCertificate233_coefficient4

theorem compactCertificate233_lower : (1 : ℚ) ≤ compactCertificate233.output.lo := by
  norm_num [CompactCertificate.output, CompactCertificate.interval,
    CompactCertificate.coefficientTargetNat, compactCertificate233, dualConstant,
    intervalTaylorSum, intervalPow, intervalSub, intervalMaxAbs, widenInterval,
    rationalErrorInterval, orderedInterval, IntervalRat.add, IntervalRat.mul, IntervalRat.scale,
    IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4]

theorem compactCertificate233_proves {t : ℝ} (ht : t ∈ compactCertificate233.interval) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t :=
  compactCertificate233.proves compactCertificate233_states compactCertificate233_chunks
    compactCertificate233_coefficients compactCertificate233_lower ht

end Erdos232
