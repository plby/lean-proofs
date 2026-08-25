/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, OpenAI Codex
-/
import ErdosProblems.Erdos232.CompactBase

open LeanCert.Core
namespace Erdos232

def compactCertificate261 : CompactCertificate where
  left := 271 / 2
  right := 136
  center := 543 / 4
  grid := fun i =>
    match i.val with
    | 0 => 43
    | 1 => 32
    | 2 => 51
    | 3 => 9
    | 4 => 25
    | 5 => 68
    | 6 => 50
    | 7 => 86
    | 8 => 63
    | 9 => 97
    | 10 => 56
    | 11 => 99
    | 12 => 93
    | 13 => 66
    | 14 => 75
    | 15 => 62
    | 16 => 55
    | 17 => 80
    | 18 => 44
    | 19 => 37
    | 20 => 23
    | 21 => 13
    | 22 => 34
    | 23 => 47
    | 24 => 20
    | 25 => 80
    | _ => 54
  point := fun i =>
    match i.val with
    | 0 => 543 / 4
    | 1 => 799942684710243 / 8000000000000
    | 2 => 258685028375619 / 1600000000000
    | 3 => 233421280313001 / 8000000000000
    | 4 => 627002392339797 / 8000000000000
    | 5 => 1702433464538049 / 8000000000000
    | 6 => 1254004784680137 / 8000000000000
    | 7 => 2148758572376301 / 8000000000000
    | 8 => 1582765839023559 / 8000000000000
    | 9 => 2428369823564457 / 8000000000000
    | 10 => 1402019971326753 / 8000000000000
    | 11 => 2487909042219477 / 8000000000000
    | 12 => 2324527350314313 / 8000000000000
    | 13 => 1658892401573529 / 8000000000000
    | 14 => 1881007177019391 / 8000000000000
    | 15 => 1568187679342479 / 8000000000000
    | 16 => 1385541373060059 / 8000000000000
    | 17 => 401583893981841 / 1600000000000
    | 18 => 1110802184956227 / 8000000000000
    | 19 => 941639313984747 / 8000000000000
    | 20 => 589234160976441 / 8000000000000
    | 21 => 316892091477447 / 8000000000000
    | 22 => 860423672653341 / 8000000000000
    | 23 => 1174834965125757 / 8000000000000
    | 24 => 496765839023559 / 8000000000000
    | 25 => 2019325556016039 / 8000000000000
    | _ => 1348815887666601 / 8000000000000
  state := fun i =>
    match i.val with
    | 0 => (orderedInterval (-67948145854 / 1000000000000) (-67948145847 / 1000000000000), orderedInterval (-8274232142 / 1000000000000) (-8274232135 / 1000000000000))
    | 1 => (orderedInterval (19432621272 / 1000000000000) (19432621273 / 1000000000000), orderedInterval (77292090200 / 1000000000000) (77292090201 / 1000000000000))
    | 2 => (orderedInterval (-49155722642 / 1000000000000) (-49155636003 / 1000000000000), orderedInterval (39155681434 / 1000000000000) (39155768073 / 1000000000000))
    | 3 => (orderedInterval (-146748063724 / 1000000000000) (-146748063618 / 1000000000000), orderedInterval (19266028932 / 1000000000000) (19266029038 / 1000000000000))
    | 4 => (orderedInterval (-52313507807 / 1000000000000) (-52313507806 / 1000000000000), orderedInterval (-73056058503 / 1000000000000) (-73056058502 / 1000000000000))
    | 5 => (orderedInterval (-2149329686 / 1000000000000) (-2149329681 / 1000000000000), orderedInterval (54658175022 / 1000000000000) (54658175027 / 1000000000000))
    | 6 => (orderedInterval (28038720626 / 1000000000000) (28038720627 / 1000000000000), orderedInterval (57139904531 / 1000000000000) (57139904532 / 1000000000000))
    | 7 => (orderedInterval (-34829516073 / 1000000000000) (-34829477548 / 1000000000000), orderedInterval (34080876292 / 1000000000000) (34080914817 / 1000000000000))
    | 8 => (orderedInterval (-36982242681 / 1000000000000) (-36982242680 / 1000000000000), orderedInterval (-42919021732 / 1000000000000) (-42919021731 / 1000000000000))
    | 9 => (orderedInterval (17971759832 / 1000000000000) (17971760328 / 1000000000000), orderedInterval (-42151952785 / 1000000000000) (-42151952289 / 1000000000000))
    | 10 => (orderedInterval (6496166131 / 1000000000000) (6496166132 / 1000000000000), orderedInterval (59901415581 / 1000000000000) (59901415583 / 1000000000000))
    | 11 => (orderedInterval (-31037080602 / 1000000000000) (-31037080601 / 1000000000000), orderedInterval (-32870967256 / 1000000000000) (-32870967255 / 1000000000000))
    | 12 => (orderedInterval (34134655546 / 1000000000000) (34134697273 / 1000000000000), orderedInterval (-32086693944 / 1000000000000) (-32086652217 / 1000000000000))
    | 13 => (orderedInterval (39794994475 / 1000000000000) (39794994476 / 1000000000000), orderedInterval (38458599595 / 1000000000000) (38458599596 / 1000000000000))
    | 14 => (orderedInterval (-14944848267 / 1000000000000) (-14944848266 / 1000000000000), orderedInterval (-49810233996 / 1000000000000) (-49810233995 / 1000000000000))
    | 15 => (orderedInterval (51097819391 / 1000000000000) (51097834308 / 1000000000000), orderedInterval (-25362801104 / 1000000000000) (-25362786187 / 1000000000000))
    | 16 => (orderedInterval (-56279716750 / 1000000000000) (-56279716749 / 1000000000000), orderedInterval (-22384624211 / 1000000000000) (-22384624210 / 1000000000000))
    | 17 => (orderedInterval (21789161988 / 1000000000000) (21789161989 / 1000000000000), orderedInterval (45362221635 / 1000000000000) (45362221636 / 1000000000000))
    | 18 => (orderedInterval (66780007609 / 1000000000000) (66780007613 / 1000000000000), orderedInterval (10955045708 / 1000000000000) (10955045711 / 1000000000000))
    | 19 => (orderedInterval (-57206911230 / 1000000000000) (-57206833793 / 1000000000000), orderedInterval (46459536596 / 1000000000000) (46459614033 / 1000000000000))
    | 20 => (orderedInterval (-76172528287 / 1000000000000) (-76172493376 / 1000000000000), orderedInterval (53818385348 / 1000000000000) (53818420259 / 1000000000000))
    | 21 => (orderedInterval (54791552036 / 1000000000000) (54791555803 / 1000000000000), orderedInterval (-115016792607 / 1000000000000) (-115016788840 / 1000000000000))
    | 22 => (orderedInterval (76847758671 / 1000000000000) (76847758688 / 1000000000000), orderedInterval (3315177051 / 1000000000000) (3315177068 / 1000000000000))
    | 23 => (orderedInterval (1049266148 / 1000000000000) (1049266154 / 1000000000000), orderedInterval (-65836432953 / 1000000000000) (-65836432947 / 1000000000000))
    | 24 => (orderedInterval (4783596986 / 1000000000000) (4783596990 / 1000000000000), orderedInterval (101103360313 / 1000000000000) (101103360317 / 1000000000000))
    | 25 => (orderedInterval (47941931002 / 1000000000000) (47941935072 / 1000000000000), orderedInterval (-15050752455 / 1000000000000) (-15050748385 / 1000000000000))
    | _ => (orderedInterval (-15759110723 / 1000000000000) (-15759110538 / 1000000000000), orderedInterval (59439817580 / 1000000000000) (59439817765 / 1000000000000))
  chunkTarget := fun r b =>
    match r.val with
    | 0 =>
      match b.val with
      | 0 => orderedInterval (-29635705872 / 1000000000000) (-29635700775 / 1000000000000)
      | 1 => orderedInterval (-165149997 / 1000000000000) (-165149978 / 1000000000000)
      | 2 => orderedInterval (180492596 / 1000000000000) (180493793 / 1000000000000)
      | 3 => orderedInterval (-7124156271 / 1000000000000) (-7124156128 / 1000000000000)
      | 4 => orderedInterval (3222521637 / 1000000000000) (3222522407 / 1000000000000)
      | 5 => orderedInterval (4368650535 / 1000000000000) (4368650721 / 1000000000000)
      | 6 => orderedInterval (-9919531537 / 1000000000000) (-9919525982 / 1000000000000)
      | 7 => orderedInterval (-2835581566 / 1000000000000) (-2835581478 / 1000000000000)
      | _ => orderedInterval (-916894456 / 1000000000000) (-916894052 / 1000000000000)
    | 1 =>
      match b.val with
      | 0 => orderedInterval (-12551912 / 1000000000000) (-12545843 / 1000000000000)
      | 1 => orderedInterval (-7676137964 / 1000000000000) (-7676137943 / 1000000000000)
      | 2 => orderedInterval (-3591629662 / 1000000000000) (-3591627297 / 1000000000000)
      | 3 => orderedInterval (11772718503 / 1000000000000) (11772718812 / 1000000000000)
      | 4 => orderedInterval (7231713992 / 1000000000000) (7231715631 / 1000000000000)
      | 5 => orderedInterval (3358825654 / 1000000000000) (3358825922 / 1000000000000)
      | 6 => orderedInterval (-3121066987 / 1000000000000) (-3121062537 / 1000000000000)
      | 7 => orderedInterval (6018493531 / 1000000000000) (6018493567 / 1000000000000)
      | _ => orderedInterval (-11294556157 / 1000000000000) (-11294555444 / 1000000000000)
    | 2 =>
      match b.val with
      | 0 => orderedInterval (30925728180 / 1000000000000) (30925735452 / 1000000000000)
      | 1 => orderedInterval (244197114 / 1000000000000) (244197142 / 1000000000000)
      | 2 => orderedInterval (-2280709129 / 1000000000000) (-2280704435 / 1000000000000)
      | 3 => orderedInterval (38233461223 / 1000000000000) (38233461906 / 1000000000000)
      | 4 => orderedInterval (-6237497137 / 1000000000000) (-6237493629 / 1000000000000)
      | 5 => orderedInterval (-8404631831 / 1000000000000) (-8404631441 / 1000000000000)
      | 6 => orderedInterval (9489613644 / 1000000000000) (9489617338 / 1000000000000)
      | 7 => orderedInterval (1230304506 / 1000000000000) (1230304528 / 1000000000000)
      | _ => orderedInterval (9008856859 / 1000000000000) (9008858142 / 1000000000000)
    | 3 =>
      match b.val with
      | 0 => orderedInterval (-1117796588 / 1000000000000) (-1117787929 / 1000000000000)
      | 1 => orderedInterval (15481844722 / 1000000000000) (15481844762 / 1000000000000)
      | 2 => orderedInterval (11370134272 / 1000000000000) (11370143554 / 1000000000000)
      | 3 => orderedInterval (-37388801724 / 1000000000000) (-37388800209 / 1000000000000)
      | 4 => orderedInterval (-19906219001 / 1000000000000) (-19906211514 / 1000000000000)
      | 5 => orderedInterval (-9057194700 / 1000000000000) (-9057194135 / 1000000000000)
      | 6 => orderedInterval (3238652443 / 1000000000000) (3238655539 / 1000000000000)
      | 7 => orderedInterval (-6411974313 / 1000000000000) (-6411974294 / 1000000000000)
      | _ => orderedInterval (13365237169 / 1000000000000) (13365239496 / 1000000000000)
    | _ =>
      match b.val with
      | 0 => orderedInterval (-32664695499 / 1000000000000) (-32664685124 / 1000000000000)
      | 1 => orderedInterval (485813658 / 1000000000000) (485813721 / 1000000000000)
      | 2 => orderedInterval (12264304408 / 1000000000000) (12264322834 / 1000000000000)
      | 3 => orderedInterval (-199468886145 / 1000000000000) (-199468882759 / 1000000000000)
      | 4 => orderedInterval (8526734916 / 1000000000000) (8526750966 / 1000000000000)
      | 5 => orderedInterval (17751098501 / 1000000000000) (17751099327 / 1000000000000)
      | 6 => orderedInterval (-10118943847 / 1000000000000) (-10118941197 / 1000000000000)
      | 7 => orderedInterval (-709904281 / 1000000000000) (-709904263 / 1000000000000)
      | _ => orderedInterval (-39809706373 / 1000000000000) (-39809702104 / 1000000000000)
  coefficientTarget := fun i =>
    match i.val with
    | 0 => orderedInterval (-42825354931 / 1000000000000) (-42825341472 / 1000000000000)
    | 1 => orderedInterval (2685808998 / 1000000000000) (2685824868 / 1000000000000)
    | 2 => orderedInterval (72209323429 / 1000000000000) (72209345003 / 1000000000000)
    | 3 => orderedInterval (-30426117720 / 1000000000000) (-30426084730 / 1000000000000)
    | _ => orderedInterval (-243744184662 / 1000000000000) (-243744128599 / 1000000000000)

theorem compactCertificate261_stateChecks0 :
    compactCertificate261.stateChecks 0 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 43 12 (543 / 4)) (orderedInterval (-67948145854 / 1000000000000) (-67948145847 / 1000000000000), orderedInterval (-8274232142 / 1000000000000) (-8274232135 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 32 12 (799942684710243 / 8000000000000)) (orderedInterval (19432621272 / 1000000000000) (19432621273 / 1000000000000), orderedInterval (77292090200 / 1000000000000) (77292090201 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 51 12 (258685028375619 / 1600000000000)) (orderedInterval (-49155722642 / 1000000000000) (-49155636003 / 1000000000000), orderedInterval (39155681434 / 1000000000000) (39155768073 / 1000000000000))) = true
  norm_num [besselStateAtRationalPoint, besselIntervalStepZero,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, besselZeroTransition,
    besselInitial, besselGridStateAt, besselGridStateBlock00, besselGridStateBlock01,
    besselGridStateBlock02, besselGridStateBlock03, besselGridStateBlock04,
    besselGridStateBlock05, besselGridStateBlock06, besselGridStateBlock07,
    besselGridStateBlock08, besselGridStateBlock09, besselGridStateBlock10,
    besselGridStateBlock11, besselGridStateBlock12, besselGridStateBlock13,
    besselGridStateBlock14, besselGridState009, besselGridState013, besselGridState020, besselGridState023, besselGridState025, besselGridState032, besselGridState034, besselGridState037, besselGridState043, besselGridState044, besselGridState047, besselGridState050, besselGridState051, besselGridState054, besselGridState055, besselGridState056, besselGridState062, besselGridState063, besselGridState066, besselGridState068, besselGridState075, besselGridState080, besselGridState086, besselGridState093, besselGridState097, besselGridState099, besselStateSubset, linearInterval, widenInterval,
    rationalErrorInterval, rationalIntervalSubset, orderedInterval, Finset.sum_range_succ,
    IntervalRat.add, IntervalRat.mul, IntervalRat.scale, IntervalRat.singleton]

theorem compactCertificate261_stateChecks1 :
    compactCertificate261.stateChecks 3 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 9 12 (233421280313001 / 8000000000000)) (orderedInterval (-146748063724 / 1000000000000) (-146748063618 / 1000000000000), orderedInterval (19266028932 / 1000000000000) (19266029038 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 25 12 (627002392339797 / 8000000000000)) (orderedInterval (-52313507807 / 1000000000000) (-52313507806 / 1000000000000), orderedInterval (-73056058503 / 1000000000000) (-73056058502 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 68 12 (1702433464538049 / 8000000000000)) (orderedInterval (-2149329686 / 1000000000000) (-2149329681 / 1000000000000), orderedInterval (54658175022 / 1000000000000) (54658175027 / 1000000000000))) = true
  norm_num [besselStateAtRationalPoint, besselIntervalStepZero,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, besselZeroTransition,
    besselInitial, besselGridStateAt, besselGridStateBlock00, besselGridStateBlock01,
    besselGridStateBlock02, besselGridStateBlock03, besselGridStateBlock04,
    besselGridStateBlock05, besselGridStateBlock06, besselGridStateBlock07,
    besselGridStateBlock08, besselGridStateBlock09, besselGridStateBlock10,
    besselGridStateBlock11, besselGridStateBlock12, besselGridStateBlock13,
    besselGridStateBlock14, besselGridState009, besselGridState013, besselGridState020, besselGridState023, besselGridState025, besselGridState032, besselGridState034, besselGridState037, besselGridState043, besselGridState044, besselGridState047, besselGridState050, besselGridState051, besselGridState054, besselGridState055, besselGridState056, besselGridState062, besselGridState063, besselGridState066, besselGridState068, besselGridState075, besselGridState080, besselGridState086, besselGridState093, besselGridState097, besselGridState099, besselStateSubset, linearInterval, widenInterval,
    rationalErrorInterval, rationalIntervalSubset, orderedInterval, Finset.sum_range_succ,
    IntervalRat.add, IntervalRat.mul, IntervalRat.scale, IntervalRat.singleton]

theorem compactCertificate261_stateChecks2 :
    compactCertificate261.stateChecks 6 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 50 12 (1254004784680137 / 8000000000000)) (orderedInterval (28038720626 / 1000000000000) (28038720627 / 1000000000000), orderedInterval (57139904531 / 1000000000000) (57139904532 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 86 12 (2148758572376301 / 8000000000000)) (orderedInterval (-34829516073 / 1000000000000) (-34829477548 / 1000000000000), orderedInterval (34080876292 / 1000000000000) (34080914817 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 63 12 (1582765839023559 / 8000000000000)) (orderedInterval (-36982242681 / 1000000000000) (-36982242680 / 1000000000000), orderedInterval (-42919021732 / 1000000000000) (-42919021731 / 1000000000000))) = true
  norm_num [besselStateAtRationalPoint, besselIntervalStepZero,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, besselZeroTransition,
    besselInitial, besselGridStateAt, besselGridStateBlock00, besselGridStateBlock01,
    besselGridStateBlock02, besselGridStateBlock03, besselGridStateBlock04,
    besselGridStateBlock05, besselGridStateBlock06, besselGridStateBlock07,
    besselGridStateBlock08, besselGridStateBlock09, besselGridStateBlock10,
    besselGridStateBlock11, besselGridStateBlock12, besselGridStateBlock13,
    besselGridStateBlock14, besselGridState009, besselGridState013, besselGridState020, besselGridState023, besselGridState025, besselGridState032, besselGridState034, besselGridState037, besselGridState043, besselGridState044, besselGridState047, besselGridState050, besselGridState051, besselGridState054, besselGridState055, besselGridState056, besselGridState062, besselGridState063, besselGridState066, besselGridState068, besselGridState075, besselGridState080, besselGridState086, besselGridState093, besselGridState097, besselGridState099, besselStateSubset, linearInterval, widenInterval,
    rationalErrorInterval, rationalIntervalSubset, orderedInterval, Finset.sum_range_succ,
    IntervalRat.add, IntervalRat.mul, IntervalRat.scale, IntervalRat.singleton]

theorem compactCertificate261_stateChecks3 :
    compactCertificate261.stateChecks 9 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 97 12 (2428369823564457 / 8000000000000)) (orderedInterval (17971759832 / 1000000000000) (17971760328 / 1000000000000), orderedInterval (-42151952785 / 1000000000000) (-42151952289 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 56 12 (1402019971326753 / 8000000000000)) (orderedInterval (6496166131 / 1000000000000) (6496166132 / 1000000000000), orderedInterval (59901415581 / 1000000000000) (59901415583 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 99 12 (2487909042219477 / 8000000000000)) (orderedInterval (-31037080602 / 1000000000000) (-31037080601 / 1000000000000), orderedInterval (-32870967256 / 1000000000000) (-32870967255 / 1000000000000))) = true
  norm_num [besselStateAtRationalPoint, besselIntervalStepZero,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, besselZeroTransition,
    besselInitial, besselGridStateAt, besselGridStateBlock00, besselGridStateBlock01,
    besselGridStateBlock02, besselGridStateBlock03, besselGridStateBlock04,
    besselGridStateBlock05, besselGridStateBlock06, besselGridStateBlock07,
    besselGridStateBlock08, besselGridStateBlock09, besselGridStateBlock10,
    besselGridStateBlock11, besselGridStateBlock12, besselGridStateBlock13,
    besselGridStateBlock14, besselGridState009, besselGridState013, besselGridState020, besselGridState023, besselGridState025, besselGridState032, besselGridState034, besselGridState037, besselGridState043, besselGridState044, besselGridState047, besselGridState050, besselGridState051, besselGridState054, besselGridState055, besselGridState056, besselGridState062, besselGridState063, besselGridState066, besselGridState068, besselGridState075, besselGridState080, besselGridState086, besselGridState093, besselGridState097, besselGridState099, besselStateSubset, linearInterval, widenInterval,
    rationalErrorInterval, rationalIntervalSubset, orderedInterval, Finset.sum_range_succ,
    IntervalRat.add, IntervalRat.mul, IntervalRat.scale, IntervalRat.singleton]

theorem compactCertificate261_stateChecks4 :
    compactCertificate261.stateChecks 12 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 93 12 (2324527350314313 / 8000000000000)) (orderedInterval (34134655546 / 1000000000000) (34134697273 / 1000000000000), orderedInterval (-32086693944 / 1000000000000) (-32086652217 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 66 12 (1658892401573529 / 8000000000000)) (orderedInterval (39794994475 / 1000000000000) (39794994476 / 1000000000000), orderedInterval (38458599595 / 1000000000000) (38458599596 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 75 12 (1881007177019391 / 8000000000000)) (orderedInterval (-14944848267 / 1000000000000) (-14944848266 / 1000000000000), orderedInterval (-49810233996 / 1000000000000) (-49810233995 / 1000000000000))) = true
  norm_num [besselStateAtRationalPoint, besselIntervalStepZero,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, besselZeroTransition,
    besselInitial, besselGridStateAt, besselGridStateBlock00, besselGridStateBlock01,
    besselGridStateBlock02, besselGridStateBlock03, besselGridStateBlock04,
    besselGridStateBlock05, besselGridStateBlock06, besselGridStateBlock07,
    besselGridStateBlock08, besselGridStateBlock09, besselGridStateBlock10,
    besselGridStateBlock11, besselGridStateBlock12, besselGridStateBlock13,
    besselGridStateBlock14, besselGridState009, besselGridState013, besselGridState020, besselGridState023, besselGridState025, besselGridState032, besselGridState034, besselGridState037, besselGridState043, besselGridState044, besselGridState047, besselGridState050, besselGridState051, besselGridState054, besselGridState055, besselGridState056, besselGridState062, besselGridState063, besselGridState066, besselGridState068, besselGridState075, besselGridState080, besselGridState086, besselGridState093, besselGridState097, besselGridState099, besselStateSubset, linearInterval, widenInterval,
    rationalErrorInterval, rationalIntervalSubset, orderedInterval, Finset.sum_range_succ,
    IntervalRat.add, IntervalRat.mul, IntervalRat.scale, IntervalRat.singleton]

theorem compactCertificate261_stateChecks5 :
    compactCertificate261.stateChecks 15 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 62 12 (1568187679342479 / 8000000000000)) (orderedInterval (51097819391 / 1000000000000) (51097834308 / 1000000000000), orderedInterval (-25362801104 / 1000000000000) (-25362786187 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 55 12 (1385541373060059 / 8000000000000)) (orderedInterval (-56279716750 / 1000000000000) (-56279716749 / 1000000000000), orderedInterval (-22384624211 / 1000000000000) (-22384624210 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 80 12 (401583893981841 / 1600000000000)) (orderedInterval (21789161988 / 1000000000000) (21789161989 / 1000000000000), orderedInterval (45362221635 / 1000000000000) (45362221636 / 1000000000000))) = true
  norm_num [besselStateAtRationalPoint, besselIntervalStepZero,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, besselZeroTransition,
    besselInitial, besselGridStateAt, besselGridStateBlock00, besselGridStateBlock01,
    besselGridStateBlock02, besselGridStateBlock03, besselGridStateBlock04,
    besselGridStateBlock05, besselGridStateBlock06, besselGridStateBlock07,
    besselGridStateBlock08, besselGridStateBlock09, besselGridStateBlock10,
    besselGridStateBlock11, besselGridStateBlock12, besselGridStateBlock13,
    besselGridStateBlock14, besselGridState009, besselGridState013, besselGridState020, besselGridState023, besselGridState025, besselGridState032, besselGridState034, besselGridState037, besselGridState043, besselGridState044, besselGridState047, besselGridState050, besselGridState051, besselGridState054, besselGridState055, besselGridState056, besselGridState062, besselGridState063, besselGridState066, besselGridState068, besselGridState075, besselGridState080, besselGridState086, besselGridState093, besselGridState097, besselGridState099, besselStateSubset, linearInterval, widenInterval,
    rationalErrorInterval, rationalIntervalSubset, orderedInterval, Finset.sum_range_succ,
    IntervalRat.add, IntervalRat.mul, IntervalRat.scale, IntervalRat.singleton]

theorem compactCertificate261_stateChecks6 :
    compactCertificate261.stateChecks 18 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 44 12 (1110802184956227 / 8000000000000)) (orderedInterval (66780007609 / 1000000000000) (66780007613 / 1000000000000), orderedInterval (10955045708 / 1000000000000) (10955045711 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 37 12 (941639313984747 / 8000000000000)) (orderedInterval (-57206911230 / 1000000000000) (-57206833793 / 1000000000000), orderedInterval (46459536596 / 1000000000000) (46459614033 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 23 12 (589234160976441 / 8000000000000)) (orderedInterval (-76172528287 / 1000000000000) (-76172493376 / 1000000000000), orderedInterval (53818385348 / 1000000000000) (53818420259 / 1000000000000))) = true
  norm_num [besselStateAtRationalPoint, besselIntervalStepZero,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, besselZeroTransition,
    besselInitial, besselGridStateAt, besselGridStateBlock00, besselGridStateBlock01,
    besselGridStateBlock02, besselGridStateBlock03, besselGridStateBlock04,
    besselGridStateBlock05, besselGridStateBlock06, besselGridStateBlock07,
    besselGridStateBlock08, besselGridStateBlock09, besselGridStateBlock10,
    besselGridStateBlock11, besselGridStateBlock12, besselGridStateBlock13,
    besselGridStateBlock14, besselGridState009, besselGridState013, besselGridState020, besselGridState023, besselGridState025, besselGridState032, besselGridState034, besselGridState037, besselGridState043, besselGridState044, besselGridState047, besselGridState050, besselGridState051, besselGridState054, besselGridState055, besselGridState056, besselGridState062, besselGridState063, besselGridState066, besselGridState068, besselGridState075, besselGridState080, besselGridState086, besselGridState093, besselGridState097, besselGridState099, besselStateSubset, linearInterval, widenInterval,
    rationalErrorInterval, rationalIntervalSubset, orderedInterval, Finset.sum_range_succ,
    IntervalRat.add, IntervalRat.mul, IntervalRat.scale, IntervalRat.singleton]

theorem compactCertificate261_stateChecks7 :
    compactCertificate261.stateChecks 21 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 13 12 (316892091477447 / 8000000000000)) (orderedInterval (54791552036 / 1000000000000) (54791555803 / 1000000000000), orderedInterval (-115016792607 / 1000000000000) (-115016788840 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 34 12 (860423672653341 / 8000000000000)) (orderedInterval (76847758671 / 1000000000000) (76847758688 / 1000000000000), orderedInterval (3315177051 / 1000000000000) (3315177068 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 47 12 (1174834965125757 / 8000000000000)) (orderedInterval (1049266148 / 1000000000000) (1049266154 / 1000000000000), orderedInterval (-65836432953 / 1000000000000) (-65836432947 / 1000000000000))) = true
  norm_num [besselStateAtRationalPoint, besselIntervalStepZero,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, besselZeroTransition,
    besselInitial, besselGridStateAt, besselGridStateBlock00, besselGridStateBlock01,
    besselGridStateBlock02, besselGridStateBlock03, besselGridStateBlock04,
    besselGridStateBlock05, besselGridStateBlock06, besselGridStateBlock07,
    besselGridStateBlock08, besselGridStateBlock09, besselGridStateBlock10,
    besselGridStateBlock11, besselGridStateBlock12, besselGridStateBlock13,
    besselGridStateBlock14, besselGridState009, besselGridState013, besselGridState020, besselGridState023, besselGridState025, besselGridState032, besselGridState034, besselGridState037, besselGridState043, besselGridState044, besselGridState047, besselGridState050, besselGridState051, besselGridState054, besselGridState055, besselGridState056, besselGridState062, besselGridState063, besselGridState066, besselGridState068, besselGridState075, besselGridState080, besselGridState086, besselGridState093, besselGridState097, besselGridState099, besselStateSubset, linearInterval, widenInterval,
    rationalErrorInterval, rationalIntervalSubset, orderedInterval, Finset.sum_range_succ,
    IntervalRat.add, IntervalRat.mul, IntervalRat.scale, IntervalRat.singleton]

theorem compactCertificate261_stateChecks8 :
    compactCertificate261.stateChecks 24 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 20 12 (496765839023559 / 8000000000000)) (orderedInterval (4783596986 / 1000000000000) (4783596990 / 1000000000000), orderedInterval (101103360313 / 1000000000000) (101103360317 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 80 12 (2019325556016039 / 8000000000000)) (orderedInterval (47941931002 / 1000000000000) (47941935072 / 1000000000000), orderedInterval (-15050752455 / 1000000000000) (-15050748385 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 54 12 (1348815887666601 / 8000000000000)) (orderedInterval (-15759110723 / 1000000000000) (-15759110538 / 1000000000000), orderedInterval (59439817580 / 1000000000000) (59439817765 / 1000000000000))) = true
  norm_num [besselStateAtRationalPoint, besselIntervalStepZero,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, besselZeroTransition,
    besselInitial, besselGridStateAt, besselGridStateBlock00, besselGridStateBlock01,
    besselGridStateBlock02, besselGridStateBlock03, besselGridStateBlock04,
    besselGridStateBlock05, besselGridStateBlock06, besselGridStateBlock07,
    besselGridStateBlock08, besselGridStateBlock09, besselGridStateBlock10,
    besselGridStateBlock11, besselGridStateBlock12, besselGridStateBlock13,
    besselGridStateBlock14, besselGridState009, besselGridState013, besselGridState020, besselGridState023, besselGridState025, besselGridState032, besselGridState034, besselGridState037, besselGridState043, besselGridState044, besselGridState047, besselGridState050, besselGridState051, besselGridState054, besselGridState055, besselGridState056, besselGridState062, besselGridState063, besselGridState066, besselGridState068, besselGridState075, besselGridState080, besselGridState086, besselGridState093, besselGridState097, besselGridState099, besselStateSubset, linearInterval, widenInterval,
    rationalErrorInterval, rationalIntervalSubset, orderedInterval, Finset.sum_range_succ,
    IntervalRat.add, IntervalRat.mul, IntervalRat.scale, IntervalRat.singleton]

theorem compactCertificate261_states : ∀ j,
    BesselStateValid (compactCertificate261.point j) (compactCertificate261.state j) :=
  compactCertificate261.statesValid_of_checks3 compactCertificate261_stateChecks0
    compactCertificate261_stateChecks1 compactCertificate261_stateChecks2
    compactCertificate261_stateChecks3 compactCertificate261_stateChecks4
    compactCertificate261_stateChecks5 compactCertificate261_stateChecks6
    compactCertificate261_stateChecks7 compactCertificate261_stateChecks8

theorem compactCertificate261_chunkChecks0_0 :
    compactCertificate261.chunkChecks (0 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 0) <| besselDerivativeNearFromState (543 / 4) 0 (IntervalRat.scale (543 / 4) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-67948145854 / 1000000000000) (-67948145847 / 1000000000000), orderedInterval (-8274232142 / 1000000000000) (-8274232135 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 0) <| besselDerivativeNearFromState (799942684710243 / 8000000000000) 0 (IntervalRat.scale (543 / 4) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (19432621272 / 1000000000000) (19432621273 / 1000000000000), orderedInterval (77292090200 / 1000000000000) (77292090201 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 0) <| besselDerivativeNearFromState (258685028375619 / 1600000000000) 0 (IntervalRat.scale (543 / 4) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-49155722642 / 1000000000000) (-49155636003 / 1000000000000), orderedInterval (39155681434 / 1000000000000) (39155768073 / 1000000000000)))) (orderedInterval (-29635705872 / 1000000000000) (-29635700775 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 0) <| besselDerivativeNearFromState (233421280313001 / 8000000000000) 0 (IntervalRat.scale (543 / 4) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-146748063724 / 1000000000000) (-146748063618 / 1000000000000), orderedInterval (19266028932 / 1000000000000) (19266029038 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 0) <| besselDerivativeNearFromState (627002392339797 / 8000000000000) 0 (IntervalRat.scale (543 / 4) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-52313507807 / 1000000000000) (-52313507806 / 1000000000000), orderedInterval (-73056058503 / 1000000000000) (-73056058502 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 0) <| besselDerivativeNearFromState (1702433464538049 / 8000000000000) 0 (IntervalRat.scale (543 / 4) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-2149329686 / 1000000000000) (-2149329681 / 1000000000000), orderedInterval (54658175022 / 1000000000000) (54658175027 / 1000000000000)))) (orderedInterval (-165149997 / 1000000000000) (-165149978 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 0) <| besselDerivativeNearFromState (1254004784680137 / 8000000000000) 0 (IntervalRat.scale (543 / 4) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (28038720626 / 1000000000000) (28038720627 / 1000000000000), orderedInterval (57139904531 / 1000000000000) (57139904532 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 0) <| besselDerivativeNearFromState (2148758572376301 / 8000000000000) 0 (IntervalRat.scale (543 / 4) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-34829516073 / 1000000000000) (-34829477548 / 1000000000000), orderedInterval (34080876292 / 1000000000000) (34080914817 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 0) <| besselDerivativeNearFromState (1582765839023559 / 8000000000000) 0 (IntervalRat.scale (543 / 4) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-36982242681 / 1000000000000) (-36982242680 / 1000000000000), orderedInterval (-42919021732 / 1000000000000) (-42919021731 / 1000000000000)))) (orderedInterval (180492596 / 1000000000000) (180493793 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate261_chunkChecks0_1 :
    compactCertificate261.chunkChecks (0 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 0) <| besselDerivativeNearFromState (2428369823564457 / 8000000000000) 0 (IntervalRat.scale (543 / 4) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (17971759832 / 1000000000000) (17971760328 / 1000000000000), orderedInterval (-42151952785 / 1000000000000) (-42151952289 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 0) <| besselDerivativeNearFromState (1402019971326753 / 8000000000000) 0 (IntervalRat.scale (543 / 4) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (6496166131 / 1000000000000) (6496166132 / 1000000000000), orderedInterval (59901415581 / 1000000000000) (59901415583 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 0) <| besselDerivativeNearFromState (2487909042219477 / 8000000000000) 0 (IntervalRat.scale (543 / 4) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-31037080602 / 1000000000000) (-31037080601 / 1000000000000), orderedInterval (-32870967256 / 1000000000000) (-32870967255 / 1000000000000)))) (orderedInterval (-7124156271 / 1000000000000) (-7124156128 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 0) <| besselDerivativeNearFromState (2324527350314313 / 8000000000000) 0 (IntervalRat.scale (543 / 4) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (34134655546 / 1000000000000) (34134697273 / 1000000000000), orderedInterval (-32086693944 / 1000000000000) (-32086652217 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 0) <| besselDerivativeNearFromState (1658892401573529 / 8000000000000) 0 (IntervalRat.scale (543 / 4) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (39794994475 / 1000000000000) (39794994476 / 1000000000000), orderedInterval (38458599595 / 1000000000000) (38458599596 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 0) <| besselDerivativeNearFromState (1881007177019391 / 8000000000000) 0 (IntervalRat.scale (543 / 4) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-14944848267 / 1000000000000) (-14944848266 / 1000000000000), orderedInterval (-49810233996 / 1000000000000) (-49810233995 / 1000000000000)))) (orderedInterval (3222521637 / 1000000000000) (3222522407 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 0) <| besselDerivativeNearFromState (1568187679342479 / 8000000000000) 0 (IntervalRat.scale (543 / 4) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (51097819391 / 1000000000000) (51097834308 / 1000000000000), orderedInterval (-25362801104 / 1000000000000) (-25362786187 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 0) <| besselDerivativeNearFromState (1385541373060059 / 8000000000000) 0 (IntervalRat.scale (543 / 4) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-56279716750 / 1000000000000) (-56279716749 / 1000000000000), orderedInterval (-22384624211 / 1000000000000) (-22384624210 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 0) <| besselDerivativeNearFromState (401583893981841 / 1600000000000) 0 (IntervalRat.scale (543 / 4) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (21789161988 / 1000000000000) (21789161989 / 1000000000000), orderedInterval (45362221635 / 1000000000000) (45362221636 / 1000000000000)))) (orderedInterval (4368650535 / 1000000000000) (4368650721 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate261_chunkChecks0_2 :
    compactCertificate261.chunkChecks (0 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 0) <| besselDerivativeNearFromState (1110802184956227 / 8000000000000) 0 (IntervalRat.scale (543 / 4) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (66780007609 / 1000000000000) (66780007613 / 1000000000000), orderedInterval (10955045708 / 1000000000000) (10955045711 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 0) <| besselDerivativeNearFromState (941639313984747 / 8000000000000) 0 (IntervalRat.scale (543 / 4) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-57206911230 / 1000000000000) (-57206833793 / 1000000000000), orderedInterval (46459536596 / 1000000000000) (46459614033 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 0) <| besselDerivativeNearFromState (589234160976441 / 8000000000000) 0 (IntervalRat.scale (543 / 4) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-76172528287 / 1000000000000) (-76172493376 / 1000000000000), orderedInterval (53818385348 / 1000000000000) (53818420259 / 1000000000000)))) (orderedInterval (-9919531537 / 1000000000000) (-9919525982 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 0) <| besselDerivativeNearFromState (316892091477447 / 8000000000000) 0 (IntervalRat.scale (543 / 4) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (54791552036 / 1000000000000) (54791555803 / 1000000000000), orderedInterval (-115016792607 / 1000000000000) (-115016788840 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 0) <| besselDerivativeNearFromState (860423672653341 / 8000000000000) 0 (IntervalRat.scale (543 / 4) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (76847758671 / 1000000000000) (76847758688 / 1000000000000), orderedInterval (3315177051 / 1000000000000) (3315177068 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 0) <| besselDerivativeNearFromState (1174834965125757 / 8000000000000) 0 (IntervalRat.scale (543 / 4) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (1049266148 / 1000000000000) (1049266154 / 1000000000000), orderedInterval (-65836432953 / 1000000000000) (-65836432947 / 1000000000000)))) (orderedInterval (-2835581566 / 1000000000000) (-2835581478 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 0) <| besselDerivativeNearFromState (496765839023559 / 8000000000000) 0 (IntervalRat.scale (543 / 4) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (4783596986 / 1000000000000) (4783596990 / 1000000000000), orderedInterval (101103360313 / 1000000000000) (101103360317 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 0) <| besselDerivativeNearFromState (2019325556016039 / 8000000000000) 0 (IntervalRat.scale (543 / 4) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (47941931002 / 1000000000000) (47941935072 / 1000000000000), orderedInterval (-15050752455 / 1000000000000) (-15050748385 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 0) <| besselDerivativeNearFromState (1348815887666601 / 8000000000000) 0 (IntervalRat.scale (543 / 4) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-15759110723 / 1000000000000) (-15759110538 / 1000000000000), orderedInterval (59439817580 / 1000000000000) (59439817765 / 1000000000000)))) (orderedInterval (-916894456 / 1000000000000) (-916894052 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate261_chunkChecks0 :
    compactCertificate261.chunkChecks (0 : Fin 5) 0 9 = true :=
  compactCertificate261.chunkChecks_nine_of_three (0 : Fin 5) compactCertificate261_chunkChecks0_0
    compactCertificate261_chunkChecks0_1 compactCertificate261_chunkChecks0_2

theorem compactCertificate261_chunkChecks1_0 :
    compactCertificate261.chunkChecks (1 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 1) <| besselDerivativeNearFromState (543 / 4) 1 (IntervalRat.scale (543 / 4) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-67948145854 / 1000000000000) (-67948145847 / 1000000000000), orderedInterval (-8274232142 / 1000000000000) (-8274232135 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 1) <| besselDerivativeNearFromState (799942684710243 / 8000000000000) 1 (IntervalRat.scale (543 / 4) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (19432621272 / 1000000000000) (19432621273 / 1000000000000), orderedInterval (77292090200 / 1000000000000) (77292090201 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 1) <| besselDerivativeNearFromState (258685028375619 / 1600000000000) 1 (IntervalRat.scale (543 / 4) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-49155722642 / 1000000000000) (-49155636003 / 1000000000000), orderedInterval (39155681434 / 1000000000000) (39155768073 / 1000000000000)))) (orderedInterval (-12551912 / 1000000000000) (-12545843 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 1) <| besselDerivativeNearFromState (233421280313001 / 8000000000000) 1 (IntervalRat.scale (543 / 4) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-146748063724 / 1000000000000) (-146748063618 / 1000000000000), orderedInterval (19266028932 / 1000000000000) (19266029038 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 1) <| besselDerivativeNearFromState (627002392339797 / 8000000000000) 1 (IntervalRat.scale (543 / 4) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-52313507807 / 1000000000000) (-52313507806 / 1000000000000), orderedInterval (-73056058503 / 1000000000000) (-73056058502 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 1) <| besselDerivativeNearFromState (1702433464538049 / 8000000000000) 1 (IntervalRat.scale (543 / 4) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-2149329686 / 1000000000000) (-2149329681 / 1000000000000), orderedInterval (54658175022 / 1000000000000) (54658175027 / 1000000000000)))) (orderedInterval (-7676137964 / 1000000000000) (-7676137943 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 1) <| besselDerivativeNearFromState (1254004784680137 / 8000000000000) 1 (IntervalRat.scale (543 / 4) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (28038720626 / 1000000000000) (28038720627 / 1000000000000), orderedInterval (57139904531 / 1000000000000) (57139904532 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 1) <| besselDerivativeNearFromState (2148758572376301 / 8000000000000) 1 (IntervalRat.scale (543 / 4) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-34829516073 / 1000000000000) (-34829477548 / 1000000000000), orderedInterval (34080876292 / 1000000000000) (34080914817 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 1) <| besselDerivativeNearFromState (1582765839023559 / 8000000000000) 1 (IntervalRat.scale (543 / 4) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-36982242681 / 1000000000000) (-36982242680 / 1000000000000), orderedInterval (-42919021732 / 1000000000000) (-42919021731 / 1000000000000)))) (orderedInterval (-3591629662 / 1000000000000) (-3591627297 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate261_chunkChecks1_1 :
    compactCertificate261.chunkChecks (1 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 1) <| besselDerivativeNearFromState (2428369823564457 / 8000000000000) 1 (IntervalRat.scale (543 / 4) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (17971759832 / 1000000000000) (17971760328 / 1000000000000), orderedInterval (-42151952785 / 1000000000000) (-42151952289 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 1) <| besselDerivativeNearFromState (1402019971326753 / 8000000000000) 1 (IntervalRat.scale (543 / 4) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (6496166131 / 1000000000000) (6496166132 / 1000000000000), orderedInterval (59901415581 / 1000000000000) (59901415583 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 1) <| besselDerivativeNearFromState (2487909042219477 / 8000000000000) 1 (IntervalRat.scale (543 / 4) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-31037080602 / 1000000000000) (-31037080601 / 1000000000000), orderedInterval (-32870967256 / 1000000000000) (-32870967255 / 1000000000000)))) (orderedInterval (11772718503 / 1000000000000) (11772718812 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 1) <| besselDerivativeNearFromState (2324527350314313 / 8000000000000) 1 (IntervalRat.scale (543 / 4) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (34134655546 / 1000000000000) (34134697273 / 1000000000000), orderedInterval (-32086693944 / 1000000000000) (-32086652217 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 1) <| besselDerivativeNearFromState (1658892401573529 / 8000000000000) 1 (IntervalRat.scale (543 / 4) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (39794994475 / 1000000000000) (39794994476 / 1000000000000), orderedInterval (38458599595 / 1000000000000) (38458599596 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 1) <| besselDerivativeNearFromState (1881007177019391 / 8000000000000) 1 (IntervalRat.scale (543 / 4) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-14944848267 / 1000000000000) (-14944848266 / 1000000000000), orderedInterval (-49810233996 / 1000000000000) (-49810233995 / 1000000000000)))) (orderedInterval (7231713992 / 1000000000000) (7231715631 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 1) <| besselDerivativeNearFromState (1568187679342479 / 8000000000000) 1 (IntervalRat.scale (543 / 4) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (51097819391 / 1000000000000) (51097834308 / 1000000000000), orderedInterval (-25362801104 / 1000000000000) (-25362786187 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 1) <| besselDerivativeNearFromState (1385541373060059 / 8000000000000) 1 (IntervalRat.scale (543 / 4) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-56279716750 / 1000000000000) (-56279716749 / 1000000000000), orderedInterval (-22384624211 / 1000000000000) (-22384624210 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 1) <| besselDerivativeNearFromState (401583893981841 / 1600000000000) 1 (IntervalRat.scale (543 / 4) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (21789161988 / 1000000000000) (21789161989 / 1000000000000), orderedInterval (45362221635 / 1000000000000) (45362221636 / 1000000000000)))) (orderedInterval (3358825654 / 1000000000000) (3358825922 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate261_chunkChecks1_2 :
    compactCertificate261.chunkChecks (1 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 1) <| besselDerivativeNearFromState (1110802184956227 / 8000000000000) 1 (IntervalRat.scale (543 / 4) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (66780007609 / 1000000000000) (66780007613 / 1000000000000), orderedInterval (10955045708 / 1000000000000) (10955045711 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 1) <| besselDerivativeNearFromState (941639313984747 / 8000000000000) 1 (IntervalRat.scale (543 / 4) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-57206911230 / 1000000000000) (-57206833793 / 1000000000000), orderedInterval (46459536596 / 1000000000000) (46459614033 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 1) <| besselDerivativeNearFromState (589234160976441 / 8000000000000) 1 (IntervalRat.scale (543 / 4) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-76172528287 / 1000000000000) (-76172493376 / 1000000000000), orderedInterval (53818385348 / 1000000000000) (53818420259 / 1000000000000)))) (orderedInterval (-3121066987 / 1000000000000) (-3121062537 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 1) <| besselDerivativeNearFromState (316892091477447 / 8000000000000) 1 (IntervalRat.scale (543 / 4) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (54791552036 / 1000000000000) (54791555803 / 1000000000000), orderedInterval (-115016792607 / 1000000000000) (-115016788840 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 1) <| besselDerivativeNearFromState (860423672653341 / 8000000000000) 1 (IntervalRat.scale (543 / 4) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (76847758671 / 1000000000000) (76847758688 / 1000000000000), orderedInterval (3315177051 / 1000000000000) (3315177068 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 1) <| besselDerivativeNearFromState (1174834965125757 / 8000000000000) 1 (IntervalRat.scale (543 / 4) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (1049266148 / 1000000000000) (1049266154 / 1000000000000), orderedInterval (-65836432953 / 1000000000000) (-65836432947 / 1000000000000)))) (orderedInterval (6018493531 / 1000000000000) (6018493567 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 1) <| besselDerivativeNearFromState (496765839023559 / 8000000000000) 1 (IntervalRat.scale (543 / 4) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (4783596986 / 1000000000000) (4783596990 / 1000000000000), orderedInterval (101103360313 / 1000000000000) (101103360317 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 1) <| besselDerivativeNearFromState (2019325556016039 / 8000000000000) 1 (IntervalRat.scale (543 / 4) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (47941931002 / 1000000000000) (47941935072 / 1000000000000), orderedInterval (-15050752455 / 1000000000000) (-15050748385 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 1) <| besselDerivativeNearFromState (1348815887666601 / 8000000000000) 1 (IntervalRat.scale (543 / 4) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-15759110723 / 1000000000000) (-15759110538 / 1000000000000), orderedInterval (59439817580 / 1000000000000) (59439817765 / 1000000000000)))) (orderedInterval (-11294556157 / 1000000000000) (-11294555444 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate261_chunkChecks1 :
    compactCertificate261.chunkChecks (1 : Fin 5) 0 9 = true :=
  compactCertificate261.chunkChecks_nine_of_three (1 : Fin 5) compactCertificate261_chunkChecks1_0
    compactCertificate261_chunkChecks1_1 compactCertificate261_chunkChecks1_2

theorem compactCertificate261_chunkChecks2_0 :
    compactCertificate261.chunkChecks (2 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 2) <| besselDerivativeNearFromState (543 / 4) 2 (IntervalRat.scale (543 / 4) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-67948145854 / 1000000000000) (-67948145847 / 1000000000000), orderedInterval (-8274232142 / 1000000000000) (-8274232135 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 2) <| besselDerivativeNearFromState (799942684710243 / 8000000000000) 2 (IntervalRat.scale (543 / 4) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (19432621272 / 1000000000000) (19432621273 / 1000000000000), orderedInterval (77292090200 / 1000000000000) (77292090201 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 2) <| besselDerivativeNearFromState (258685028375619 / 1600000000000) 2 (IntervalRat.scale (543 / 4) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-49155722642 / 1000000000000) (-49155636003 / 1000000000000), orderedInterval (39155681434 / 1000000000000) (39155768073 / 1000000000000)))) (orderedInterval (30925728180 / 1000000000000) (30925735452 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 2) <| besselDerivativeNearFromState (233421280313001 / 8000000000000) 2 (IntervalRat.scale (543 / 4) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-146748063724 / 1000000000000) (-146748063618 / 1000000000000), orderedInterval (19266028932 / 1000000000000) (19266029038 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 2) <| besselDerivativeNearFromState (627002392339797 / 8000000000000) 2 (IntervalRat.scale (543 / 4) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-52313507807 / 1000000000000) (-52313507806 / 1000000000000), orderedInterval (-73056058503 / 1000000000000) (-73056058502 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 2) <| besselDerivativeNearFromState (1702433464538049 / 8000000000000) 2 (IntervalRat.scale (543 / 4) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-2149329686 / 1000000000000) (-2149329681 / 1000000000000), orderedInterval (54658175022 / 1000000000000) (54658175027 / 1000000000000)))) (orderedInterval (244197114 / 1000000000000) (244197142 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 2) <| besselDerivativeNearFromState (1254004784680137 / 8000000000000) 2 (IntervalRat.scale (543 / 4) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (28038720626 / 1000000000000) (28038720627 / 1000000000000), orderedInterval (57139904531 / 1000000000000) (57139904532 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 2) <| besselDerivativeNearFromState (2148758572376301 / 8000000000000) 2 (IntervalRat.scale (543 / 4) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-34829516073 / 1000000000000) (-34829477548 / 1000000000000), orderedInterval (34080876292 / 1000000000000) (34080914817 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 2) <| besselDerivativeNearFromState (1582765839023559 / 8000000000000) 2 (IntervalRat.scale (543 / 4) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-36982242681 / 1000000000000) (-36982242680 / 1000000000000), orderedInterval (-42919021732 / 1000000000000) (-42919021731 / 1000000000000)))) (orderedInterval (-2280709129 / 1000000000000) (-2280704435 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate261_chunkChecks2_1 :
    compactCertificate261.chunkChecks (2 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 2) <| besselDerivativeNearFromState (2428369823564457 / 8000000000000) 2 (IntervalRat.scale (543 / 4) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (17971759832 / 1000000000000) (17971760328 / 1000000000000), orderedInterval (-42151952785 / 1000000000000) (-42151952289 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 2) <| besselDerivativeNearFromState (1402019971326753 / 8000000000000) 2 (IntervalRat.scale (543 / 4) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (6496166131 / 1000000000000) (6496166132 / 1000000000000), orderedInterval (59901415581 / 1000000000000) (59901415583 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 2) <| besselDerivativeNearFromState (2487909042219477 / 8000000000000) 2 (IntervalRat.scale (543 / 4) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-31037080602 / 1000000000000) (-31037080601 / 1000000000000), orderedInterval (-32870967256 / 1000000000000) (-32870967255 / 1000000000000)))) (orderedInterval (38233461223 / 1000000000000) (38233461906 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 2) <| besselDerivativeNearFromState (2324527350314313 / 8000000000000) 2 (IntervalRat.scale (543 / 4) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (34134655546 / 1000000000000) (34134697273 / 1000000000000), orderedInterval (-32086693944 / 1000000000000) (-32086652217 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 2) <| besselDerivativeNearFromState (1658892401573529 / 8000000000000) 2 (IntervalRat.scale (543 / 4) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (39794994475 / 1000000000000) (39794994476 / 1000000000000), orderedInterval (38458599595 / 1000000000000) (38458599596 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 2) <| besselDerivativeNearFromState (1881007177019391 / 8000000000000) 2 (IntervalRat.scale (543 / 4) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-14944848267 / 1000000000000) (-14944848266 / 1000000000000), orderedInterval (-49810233996 / 1000000000000) (-49810233995 / 1000000000000)))) (orderedInterval (-6237497137 / 1000000000000) (-6237493629 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 2) <| besselDerivativeNearFromState (1568187679342479 / 8000000000000) 2 (IntervalRat.scale (543 / 4) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (51097819391 / 1000000000000) (51097834308 / 1000000000000), orderedInterval (-25362801104 / 1000000000000) (-25362786187 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 2) <| besselDerivativeNearFromState (1385541373060059 / 8000000000000) 2 (IntervalRat.scale (543 / 4) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-56279716750 / 1000000000000) (-56279716749 / 1000000000000), orderedInterval (-22384624211 / 1000000000000) (-22384624210 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 2) <| besselDerivativeNearFromState (401583893981841 / 1600000000000) 2 (IntervalRat.scale (543 / 4) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (21789161988 / 1000000000000) (21789161989 / 1000000000000), orderedInterval (45362221635 / 1000000000000) (45362221636 / 1000000000000)))) (orderedInterval (-8404631831 / 1000000000000) (-8404631441 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate261_chunkChecks2_2 :
    compactCertificate261.chunkChecks (2 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 2) <| besselDerivativeNearFromState (1110802184956227 / 8000000000000) 2 (IntervalRat.scale (543 / 4) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (66780007609 / 1000000000000) (66780007613 / 1000000000000), orderedInterval (10955045708 / 1000000000000) (10955045711 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 2) <| besselDerivativeNearFromState (941639313984747 / 8000000000000) 2 (IntervalRat.scale (543 / 4) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-57206911230 / 1000000000000) (-57206833793 / 1000000000000), orderedInterval (46459536596 / 1000000000000) (46459614033 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 2) <| besselDerivativeNearFromState (589234160976441 / 8000000000000) 2 (IntervalRat.scale (543 / 4) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-76172528287 / 1000000000000) (-76172493376 / 1000000000000), orderedInterval (53818385348 / 1000000000000) (53818420259 / 1000000000000)))) (orderedInterval (9489613644 / 1000000000000) (9489617338 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 2) <| besselDerivativeNearFromState (316892091477447 / 8000000000000) 2 (IntervalRat.scale (543 / 4) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (54791552036 / 1000000000000) (54791555803 / 1000000000000), orderedInterval (-115016792607 / 1000000000000) (-115016788840 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 2) <| besselDerivativeNearFromState (860423672653341 / 8000000000000) 2 (IntervalRat.scale (543 / 4) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (76847758671 / 1000000000000) (76847758688 / 1000000000000), orderedInterval (3315177051 / 1000000000000) (3315177068 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 2) <| besselDerivativeNearFromState (1174834965125757 / 8000000000000) 2 (IntervalRat.scale (543 / 4) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (1049266148 / 1000000000000) (1049266154 / 1000000000000), orderedInterval (-65836432953 / 1000000000000) (-65836432947 / 1000000000000)))) (orderedInterval (1230304506 / 1000000000000) (1230304528 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 2) <| besselDerivativeNearFromState (496765839023559 / 8000000000000) 2 (IntervalRat.scale (543 / 4) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (4783596986 / 1000000000000) (4783596990 / 1000000000000), orderedInterval (101103360313 / 1000000000000) (101103360317 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 2) <| besselDerivativeNearFromState (2019325556016039 / 8000000000000) 2 (IntervalRat.scale (543 / 4) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (47941931002 / 1000000000000) (47941935072 / 1000000000000), orderedInterval (-15050752455 / 1000000000000) (-15050748385 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 2) <| besselDerivativeNearFromState (1348815887666601 / 8000000000000) 2 (IntervalRat.scale (543 / 4) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-15759110723 / 1000000000000) (-15759110538 / 1000000000000), orderedInterval (59439817580 / 1000000000000) (59439817765 / 1000000000000)))) (orderedInterval (9008856859 / 1000000000000) (9008858142 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate261_chunkChecks2 :
    compactCertificate261.chunkChecks (2 : Fin 5) 0 9 = true :=
  compactCertificate261.chunkChecks_nine_of_three (2 : Fin 5) compactCertificate261_chunkChecks2_0
    compactCertificate261_chunkChecks2_1 compactCertificate261_chunkChecks2_2

theorem compactCertificate261_chunkChecks3_0 :
    compactCertificate261.chunkChecks (3 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 3) <| besselDerivativeNearFromState (543 / 4) 3 (IntervalRat.scale (543 / 4) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-67948145854 / 1000000000000) (-67948145847 / 1000000000000), orderedInterval (-8274232142 / 1000000000000) (-8274232135 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 3) <| besselDerivativeNearFromState (799942684710243 / 8000000000000) 3 (IntervalRat.scale (543 / 4) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (19432621272 / 1000000000000) (19432621273 / 1000000000000), orderedInterval (77292090200 / 1000000000000) (77292090201 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 3) <| besselDerivativeNearFromState (258685028375619 / 1600000000000) 3 (IntervalRat.scale (543 / 4) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-49155722642 / 1000000000000) (-49155636003 / 1000000000000), orderedInterval (39155681434 / 1000000000000) (39155768073 / 1000000000000)))) (orderedInterval (-1117796588 / 1000000000000) (-1117787929 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 3) <| besselDerivativeNearFromState (233421280313001 / 8000000000000) 3 (IntervalRat.scale (543 / 4) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-146748063724 / 1000000000000) (-146748063618 / 1000000000000), orderedInterval (19266028932 / 1000000000000) (19266029038 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 3) <| besselDerivativeNearFromState (627002392339797 / 8000000000000) 3 (IntervalRat.scale (543 / 4) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-52313507807 / 1000000000000) (-52313507806 / 1000000000000), orderedInterval (-73056058503 / 1000000000000) (-73056058502 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 3) <| besselDerivativeNearFromState (1702433464538049 / 8000000000000) 3 (IntervalRat.scale (543 / 4) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-2149329686 / 1000000000000) (-2149329681 / 1000000000000), orderedInterval (54658175022 / 1000000000000) (54658175027 / 1000000000000)))) (orderedInterval (15481844722 / 1000000000000) (15481844762 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 3) <| besselDerivativeNearFromState (1254004784680137 / 8000000000000) 3 (IntervalRat.scale (543 / 4) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (28038720626 / 1000000000000) (28038720627 / 1000000000000), orderedInterval (57139904531 / 1000000000000) (57139904532 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 3) <| besselDerivativeNearFromState (2148758572376301 / 8000000000000) 3 (IntervalRat.scale (543 / 4) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-34829516073 / 1000000000000) (-34829477548 / 1000000000000), orderedInterval (34080876292 / 1000000000000) (34080914817 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 3) <| besselDerivativeNearFromState (1582765839023559 / 8000000000000) 3 (IntervalRat.scale (543 / 4) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-36982242681 / 1000000000000) (-36982242680 / 1000000000000), orderedInterval (-42919021732 / 1000000000000) (-42919021731 / 1000000000000)))) (orderedInterval (11370134272 / 1000000000000) (11370143554 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate261_chunkChecks3_1 :
    compactCertificate261.chunkChecks (3 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 3) <| besselDerivativeNearFromState (2428369823564457 / 8000000000000) 3 (IntervalRat.scale (543 / 4) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (17971759832 / 1000000000000) (17971760328 / 1000000000000), orderedInterval (-42151952785 / 1000000000000) (-42151952289 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 3) <| besselDerivativeNearFromState (1402019971326753 / 8000000000000) 3 (IntervalRat.scale (543 / 4) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (6496166131 / 1000000000000) (6496166132 / 1000000000000), orderedInterval (59901415581 / 1000000000000) (59901415583 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 3) <| besselDerivativeNearFromState (2487909042219477 / 8000000000000) 3 (IntervalRat.scale (543 / 4) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-31037080602 / 1000000000000) (-31037080601 / 1000000000000), orderedInterval (-32870967256 / 1000000000000) (-32870967255 / 1000000000000)))) (orderedInterval (-37388801724 / 1000000000000) (-37388800209 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 3) <| besselDerivativeNearFromState (2324527350314313 / 8000000000000) 3 (IntervalRat.scale (543 / 4) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (34134655546 / 1000000000000) (34134697273 / 1000000000000), orderedInterval (-32086693944 / 1000000000000) (-32086652217 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 3) <| besselDerivativeNearFromState (1658892401573529 / 8000000000000) 3 (IntervalRat.scale (543 / 4) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (39794994475 / 1000000000000) (39794994476 / 1000000000000), orderedInterval (38458599595 / 1000000000000) (38458599596 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 3) <| besselDerivativeNearFromState (1881007177019391 / 8000000000000) 3 (IntervalRat.scale (543 / 4) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-14944848267 / 1000000000000) (-14944848266 / 1000000000000), orderedInterval (-49810233996 / 1000000000000) (-49810233995 / 1000000000000)))) (orderedInterval (-19906219001 / 1000000000000) (-19906211514 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 3) <| besselDerivativeNearFromState (1568187679342479 / 8000000000000) 3 (IntervalRat.scale (543 / 4) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (51097819391 / 1000000000000) (51097834308 / 1000000000000), orderedInterval (-25362801104 / 1000000000000) (-25362786187 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 3) <| besselDerivativeNearFromState (1385541373060059 / 8000000000000) 3 (IntervalRat.scale (543 / 4) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-56279716750 / 1000000000000) (-56279716749 / 1000000000000), orderedInterval (-22384624211 / 1000000000000) (-22384624210 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 3) <| besselDerivativeNearFromState (401583893981841 / 1600000000000) 3 (IntervalRat.scale (543 / 4) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (21789161988 / 1000000000000) (21789161989 / 1000000000000), orderedInterval (45362221635 / 1000000000000) (45362221636 / 1000000000000)))) (orderedInterval (-9057194700 / 1000000000000) (-9057194135 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate261_chunkChecks3_2 :
    compactCertificate261.chunkChecks (3 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 3) <| besselDerivativeNearFromState (1110802184956227 / 8000000000000) 3 (IntervalRat.scale (543 / 4) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (66780007609 / 1000000000000) (66780007613 / 1000000000000), orderedInterval (10955045708 / 1000000000000) (10955045711 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 3) <| besselDerivativeNearFromState (941639313984747 / 8000000000000) 3 (IntervalRat.scale (543 / 4) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-57206911230 / 1000000000000) (-57206833793 / 1000000000000), orderedInterval (46459536596 / 1000000000000) (46459614033 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 3) <| besselDerivativeNearFromState (589234160976441 / 8000000000000) 3 (IntervalRat.scale (543 / 4) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-76172528287 / 1000000000000) (-76172493376 / 1000000000000), orderedInterval (53818385348 / 1000000000000) (53818420259 / 1000000000000)))) (orderedInterval (3238652443 / 1000000000000) (3238655539 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 3) <| besselDerivativeNearFromState (316892091477447 / 8000000000000) 3 (IntervalRat.scale (543 / 4) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (54791552036 / 1000000000000) (54791555803 / 1000000000000), orderedInterval (-115016792607 / 1000000000000) (-115016788840 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 3) <| besselDerivativeNearFromState (860423672653341 / 8000000000000) 3 (IntervalRat.scale (543 / 4) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (76847758671 / 1000000000000) (76847758688 / 1000000000000), orderedInterval (3315177051 / 1000000000000) (3315177068 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 3) <| besselDerivativeNearFromState (1174834965125757 / 8000000000000) 3 (IntervalRat.scale (543 / 4) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (1049266148 / 1000000000000) (1049266154 / 1000000000000), orderedInterval (-65836432953 / 1000000000000) (-65836432947 / 1000000000000)))) (orderedInterval (-6411974313 / 1000000000000) (-6411974294 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 3) <| besselDerivativeNearFromState (496765839023559 / 8000000000000) 3 (IntervalRat.scale (543 / 4) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (4783596986 / 1000000000000) (4783596990 / 1000000000000), orderedInterval (101103360313 / 1000000000000) (101103360317 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 3) <| besselDerivativeNearFromState (2019325556016039 / 8000000000000) 3 (IntervalRat.scale (543 / 4) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (47941931002 / 1000000000000) (47941935072 / 1000000000000), orderedInterval (-15050752455 / 1000000000000) (-15050748385 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 3) <| besselDerivativeNearFromState (1348815887666601 / 8000000000000) 3 (IntervalRat.scale (543 / 4) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-15759110723 / 1000000000000) (-15759110538 / 1000000000000), orderedInterval (59439817580 / 1000000000000) (59439817765 / 1000000000000)))) (orderedInterval (13365237169 / 1000000000000) (13365239496 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate261_chunkChecks3 :
    compactCertificate261.chunkChecks (3 : Fin 5) 0 9 = true :=
  compactCertificate261.chunkChecks_nine_of_three (3 : Fin 5) compactCertificate261_chunkChecks3_0
    compactCertificate261_chunkChecks3_1 compactCertificate261_chunkChecks3_2

theorem compactCertificate261_chunkChecks4_0 :
    compactCertificate261.chunkChecks (4 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 4) <| besselDerivativeNearFromState (543 / 4) 4 (IntervalRat.scale (543 / 4) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-67948145854 / 1000000000000) (-67948145847 / 1000000000000), orderedInterval (-8274232142 / 1000000000000) (-8274232135 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 4) <| besselDerivativeNearFromState (799942684710243 / 8000000000000) 4 (IntervalRat.scale (543 / 4) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (19432621272 / 1000000000000) (19432621273 / 1000000000000), orderedInterval (77292090200 / 1000000000000) (77292090201 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 4) <| besselDerivativeNearFromState (258685028375619 / 1600000000000) 4 (IntervalRat.scale (543 / 4) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-49155722642 / 1000000000000) (-49155636003 / 1000000000000), orderedInterval (39155681434 / 1000000000000) (39155768073 / 1000000000000)))) (orderedInterval (-32664695499 / 1000000000000) (-32664685124 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 4) <| besselDerivativeNearFromState (233421280313001 / 8000000000000) 4 (IntervalRat.scale (543 / 4) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-146748063724 / 1000000000000) (-146748063618 / 1000000000000), orderedInterval (19266028932 / 1000000000000) (19266029038 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 4) <| besselDerivativeNearFromState (627002392339797 / 8000000000000) 4 (IntervalRat.scale (543 / 4) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-52313507807 / 1000000000000) (-52313507806 / 1000000000000), orderedInterval (-73056058503 / 1000000000000) (-73056058502 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 4) <| besselDerivativeNearFromState (1702433464538049 / 8000000000000) 4 (IntervalRat.scale (543 / 4) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-2149329686 / 1000000000000) (-2149329681 / 1000000000000), orderedInterval (54658175022 / 1000000000000) (54658175027 / 1000000000000)))) (orderedInterval (485813658 / 1000000000000) (485813721 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 4) <| besselDerivativeNearFromState (1254004784680137 / 8000000000000) 4 (IntervalRat.scale (543 / 4) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (28038720626 / 1000000000000) (28038720627 / 1000000000000), orderedInterval (57139904531 / 1000000000000) (57139904532 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 4) <| besselDerivativeNearFromState (2148758572376301 / 8000000000000) 4 (IntervalRat.scale (543 / 4) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-34829516073 / 1000000000000) (-34829477548 / 1000000000000), orderedInterval (34080876292 / 1000000000000) (34080914817 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 4) <| besselDerivativeNearFromState (1582765839023559 / 8000000000000) 4 (IntervalRat.scale (543 / 4) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-36982242681 / 1000000000000) (-36982242680 / 1000000000000), orderedInterval (-42919021732 / 1000000000000) (-42919021731 / 1000000000000)))) (orderedInterval (12264304408 / 1000000000000) (12264322834 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate261_chunkChecks4_1 :
    compactCertificate261.chunkChecks (4 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 4) <| besselDerivativeNearFromState (2428369823564457 / 8000000000000) 4 (IntervalRat.scale (543 / 4) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (17971759832 / 1000000000000) (17971760328 / 1000000000000), orderedInterval (-42151952785 / 1000000000000) (-42151952289 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 4) <| besselDerivativeNearFromState (1402019971326753 / 8000000000000) 4 (IntervalRat.scale (543 / 4) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (6496166131 / 1000000000000) (6496166132 / 1000000000000), orderedInterval (59901415581 / 1000000000000) (59901415583 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 4) <| besselDerivativeNearFromState (2487909042219477 / 8000000000000) 4 (IntervalRat.scale (543 / 4) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-31037080602 / 1000000000000) (-31037080601 / 1000000000000), orderedInterval (-32870967256 / 1000000000000) (-32870967255 / 1000000000000)))) (orderedInterval (-199468886145 / 1000000000000) (-199468882759 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 4) <| besselDerivativeNearFromState (2324527350314313 / 8000000000000) 4 (IntervalRat.scale (543 / 4) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (34134655546 / 1000000000000) (34134697273 / 1000000000000), orderedInterval (-32086693944 / 1000000000000) (-32086652217 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 4) <| besselDerivativeNearFromState (1658892401573529 / 8000000000000) 4 (IntervalRat.scale (543 / 4) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (39794994475 / 1000000000000) (39794994476 / 1000000000000), orderedInterval (38458599595 / 1000000000000) (38458599596 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 4) <| besselDerivativeNearFromState (1881007177019391 / 8000000000000) 4 (IntervalRat.scale (543 / 4) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-14944848267 / 1000000000000) (-14944848266 / 1000000000000), orderedInterval (-49810233996 / 1000000000000) (-49810233995 / 1000000000000)))) (orderedInterval (8526734916 / 1000000000000) (8526750966 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 4) <| besselDerivativeNearFromState (1568187679342479 / 8000000000000) 4 (IntervalRat.scale (543 / 4) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (51097819391 / 1000000000000) (51097834308 / 1000000000000), orderedInterval (-25362801104 / 1000000000000) (-25362786187 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 4) <| besselDerivativeNearFromState (1385541373060059 / 8000000000000) 4 (IntervalRat.scale (543 / 4) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-56279716750 / 1000000000000) (-56279716749 / 1000000000000), orderedInterval (-22384624211 / 1000000000000) (-22384624210 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 4) <| besselDerivativeNearFromState (401583893981841 / 1600000000000) 4 (IntervalRat.scale (543 / 4) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (21789161988 / 1000000000000) (21789161989 / 1000000000000), orderedInterval (45362221635 / 1000000000000) (45362221636 / 1000000000000)))) (orderedInterval (17751098501 / 1000000000000) (17751099327 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate261_chunkChecks4_2 :
    compactCertificate261.chunkChecks (4 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 4) <| besselDerivativeNearFromState (1110802184956227 / 8000000000000) 4 (IntervalRat.scale (543 / 4) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (66780007609 / 1000000000000) (66780007613 / 1000000000000), orderedInterval (10955045708 / 1000000000000) (10955045711 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 4) <| besselDerivativeNearFromState (941639313984747 / 8000000000000) 4 (IntervalRat.scale (543 / 4) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-57206911230 / 1000000000000) (-57206833793 / 1000000000000), orderedInterval (46459536596 / 1000000000000) (46459614033 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 4) <| besselDerivativeNearFromState (589234160976441 / 8000000000000) 4 (IntervalRat.scale (543 / 4) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-76172528287 / 1000000000000) (-76172493376 / 1000000000000), orderedInterval (53818385348 / 1000000000000) (53818420259 / 1000000000000)))) (orderedInterval (-10118943847 / 1000000000000) (-10118941197 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 4) <| besselDerivativeNearFromState (316892091477447 / 8000000000000) 4 (IntervalRat.scale (543 / 4) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (54791552036 / 1000000000000) (54791555803 / 1000000000000), orderedInterval (-115016792607 / 1000000000000) (-115016788840 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 4) <| besselDerivativeNearFromState (860423672653341 / 8000000000000) 4 (IntervalRat.scale (543 / 4) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (76847758671 / 1000000000000) (76847758688 / 1000000000000), orderedInterval (3315177051 / 1000000000000) (3315177068 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 4) <| besselDerivativeNearFromState (1174834965125757 / 8000000000000) 4 (IntervalRat.scale (543 / 4) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (1049266148 / 1000000000000) (1049266154 / 1000000000000), orderedInterval (-65836432953 / 1000000000000) (-65836432947 / 1000000000000)))) (orderedInterval (-709904281 / 1000000000000) (-709904263 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 4) <| besselDerivativeNearFromState (496765839023559 / 8000000000000) 4 (IntervalRat.scale (543 / 4) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (4783596986 / 1000000000000) (4783596990 / 1000000000000), orderedInterval (101103360313 / 1000000000000) (101103360317 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 4) <| besselDerivativeNearFromState (2019325556016039 / 8000000000000) 4 (IntervalRat.scale (543 / 4) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (47941931002 / 1000000000000) (47941935072 / 1000000000000), orderedInterval (-15050752455 / 1000000000000) (-15050748385 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 4) <| besselDerivativeNearFromState (1348815887666601 / 8000000000000) 4 (IntervalRat.scale (543 / 4) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-15759110723 / 1000000000000) (-15759110538 / 1000000000000), orderedInterval (59439817580 / 1000000000000) (59439817765 / 1000000000000)))) (orderedInterval (-39809706373 / 1000000000000) (-39809702104 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate261_chunkChecks4 :
    compactCertificate261.chunkChecks (4 : Fin 5) 0 9 = true :=
  compactCertificate261.chunkChecks_nine_of_three (4 : Fin 5) compactCertificate261_chunkChecks4_0
    compactCertificate261_chunkChecks4_1 compactCertificate261_chunkChecks4_2

theorem compactCertificate261_chunks :
    ∀ r : Fin 5, ∀ b, compactCertificate261.chunkCheck r b = true :=
  compactCertificate261.chunkChecks_all (by
    intro r
    fin_cases r
    · exact compactCertificate261_chunkChecks0
    · exact compactCertificate261_chunkChecks1
    · exact compactCertificate261_chunkChecks2
    · exact compactCertificate261_chunkChecks3
    · exact compactCertificate261_chunkChecks4)

theorem compactCertificate261_coefficient0 :
    compactCertificate261.coefficientCheck (0 : Fin 5) = true := by
  norm_num [CompactCertificate.coefficientCheck, intervalFinSumHull,
    compactCertificate261, rationalIntervalSubset, orderedInterval, Fin.sum_univ_succ]

theorem compactCertificate261_coefficient1 :
    compactCertificate261.coefficientCheck (1 : Fin 5) = true := by
  norm_num [CompactCertificate.coefficientCheck, intervalFinSumHull,
    compactCertificate261, rationalIntervalSubset, orderedInterval, Fin.sum_univ_succ]

theorem compactCertificate261_coefficient2 :
    compactCertificate261.coefficientCheck (2 : Fin 5) = true := by
  norm_num [CompactCertificate.coefficientCheck, intervalFinSumHull,
    compactCertificate261, rationalIntervalSubset, orderedInterval, Fin.sum_univ_succ]

theorem compactCertificate261_coefficient3 :
    compactCertificate261.coefficientCheck (3 : Fin 5) = true := by
  norm_num [CompactCertificate.coefficientCheck, intervalFinSumHull,
    compactCertificate261, rationalIntervalSubset, orderedInterval, Fin.sum_univ_succ]

theorem compactCertificate261_coefficient4 :
    compactCertificate261.coefficientCheck (4 : Fin 5) = true := by
  norm_num [CompactCertificate.coefficientCheck, intervalFinSumHull,
    compactCertificate261, rationalIntervalSubset, orderedInterval, Fin.sum_univ_succ]

theorem compactCertificate261_coefficients : ∀ r : Fin 5,
    compactCertificate261.coefficientCheck r = true := by
  intro r
  fin_cases r
  · exact compactCertificate261_coefficient0
  · exact compactCertificate261_coefficient1
  · exact compactCertificate261_coefficient2
  · exact compactCertificate261_coefficient3
  · exact compactCertificate261_coefficient4

theorem compactCertificate261_lower : (1 : ℚ) ≤ compactCertificate261.output.lo := by
  norm_num [CompactCertificate.output, CompactCertificate.interval,
    CompactCertificate.coefficientTargetNat, compactCertificate261, dualConstant,
    intervalTaylorSum, intervalPow, intervalSub, intervalMaxAbs, widenInterval,
    rationalErrorInterval, orderedInterval, IntervalRat.add, IntervalRat.mul, IntervalRat.scale,
    IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4]

theorem compactCertificate261_proves {t : ℝ} (ht : t ∈ compactCertificate261.interval) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t :=
  compactCertificate261.proves compactCertificate261_states compactCertificate261_chunks
    compactCertificate261_coefficients compactCertificate261_lower ht

end Erdos232
