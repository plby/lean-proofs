/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, OpenAI Codex
-/
import ErdosProblems.Erdos232.CompactBase

open LeanCert.Core
namespace Erdos232

def compactCertificate238 : CompactCertificate where
  left := 115
  right := 116
  center := 231 / 2
  grid := fun i =>
    match i.val with
    | 0 => 37
    | 1 => 27
    | 2 => 44
    | 3 => 8
    | 4 => 21
    | 5 => 58
    | 6 => 42
    | 7 => 73
    | 8 => 54
    | 9 => 82
    | 10 => 47
    | 11 => 84
    | 12 => 79
    | 13 => 56
    | 14 => 64
    | 15 => 53
    | 16 => 47
    | 17 => 68
    | 18 => 38
    | 19 => 32
    | 20 => 20
    | 21 => 11
    | 22 => 29
    | 23 => 40
    | 24 => 17
    | 25 => 68
    | _ => 46
  point := fun i =>
    match i.val with
    | 0 => 231 / 2
    | 1 => 340307108965131 / 4000000000000
    | 2 => 110048326988523 / 800000000000
    | 3 => 99300765658017 / 4000000000000
    | 4 => 266735824365549 / 4000000000000
    | 5 => 724239650659833 / 4000000000000
    | 6 => 533471648731329 / 4000000000000
    | 7 => 914112762834117 / 4000000000000
    | 8 => 673331323783503 / 4000000000000
    | 9 => 1033063405604769 / 4000000000000
    | 10 => 596439435315801 / 4000000000000
    | 11 => 1058392244480109 / 4000000000000
    | 12 => 988887325824321 / 4000000000000
    | 13 => 705716657022993 / 4000000000000
    | 14 => 800207473096647 / 4000000000000
    | 15 => 667129565245143 / 4000000000000
    | 16 => 589429202904003 / 4000000000000
    | 17 => 170839557108297 / 800000000000
    | 18 => 472551205754859 / 4000000000000
    | 19 => 400586890479699 / 4000000000000
    | 20 => 250668676216497 / 4000000000000
    | 21 => 134810447755599 / 4000000000000
    | 22 => 366036590023797 / 4000000000000
    | 23 => 499791670246869 / 4000000000000
    | 24 => 211331323783503 / 4000000000000
    | 25 => 859050098415663 / 4000000000000
    | _ => 573805653869217 / 4000000000000
  state := fun i =>
    match i.val with
    | 0 => (orderedInterval (-3368501736 / 1000000000000) (-3368501733 / 1000000000000), orderedInterval (-74151206122 / 1000000000000) (-74151206118 / 1000000000000))
    | 1 => (orderedInterval (-74499778082 / 1000000000000) (-74499778081 / 1000000000000), orderedInterval (-43523591289 / 1000000000000) (-43523591288 / 1000000000000))
    | 2 => (orderedInterval (7793998364 / 1000000000000) (7793998366 / 1000000000000), orderedInterval (67552823109 / 1000000000000) (67552823111 / 1000000000000))
    | 3 => (orderedInterval (72918779631 / 1000000000000) (72918779632 / 1000000000000), orderedInterval (141115226498 / 1000000000000) (141115226499 / 1000000000000))
    | 4 => (orderedInterval (-97418738204 / 1000000000000) (-97418738196 / 1000000000000), orderedInterval (-6762589290 / 1000000000000) (-6762589282 / 1000000000000))
    | 5 => (orderedInterval (-21318229895 / 1000000000000) (-21318229208 / 1000000000000), orderedInterval (55390736683 / 1000000000000) (55390737370 / 1000000000000))
    | 6 => (orderedInterval (55634968091 / 1000000000000) (55635024359 / 1000000000000), orderedInterval (-41173798873 / 1000000000000) (-41173742604 / 1000000000000))
    | 7 => (orderedInterval (1225537892 / 1000000000000) (1225537895 / 1000000000000), orderedInterval (-52768609640 / 1000000000000) (-52768609637 / 1000000000000))
    | 8 => (orderedInterval (-31010104705 / 1000000000000) (-31010100107 / 1000000000000), orderedInterval (53198534016 / 1000000000000) (53198538614 / 1000000000000))
    | 9 => (orderedInterval (49225510137 / 1000000000000) (49225510152 / 1000000000000), orderedInterval (6371785693 / 1000000000000) (6371785708 / 1000000000000))
    | 10 => (orderedInterval (-51265680902 / 1000000000000) (-51265600137 / 1000000000000), orderedInterval (40684777617 / 1000000000000) (40684858382 / 1000000000000))
    | 11 => (orderedInterval (48887645441 / 1000000000000) (48887645475 / 1000000000000), orderedInterval (3905359993 / 1000000000000) (3905360027 / 1000000000000))
    | 12 => (orderedInterval (9039762521 / 1000000000000) (9039762554 / 1000000000000), orderedInterval (-49952067890 / 1000000000000) (-49952067857 / 1000000000000))
    | 13 => (orderedInterval (57627255277 / 1000000000000) (57627255278 / 1000000000000), orderedInterval (16790927784 / 1000000000000) (16790927786 / 1000000000000))
    | 14 => (orderedInterval (-12601625746 / 1000000000000) (-12601625653 / 1000000000000), orderedInterval (55017689768 / 1000000000000) (55017689861 / 1000000000000))
    | 15 => (orderedInterval (-53975347739 / 1000000000000) (-53975347738 / 1000000000000), orderedInterval (-29900141583 / 1000000000000) (-29900141582 / 1000000000000))
    | 16 => (orderedInterval (-30759121781 / 1000000000000) (-30759121780 / 1000000000000), orderedInterval (-57982948107 / 1000000000000) (-57982948106 / 1000000000000))
    | 17 => (orderedInterval (35422304313 / 1000000000000) (35422304314 / 1000000000000), orderedInterval (41466995500 / 1000000000000) (41466995501 / 1000000000000))
    | 18 => (orderedInterval (-32482715667 / 1000000000000) (-32482712837 / 1000000000000), orderedInterval (65968260017 / 1000000000000) (65968262848 / 1000000000000))
    | 19 => (orderedInterval (31041352239 / 1000000000000) (31041352240 / 1000000000000), orderedInterval (73284526179 / 1000000000000) (73284526180 / 1000000000000))
    | 20 => (orderedInterval (58456882610 / 1000000000000) (58456882611 / 1000000000000), orderedInterval (81641133066 / 1000000000000) (81641133067 / 1000000000000))
    | 21 => (orderedInterval (10053195484 / 1000000000000) (10053195517 / 1000000000000), orderedInterval (-137226891353 / 1000000000000) (-137226891320 / 1000000000000))
    | 22 => (orderedInterval (-77339268470 / 1000000000000) (-77339268469 / 1000000000000), orderedInterval (-30809798642 / 1000000000000) (-30809798641 / 1000000000000))
    | 23 => (orderedInterval (4893452548 / 1000000000000) (4893452550 / 1000000000000), orderedInterval (71192605658 / 1000000000000) (71192605661 / 1000000000000))
    | 24 => (orderedInterval (-22752284493 / 1000000000000) (-22752284492 / 1000000000000), orderedInterval (-107174298267 / 1000000000000) (-107174298266 / 1000000000000))
    | 25 => (orderedInterval (51177110890 / 1000000000000) (51177116295 / 1000000000000), orderedInterval (-18698526909 / 1000000000000) (-18698521504 / 1000000000000))
    | _ => (orderedInterval (-18238505079 / 1000000000000) (-18238504801 / 1000000000000), orderedInterval (64135850134 / 1000000000000) (64135850411 / 1000000000000))
  chunkTarget := fun r b =>
    match r.val with
    | 0 =>
      match b.val with
      | 0 => orderedInterval (-1571988864 / 1000000000000) (-1571988854 / 1000000000000)
      | 1 => orderedInterval (-2832540031 / 1000000000000) (-2832539967 / 1000000000000)
      | 2 => orderedInterval (-787253544 / 1000000000000) (-787253425 / 1000000000000)
      | 3 => orderedInterval (-5595477073 / 1000000000000) (-5595471035 / 1000000000000)
      | 4 => orderedInterval (5349974285 / 1000000000000) (5349974301 / 1000000000000)
      | 5 => orderedInterval (2043903726 / 1000000000000) (2043903738 / 1000000000000)
      | 6 => orderedInterval (5339880748 / 1000000000000) (5339881230 / 1000000000000)
      | 7 => orderedInterval (1193923198 / 1000000000000) (1193923214 / 1000000000000)
      | _ => orderedInterval (-881039145 / 1000000000000) (-881038620 / 1000000000000)
    | 1 =>
      match b.val with
      | 0 => orderedInterval (-24968460416 / 1000000000000) (-24968460405 / 1000000000000)
      | 1 => orderedInterval (-6644446509 / 1000000000000) (-6644446416 / 1000000000000)
      | 2 => orderedInterval (5094177305 / 1000000000000) (5094177479 / 1000000000000)
      | 3 => orderedInterval (2631765042 / 1000000000000) (2631772880 / 1000000000000)
      | 4 => orderedInterval (3873395313 / 1000000000000) (3873395339 / 1000000000000)
      | 5 => orderedInterval (5697836768 / 1000000000000) (5697836785 / 1000000000000)
      | 6 => orderedInterval (-12943167547 / 1000000000000) (-12943167057 / 1000000000000)
      | 7 => orderedInterval (-4609252678 / 1000000000000) (-4609252664 / 1000000000000)
      | _ => orderedInterval (-12411089790 / 1000000000000) (-12411088861 / 1000000000000)
    | 2 =>
      match b.val with
      | 0 => orderedInterval (1279227213 / 1000000000000) (1279227226 / 1000000000000)
      | 1 => orderedInterval (-2444525562 / 1000000000000) (-2444525419 / 1000000000000)
      | 2 => orderedInterval (1695786289 / 1000000000000) (1695786548 / 1000000000000)
      | 3 => orderedInterval (13568551476 / 1000000000000) (13568561759 / 1000000000000)
      | 4 => orderedInterval (-12192429245 / 1000000000000) (-12192429203 / 1000000000000)
      | 5 => orderedInterval (-4715254504 / 1000000000000) (-4715254479 / 1000000000000)
      | 6 => orderedInterval (-4560968072 / 1000000000000) (-4560967568 / 1000000000000)
      | 7 => orderedInterval (-606780228 / 1000000000000) (-606780214 / 1000000000000)
      | _ => orderedInterval (9260750005 / 1000000000000) (9260751681 / 1000000000000)
    | 3 =>
      match b.val with
      | 0 => orderedInterval (22843137134 / 1000000000000) (22843137149 / 1000000000000)
      | 1 => orderedInterval (15252648653 / 1000000000000) (15252648876 / 1000000000000)
      | 2 => orderedInterval (-16601700699 / 1000000000000) (-16601700314 / 1000000000000)
      | 3 => orderedInterval (-619828254 / 1000000000000) (-619814759 / 1000000000000)
      | 4 => orderedInterval (-12950102853 / 1000000000000) (-12950102781 / 1000000000000)
      | 5 => orderedInterval (-12520467943 / 1000000000000) (-12520467905 / 1000000000000)
      | 6 => orderedInterval (13605038515 / 1000000000000) (13605039030 / 1000000000000)
      | 7 => orderedInterval (6501894091 / 1000000000000) (6501894105 / 1000000000000)
      | _ => orderedInterval (13250423338 / 1000000000000) (13250426383 / 1000000000000)
    | _ =>
      match b.val with
      | 0 => orderedInterval (-1014708887 / 1000000000000) (-1014708871 / 1000000000000)
      | 1 => orderedInterval (8490860683 / 1000000000000) (8490861033 / 1000000000000)
      | 2 => orderedInterval (-3673097437 / 1000000000000) (-3673096861 / 1000000000000)
      | 3 => orderedInterval (-37790778654 / 1000000000000) (-37790760619 / 1000000000000)
      | 4 => orderedInterval (27040687671 / 1000000000000) (27040687798 / 1000000000000)
      | 5 => orderedInterval (12768822535 / 1000000000000) (12768822594 / 1000000000000)
      | 6 => orderedInterval (4620650515 / 1000000000000) (4620651044 / 1000000000000)
      | 7 => orderedInterval (63752671 / 1000000000000) (63752686 / 1000000000000)
      | _ => orderedInterval (-41890369607 / 1000000000000) (-41890364008 / 1000000000000)
  coefficientTarget := fun i =>
    match i.val with
    | 0 => orderedInterval (2259383300 / 1000000000000) (2259390582 / 1000000000000)
    | 1 => orderedInterval (-44279242512 / 1000000000000) (-44279232920 / 1000000000000)
    | 2 => orderedInterval (1284357372 / 1000000000000) (1284370331 / 1000000000000)
    | 3 => orderedInterval (28761041982 / 1000000000000) (28761059784 / 1000000000000)
    | _ => orderedInterval (-31384180510 / 1000000000000) (-31384155204 / 1000000000000)

theorem compactCertificate238_stateChecks0 :
    compactCertificate238.stateChecks 0 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 37 12 (231 / 2)) (orderedInterval (-3368501736 / 1000000000000) (-3368501733 / 1000000000000), orderedInterval (-74151206122 / 1000000000000) (-74151206118 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 27 12 (340307108965131 / 4000000000000)) (orderedInterval (-74499778082 / 1000000000000) (-74499778081 / 1000000000000), orderedInterval (-43523591289 / 1000000000000) (-43523591288 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 44 12 (110048326988523 / 800000000000)) (orderedInterval (7793998364 / 1000000000000) (7793998366 / 1000000000000), orderedInterval (67552823109 / 1000000000000) (67552823111 / 1000000000000))) = true
  norm_num [besselStateAtRationalPoint, besselIntervalStepZero,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, besselZeroTransition,
    besselInitial, besselGridStateAt, besselGridStateBlock00, besselGridStateBlock01,
    besselGridStateBlock02, besselGridStateBlock03, besselGridStateBlock04,
    besselGridStateBlock05, besselGridStateBlock06, besselGridStateBlock07,
    besselGridStateBlock08, besselGridStateBlock09, besselGridStateBlock10,
    besselGridStateBlock11, besselGridStateBlock12, besselGridStateBlock13,
    besselGridStateBlock14, besselGridState008, besselGridState011, besselGridState017, besselGridState020, besselGridState021, besselGridState027, besselGridState029, besselGridState032, besselGridState037, besselGridState038, besselGridState040, besselGridState042, besselGridState044, besselGridState046, besselGridState047, besselGridState053, besselGridState054, besselGridState056, besselGridState058, besselGridState064, besselGridState068, besselGridState073, besselGridState079, besselGridState082, besselGridState084, besselStateSubset, linearInterval, widenInterval,
    rationalErrorInterval, rationalIntervalSubset, orderedInterval, Finset.sum_range_succ,
    IntervalRat.add, IntervalRat.mul, IntervalRat.scale, IntervalRat.singleton]

theorem compactCertificate238_stateChecks1 :
    compactCertificate238.stateChecks 3 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 8 12 (99300765658017 / 4000000000000)) (orderedInterval (72918779631 / 1000000000000) (72918779632 / 1000000000000), orderedInterval (141115226498 / 1000000000000) (141115226499 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 21 12 (266735824365549 / 4000000000000)) (orderedInterval (-97418738204 / 1000000000000) (-97418738196 / 1000000000000), orderedInterval (-6762589290 / 1000000000000) (-6762589282 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 58 12 (724239650659833 / 4000000000000)) (orderedInterval (-21318229895 / 1000000000000) (-21318229208 / 1000000000000), orderedInterval (55390736683 / 1000000000000) (55390737370 / 1000000000000))) = true
  norm_num [besselStateAtRationalPoint, besselIntervalStepZero,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, besselZeroTransition,
    besselInitial, besselGridStateAt, besselGridStateBlock00, besselGridStateBlock01,
    besselGridStateBlock02, besselGridStateBlock03, besselGridStateBlock04,
    besselGridStateBlock05, besselGridStateBlock06, besselGridStateBlock07,
    besselGridStateBlock08, besselGridStateBlock09, besselGridStateBlock10,
    besselGridStateBlock11, besselGridStateBlock12, besselGridStateBlock13,
    besselGridStateBlock14, besselGridState008, besselGridState011, besselGridState017, besselGridState020, besselGridState021, besselGridState027, besselGridState029, besselGridState032, besselGridState037, besselGridState038, besselGridState040, besselGridState042, besselGridState044, besselGridState046, besselGridState047, besselGridState053, besselGridState054, besselGridState056, besselGridState058, besselGridState064, besselGridState068, besselGridState073, besselGridState079, besselGridState082, besselGridState084, besselStateSubset, linearInterval, widenInterval,
    rationalErrorInterval, rationalIntervalSubset, orderedInterval, Finset.sum_range_succ,
    IntervalRat.add, IntervalRat.mul, IntervalRat.scale, IntervalRat.singleton]

theorem compactCertificate238_stateChecks2 :
    compactCertificate238.stateChecks 6 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 42 12 (533471648731329 / 4000000000000)) (orderedInterval (55634968091 / 1000000000000) (55635024359 / 1000000000000), orderedInterval (-41173798873 / 1000000000000) (-41173742604 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 73 12 (914112762834117 / 4000000000000)) (orderedInterval (1225537892 / 1000000000000) (1225537895 / 1000000000000), orderedInterval (-52768609640 / 1000000000000) (-52768609637 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 54 12 (673331323783503 / 4000000000000)) (orderedInterval (-31010104705 / 1000000000000) (-31010100107 / 1000000000000), orderedInterval (53198534016 / 1000000000000) (53198538614 / 1000000000000))) = true
  norm_num [besselStateAtRationalPoint, besselIntervalStepZero,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, besselZeroTransition,
    besselInitial, besselGridStateAt, besselGridStateBlock00, besselGridStateBlock01,
    besselGridStateBlock02, besselGridStateBlock03, besselGridStateBlock04,
    besselGridStateBlock05, besselGridStateBlock06, besselGridStateBlock07,
    besselGridStateBlock08, besselGridStateBlock09, besselGridStateBlock10,
    besselGridStateBlock11, besselGridStateBlock12, besselGridStateBlock13,
    besselGridStateBlock14, besselGridState008, besselGridState011, besselGridState017, besselGridState020, besselGridState021, besselGridState027, besselGridState029, besselGridState032, besselGridState037, besselGridState038, besselGridState040, besselGridState042, besselGridState044, besselGridState046, besselGridState047, besselGridState053, besselGridState054, besselGridState056, besselGridState058, besselGridState064, besselGridState068, besselGridState073, besselGridState079, besselGridState082, besselGridState084, besselStateSubset, linearInterval, widenInterval,
    rationalErrorInterval, rationalIntervalSubset, orderedInterval, Finset.sum_range_succ,
    IntervalRat.add, IntervalRat.mul, IntervalRat.scale, IntervalRat.singleton]

theorem compactCertificate238_stateChecks3 :
    compactCertificate238.stateChecks 9 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 82 12 (1033063405604769 / 4000000000000)) (orderedInterval (49225510137 / 1000000000000) (49225510152 / 1000000000000), orderedInterval (6371785693 / 1000000000000) (6371785708 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 47 12 (596439435315801 / 4000000000000)) (orderedInterval (-51265680902 / 1000000000000) (-51265600137 / 1000000000000), orderedInterval (40684777617 / 1000000000000) (40684858382 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 84 12 (1058392244480109 / 4000000000000)) (orderedInterval (48887645441 / 1000000000000) (48887645475 / 1000000000000), orderedInterval (3905359993 / 1000000000000) (3905360027 / 1000000000000))) = true
  norm_num [besselStateAtRationalPoint, besselIntervalStepZero,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, besselZeroTransition,
    besselInitial, besselGridStateAt, besselGridStateBlock00, besselGridStateBlock01,
    besselGridStateBlock02, besselGridStateBlock03, besselGridStateBlock04,
    besselGridStateBlock05, besselGridStateBlock06, besselGridStateBlock07,
    besselGridStateBlock08, besselGridStateBlock09, besselGridStateBlock10,
    besselGridStateBlock11, besselGridStateBlock12, besselGridStateBlock13,
    besselGridStateBlock14, besselGridState008, besselGridState011, besselGridState017, besselGridState020, besselGridState021, besselGridState027, besselGridState029, besselGridState032, besselGridState037, besselGridState038, besselGridState040, besselGridState042, besselGridState044, besselGridState046, besselGridState047, besselGridState053, besselGridState054, besselGridState056, besselGridState058, besselGridState064, besselGridState068, besselGridState073, besselGridState079, besselGridState082, besselGridState084, besselStateSubset, linearInterval, widenInterval,
    rationalErrorInterval, rationalIntervalSubset, orderedInterval, Finset.sum_range_succ,
    IntervalRat.add, IntervalRat.mul, IntervalRat.scale, IntervalRat.singleton]

theorem compactCertificate238_stateChecks4 :
    compactCertificate238.stateChecks 12 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 79 12 (988887325824321 / 4000000000000)) (orderedInterval (9039762521 / 1000000000000) (9039762554 / 1000000000000), orderedInterval (-49952067890 / 1000000000000) (-49952067857 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 56 12 (705716657022993 / 4000000000000)) (orderedInterval (57627255277 / 1000000000000) (57627255278 / 1000000000000), orderedInterval (16790927784 / 1000000000000) (16790927786 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 64 12 (800207473096647 / 4000000000000)) (orderedInterval (-12601625746 / 1000000000000) (-12601625653 / 1000000000000), orderedInterval (55017689768 / 1000000000000) (55017689861 / 1000000000000))) = true
  norm_num [besselStateAtRationalPoint, besselIntervalStepZero,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, besselZeroTransition,
    besselInitial, besselGridStateAt, besselGridStateBlock00, besselGridStateBlock01,
    besselGridStateBlock02, besselGridStateBlock03, besselGridStateBlock04,
    besselGridStateBlock05, besselGridStateBlock06, besselGridStateBlock07,
    besselGridStateBlock08, besselGridStateBlock09, besselGridStateBlock10,
    besselGridStateBlock11, besselGridStateBlock12, besselGridStateBlock13,
    besselGridStateBlock14, besselGridState008, besselGridState011, besselGridState017, besselGridState020, besselGridState021, besselGridState027, besselGridState029, besselGridState032, besselGridState037, besselGridState038, besselGridState040, besselGridState042, besselGridState044, besselGridState046, besselGridState047, besselGridState053, besselGridState054, besselGridState056, besselGridState058, besselGridState064, besselGridState068, besselGridState073, besselGridState079, besselGridState082, besselGridState084, besselStateSubset, linearInterval, widenInterval,
    rationalErrorInterval, rationalIntervalSubset, orderedInterval, Finset.sum_range_succ,
    IntervalRat.add, IntervalRat.mul, IntervalRat.scale, IntervalRat.singleton]

theorem compactCertificate238_stateChecks5 :
    compactCertificate238.stateChecks 15 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 53 12 (667129565245143 / 4000000000000)) (orderedInterval (-53975347739 / 1000000000000) (-53975347738 / 1000000000000), orderedInterval (-29900141583 / 1000000000000) (-29900141582 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 47 12 (589429202904003 / 4000000000000)) (orderedInterval (-30759121781 / 1000000000000) (-30759121780 / 1000000000000), orderedInterval (-57982948107 / 1000000000000) (-57982948106 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 68 12 (170839557108297 / 800000000000)) (orderedInterval (35422304313 / 1000000000000) (35422304314 / 1000000000000), orderedInterval (41466995500 / 1000000000000) (41466995501 / 1000000000000))) = true
  norm_num [besselStateAtRationalPoint, besselIntervalStepZero,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, besselZeroTransition,
    besselInitial, besselGridStateAt, besselGridStateBlock00, besselGridStateBlock01,
    besselGridStateBlock02, besselGridStateBlock03, besselGridStateBlock04,
    besselGridStateBlock05, besselGridStateBlock06, besselGridStateBlock07,
    besselGridStateBlock08, besselGridStateBlock09, besselGridStateBlock10,
    besselGridStateBlock11, besselGridStateBlock12, besselGridStateBlock13,
    besselGridStateBlock14, besselGridState008, besselGridState011, besselGridState017, besselGridState020, besselGridState021, besselGridState027, besselGridState029, besselGridState032, besselGridState037, besselGridState038, besselGridState040, besselGridState042, besselGridState044, besselGridState046, besselGridState047, besselGridState053, besselGridState054, besselGridState056, besselGridState058, besselGridState064, besselGridState068, besselGridState073, besselGridState079, besselGridState082, besselGridState084, besselStateSubset, linearInterval, widenInterval,
    rationalErrorInterval, rationalIntervalSubset, orderedInterval, Finset.sum_range_succ,
    IntervalRat.add, IntervalRat.mul, IntervalRat.scale, IntervalRat.singleton]

theorem compactCertificate238_stateChecks6 :
    compactCertificate238.stateChecks 18 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 38 12 (472551205754859 / 4000000000000)) (orderedInterval (-32482715667 / 1000000000000) (-32482712837 / 1000000000000), orderedInterval (65968260017 / 1000000000000) (65968262848 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 32 12 (400586890479699 / 4000000000000)) (orderedInterval (31041352239 / 1000000000000) (31041352240 / 1000000000000), orderedInterval (73284526179 / 1000000000000) (73284526180 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 20 12 (250668676216497 / 4000000000000)) (orderedInterval (58456882610 / 1000000000000) (58456882611 / 1000000000000), orderedInterval (81641133066 / 1000000000000) (81641133067 / 1000000000000))) = true
  norm_num [besselStateAtRationalPoint, besselIntervalStepZero,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, besselZeroTransition,
    besselInitial, besselGridStateAt, besselGridStateBlock00, besselGridStateBlock01,
    besselGridStateBlock02, besselGridStateBlock03, besselGridStateBlock04,
    besselGridStateBlock05, besselGridStateBlock06, besselGridStateBlock07,
    besselGridStateBlock08, besselGridStateBlock09, besselGridStateBlock10,
    besselGridStateBlock11, besselGridStateBlock12, besselGridStateBlock13,
    besselGridStateBlock14, besselGridState008, besselGridState011, besselGridState017, besselGridState020, besselGridState021, besselGridState027, besselGridState029, besselGridState032, besselGridState037, besselGridState038, besselGridState040, besselGridState042, besselGridState044, besselGridState046, besselGridState047, besselGridState053, besselGridState054, besselGridState056, besselGridState058, besselGridState064, besselGridState068, besselGridState073, besselGridState079, besselGridState082, besselGridState084, besselStateSubset, linearInterval, widenInterval,
    rationalErrorInterval, rationalIntervalSubset, orderedInterval, Finset.sum_range_succ,
    IntervalRat.add, IntervalRat.mul, IntervalRat.scale, IntervalRat.singleton]

theorem compactCertificate238_stateChecks7 :
    compactCertificate238.stateChecks 21 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 11 12 (134810447755599 / 4000000000000)) (orderedInterval (10053195484 / 1000000000000) (10053195517 / 1000000000000), orderedInterval (-137226891353 / 1000000000000) (-137226891320 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 29 12 (366036590023797 / 4000000000000)) (orderedInterval (-77339268470 / 1000000000000) (-77339268469 / 1000000000000), orderedInterval (-30809798642 / 1000000000000) (-30809798641 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 40 12 (499791670246869 / 4000000000000)) (orderedInterval (4893452548 / 1000000000000) (4893452550 / 1000000000000), orderedInterval (71192605658 / 1000000000000) (71192605661 / 1000000000000))) = true
  norm_num [besselStateAtRationalPoint, besselIntervalStepZero,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, besselZeroTransition,
    besselInitial, besselGridStateAt, besselGridStateBlock00, besselGridStateBlock01,
    besselGridStateBlock02, besselGridStateBlock03, besselGridStateBlock04,
    besselGridStateBlock05, besselGridStateBlock06, besselGridStateBlock07,
    besselGridStateBlock08, besselGridStateBlock09, besselGridStateBlock10,
    besselGridStateBlock11, besselGridStateBlock12, besselGridStateBlock13,
    besselGridStateBlock14, besselGridState008, besselGridState011, besselGridState017, besselGridState020, besselGridState021, besselGridState027, besselGridState029, besselGridState032, besselGridState037, besselGridState038, besselGridState040, besselGridState042, besselGridState044, besselGridState046, besselGridState047, besselGridState053, besselGridState054, besselGridState056, besselGridState058, besselGridState064, besselGridState068, besselGridState073, besselGridState079, besselGridState082, besselGridState084, besselStateSubset, linearInterval, widenInterval,
    rationalErrorInterval, rationalIntervalSubset, orderedInterval, Finset.sum_range_succ,
    IntervalRat.add, IntervalRat.mul, IntervalRat.scale, IntervalRat.singleton]

theorem compactCertificate238_stateChecks8 :
    compactCertificate238.stateChecks 24 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 17 12 (211331323783503 / 4000000000000)) (orderedInterval (-22752284493 / 1000000000000) (-22752284492 / 1000000000000), orderedInterval (-107174298267 / 1000000000000) (-107174298266 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 68 12 (859050098415663 / 4000000000000)) (orderedInterval (51177110890 / 1000000000000) (51177116295 / 1000000000000), orderedInterval (-18698526909 / 1000000000000) (-18698521504 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 46 12 (573805653869217 / 4000000000000)) (orderedInterval (-18238505079 / 1000000000000) (-18238504801 / 1000000000000), orderedInterval (64135850134 / 1000000000000) (64135850411 / 1000000000000))) = true
  norm_num [besselStateAtRationalPoint, besselIntervalStepZero,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, besselZeroTransition,
    besselInitial, besselGridStateAt, besselGridStateBlock00, besselGridStateBlock01,
    besselGridStateBlock02, besselGridStateBlock03, besselGridStateBlock04,
    besselGridStateBlock05, besselGridStateBlock06, besselGridStateBlock07,
    besselGridStateBlock08, besselGridStateBlock09, besselGridStateBlock10,
    besselGridStateBlock11, besselGridStateBlock12, besselGridStateBlock13,
    besselGridStateBlock14, besselGridState008, besselGridState011, besselGridState017, besselGridState020, besselGridState021, besselGridState027, besselGridState029, besselGridState032, besselGridState037, besselGridState038, besselGridState040, besselGridState042, besselGridState044, besselGridState046, besselGridState047, besselGridState053, besselGridState054, besselGridState056, besselGridState058, besselGridState064, besselGridState068, besselGridState073, besselGridState079, besselGridState082, besselGridState084, besselStateSubset, linearInterval, widenInterval,
    rationalErrorInterval, rationalIntervalSubset, orderedInterval, Finset.sum_range_succ,
    IntervalRat.add, IntervalRat.mul, IntervalRat.scale, IntervalRat.singleton]

theorem compactCertificate238_states : ∀ j,
    BesselStateValid (compactCertificate238.point j) (compactCertificate238.state j) :=
  compactCertificate238.statesValid_of_checks3 compactCertificate238_stateChecks0
    compactCertificate238_stateChecks1 compactCertificate238_stateChecks2
    compactCertificate238_stateChecks3 compactCertificate238_stateChecks4
    compactCertificate238_stateChecks5 compactCertificate238_stateChecks6
    compactCertificate238_stateChecks7 compactCertificate238_stateChecks8

theorem compactCertificate238_chunkChecks0_0 :
    compactCertificate238.chunkChecks (0 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 0) <| besselDerivativeNearFromState (231 / 2) 0 (IntervalRat.scale (231 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-3368501736 / 1000000000000) (-3368501733 / 1000000000000), orderedInterval (-74151206122 / 1000000000000) (-74151206118 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 0) <| besselDerivativeNearFromState (340307108965131 / 4000000000000) 0 (IntervalRat.scale (231 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-74499778082 / 1000000000000) (-74499778081 / 1000000000000), orderedInterval (-43523591289 / 1000000000000) (-43523591288 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 0) <| besselDerivativeNearFromState (110048326988523 / 800000000000) 0 (IntervalRat.scale (231 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (7793998364 / 1000000000000) (7793998366 / 1000000000000), orderedInterval (67552823109 / 1000000000000) (67552823111 / 1000000000000)))) (orderedInterval (-1571988864 / 1000000000000) (-1571988854 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 0) <| besselDerivativeNearFromState (99300765658017 / 4000000000000) 0 (IntervalRat.scale (231 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (72918779631 / 1000000000000) (72918779632 / 1000000000000), orderedInterval (141115226498 / 1000000000000) (141115226499 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 0) <| besselDerivativeNearFromState (266735824365549 / 4000000000000) 0 (IntervalRat.scale (231 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-97418738204 / 1000000000000) (-97418738196 / 1000000000000), orderedInterval (-6762589290 / 1000000000000) (-6762589282 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 0) <| besselDerivativeNearFromState (724239650659833 / 4000000000000) 0 (IntervalRat.scale (231 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-21318229895 / 1000000000000) (-21318229208 / 1000000000000), orderedInterval (55390736683 / 1000000000000) (55390737370 / 1000000000000)))) (orderedInterval (-2832540031 / 1000000000000) (-2832539967 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 0) <| besselDerivativeNearFromState (533471648731329 / 4000000000000) 0 (IntervalRat.scale (231 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (55634968091 / 1000000000000) (55635024359 / 1000000000000), orderedInterval (-41173798873 / 1000000000000) (-41173742604 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 0) <| besselDerivativeNearFromState (914112762834117 / 4000000000000) 0 (IntervalRat.scale (231 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (1225537892 / 1000000000000) (1225537895 / 1000000000000), orderedInterval (-52768609640 / 1000000000000) (-52768609637 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 0) <| besselDerivativeNearFromState (673331323783503 / 4000000000000) 0 (IntervalRat.scale (231 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-31010104705 / 1000000000000) (-31010100107 / 1000000000000), orderedInterval (53198534016 / 1000000000000) (53198538614 / 1000000000000)))) (orderedInterval (-787253544 / 1000000000000) (-787253425 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate238_chunkChecks0_1 :
    compactCertificate238.chunkChecks (0 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 0) <| besselDerivativeNearFromState (1033063405604769 / 4000000000000) 0 (IntervalRat.scale (231 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (49225510137 / 1000000000000) (49225510152 / 1000000000000), orderedInterval (6371785693 / 1000000000000) (6371785708 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 0) <| besselDerivativeNearFromState (596439435315801 / 4000000000000) 0 (IntervalRat.scale (231 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-51265680902 / 1000000000000) (-51265600137 / 1000000000000), orderedInterval (40684777617 / 1000000000000) (40684858382 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 0) <| besselDerivativeNearFromState (1058392244480109 / 4000000000000) 0 (IntervalRat.scale (231 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (48887645441 / 1000000000000) (48887645475 / 1000000000000), orderedInterval (3905359993 / 1000000000000) (3905360027 / 1000000000000)))) (orderedInterval (-5595477073 / 1000000000000) (-5595471035 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 0) <| besselDerivativeNearFromState (988887325824321 / 4000000000000) 0 (IntervalRat.scale (231 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (9039762521 / 1000000000000) (9039762554 / 1000000000000), orderedInterval (-49952067890 / 1000000000000) (-49952067857 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 0) <| besselDerivativeNearFromState (705716657022993 / 4000000000000) 0 (IntervalRat.scale (231 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (57627255277 / 1000000000000) (57627255278 / 1000000000000), orderedInterval (16790927784 / 1000000000000) (16790927786 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 0) <| besselDerivativeNearFromState (800207473096647 / 4000000000000) 0 (IntervalRat.scale (231 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-12601625746 / 1000000000000) (-12601625653 / 1000000000000), orderedInterval (55017689768 / 1000000000000) (55017689861 / 1000000000000)))) (orderedInterval (5349974285 / 1000000000000) (5349974301 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 0) <| besselDerivativeNearFromState (667129565245143 / 4000000000000) 0 (IntervalRat.scale (231 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-53975347739 / 1000000000000) (-53975347738 / 1000000000000), orderedInterval (-29900141583 / 1000000000000) (-29900141582 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 0) <| besselDerivativeNearFromState (589429202904003 / 4000000000000) 0 (IntervalRat.scale (231 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-30759121781 / 1000000000000) (-30759121780 / 1000000000000), orderedInterval (-57982948107 / 1000000000000) (-57982948106 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 0) <| besselDerivativeNearFromState (170839557108297 / 800000000000) 0 (IntervalRat.scale (231 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (35422304313 / 1000000000000) (35422304314 / 1000000000000), orderedInterval (41466995500 / 1000000000000) (41466995501 / 1000000000000)))) (orderedInterval (2043903726 / 1000000000000) (2043903738 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate238_chunkChecks0_2 :
    compactCertificate238.chunkChecks (0 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 0) <| besselDerivativeNearFromState (472551205754859 / 4000000000000) 0 (IntervalRat.scale (231 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-32482715667 / 1000000000000) (-32482712837 / 1000000000000), orderedInterval (65968260017 / 1000000000000) (65968262848 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 0) <| besselDerivativeNearFromState (400586890479699 / 4000000000000) 0 (IntervalRat.scale (231 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (31041352239 / 1000000000000) (31041352240 / 1000000000000), orderedInterval (73284526179 / 1000000000000) (73284526180 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 0) <| besselDerivativeNearFromState (250668676216497 / 4000000000000) 0 (IntervalRat.scale (231 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (58456882610 / 1000000000000) (58456882611 / 1000000000000), orderedInterval (81641133066 / 1000000000000) (81641133067 / 1000000000000)))) (orderedInterval (5339880748 / 1000000000000) (5339881230 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 0) <| besselDerivativeNearFromState (134810447755599 / 4000000000000) 0 (IntervalRat.scale (231 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (10053195484 / 1000000000000) (10053195517 / 1000000000000), orderedInterval (-137226891353 / 1000000000000) (-137226891320 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 0) <| besselDerivativeNearFromState (366036590023797 / 4000000000000) 0 (IntervalRat.scale (231 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-77339268470 / 1000000000000) (-77339268469 / 1000000000000), orderedInterval (-30809798642 / 1000000000000) (-30809798641 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 0) <| besselDerivativeNearFromState (499791670246869 / 4000000000000) 0 (IntervalRat.scale (231 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (4893452548 / 1000000000000) (4893452550 / 1000000000000), orderedInterval (71192605658 / 1000000000000) (71192605661 / 1000000000000)))) (orderedInterval (1193923198 / 1000000000000) (1193923214 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 0) <| besselDerivativeNearFromState (211331323783503 / 4000000000000) 0 (IntervalRat.scale (231 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-22752284493 / 1000000000000) (-22752284492 / 1000000000000), orderedInterval (-107174298267 / 1000000000000) (-107174298266 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 0) <| besselDerivativeNearFromState (859050098415663 / 4000000000000) 0 (IntervalRat.scale (231 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (51177110890 / 1000000000000) (51177116295 / 1000000000000), orderedInterval (-18698526909 / 1000000000000) (-18698521504 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 0) <| besselDerivativeNearFromState (573805653869217 / 4000000000000) 0 (IntervalRat.scale (231 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-18238505079 / 1000000000000) (-18238504801 / 1000000000000), orderedInterval (64135850134 / 1000000000000) (64135850411 / 1000000000000)))) (orderedInterval (-881039145 / 1000000000000) (-881038620 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate238_chunkChecks0 :
    compactCertificate238.chunkChecks (0 : Fin 5) 0 9 = true :=
  compactCertificate238.chunkChecks_nine_of_three (0 : Fin 5) compactCertificate238_chunkChecks0_0
    compactCertificate238_chunkChecks0_1 compactCertificate238_chunkChecks0_2

theorem compactCertificate238_chunkChecks1_0 :
    compactCertificate238.chunkChecks (1 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 1) <| besselDerivativeNearFromState (231 / 2) 1 (IntervalRat.scale (231 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-3368501736 / 1000000000000) (-3368501733 / 1000000000000), orderedInterval (-74151206122 / 1000000000000) (-74151206118 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 1) <| besselDerivativeNearFromState (340307108965131 / 4000000000000) 1 (IntervalRat.scale (231 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-74499778082 / 1000000000000) (-74499778081 / 1000000000000), orderedInterval (-43523591289 / 1000000000000) (-43523591288 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 1) <| besselDerivativeNearFromState (110048326988523 / 800000000000) 1 (IntervalRat.scale (231 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (7793998364 / 1000000000000) (7793998366 / 1000000000000), orderedInterval (67552823109 / 1000000000000) (67552823111 / 1000000000000)))) (orderedInterval (-24968460416 / 1000000000000) (-24968460405 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 1) <| besselDerivativeNearFromState (99300765658017 / 4000000000000) 1 (IntervalRat.scale (231 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (72918779631 / 1000000000000) (72918779632 / 1000000000000), orderedInterval (141115226498 / 1000000000000) (141115226499 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 1) <| besselDerivativeNearFromState (266735824365549 / 4000000000000) 1 (IntervalRat.scale (231 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-97418738204 / 1000000000000) (-97418738196 / 1000000000000), orderedInterval (-6762589290 / 1000000000000) (-6762589282 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 1) <| besselDerivativeNearFromState (724239650659833 / 4000000000000) 1 (IntervalRat.scale (231 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-21318229895 / 1000000000000) (-21318229208 / 1000000000000), orderedInterval (55390736683 / 1000000000000) (55390737370 / 1000000000000)))) (orderedInterval (-6644446509 / 1000000000000) (-6644446416 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 1) <| besselDerivativeNearFromState (533471648731329 / 4000000000000) 1 (IntervalRat.scale (231 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (55634968091 / 1000000000000) (55635024359 / 1000000000000), orderedInterval (-41173798873 / 1000000000000) (-41173742604 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 1) <| besselDerivativeNearFromState (914112762834117 / 4000000000000) 1 (IntervalRat.scale (231 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (1225537892 / 1000000000000) (1225537895 / 1000000000000), orderedInterval (-52768609640 / 1000000000000) (-52768609637 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 1) <| besselDerivativeNearFromState (673331323783503 / 4000000000000) 1 (IntervalRat.scale (231 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-31010104705 / 1000000000000) (-31010100107 / 1000000000000), orderedInterval (53198534016 / 1000000000000) (53198538614 / 1000000000000)))) (orderedInterval (5094177305 / 1000000000000) (5094177479 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate238_chunkChecks1_1 :
    compactCertificate238.chunkChecks (1 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 1) <| besselDerivativeNearFromState (1033063405604769 / 4000000000000) 1 (IntervalRat.scale (231 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (49225510137 / 1000000000000) (49225510152 / 1000000000000), orderedInterval (6371785693 / 1000000000000) (6371785708 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 1) <| besselDerivativeNearFromState (596439435315801 / 4000000000000) 1 (IntervalRat.scale (231 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-51265680902 / 1000000000000) (-51265600137 / 1000000000000), orderedInterval (40684777617 / 1000000000000) (40684858382 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 1) <| besselDerivativeNearFromState (1058392244480109 / 4000000000000) 1 (IntervalRat.scale (231 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (48887645441 / 1000000000000) (48887645475 / 1000000000000), orderedInterval (3905359993 / 1000000000000) (3905360027 / 1000000000000)))) (orderedInterval (2631765042 / 1000000000000) (2631772880 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 1) <| besselDerivativeNearFromState (988887325824321 / 4000000000000) 1 (IntervalRat.scale (231 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (9039762521 / 1000000000000) (9039762554 / 1000000000000), orderedInterval (-49952067890 / 1000000000000) (-49952067857 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 1) <| besselDerivativeNearFromState (705716657022993 / 4000000000000) 1 (IntervalRat.scale (231 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (57627255277 / 1000000000000) (57627255278 / 1000000000000), orderedInterval (16790927784 / 1000000000000) (16790927786 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 1) <| besselDerivativeNearFromState (800207473096647 / 4000000000000) 1 (IntervalRat.scale (231 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-12601625746 / 1000000000000) (-12601625653 / 1000000000000), orderedInterval (55017689768 / 1000000000000) (55017689861 / 1000000000000)))) (orderedInterval (3873395313 / 1000000000000) (3873395339 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 1) <| besselDerivativeNearFromState (667129565245143 / 4000000000000) 1 (IntervalRat.scale (231 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-53975347739 / 1000000000000) (-53975347738 / 1000000000000), orderedInterval (-29900141583 / 1000000000000) (-29900141582 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 1) <| besselDerivativeNearFromState (589429202904003 / 4000000000000) 1 (IntervalRat.scale (231 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-30759121781 / 1000000000000) (-30759121780 / 1000000000000), orderedInterval (-57982948107 / 1000000000000) (-57982948106 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 1) <| besselDerivativeNearFromState (170839557108297 / 800000000000) 1 (IntervalRat.scale (231 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (35422304313 / 1000000000000) (35422304314 / 1000000000000), orderedInterval (41466995500 / 1000000000000) (41466995501 / 1000000000000)))) (orderedInterval (5697836768 / 1000000000000) (5697836785 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate238_chunkChecks1_2 :
    compactCertificate238.chunkChecks (1 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 1) <| besselDerivativeNearFromState (472551205754859 / 4000000000000) 1 (IntervalRat.scale (231 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-32482715667 / 1000000000000) (-32482712837 / 1000000000000), orderedInterval (65968260017 / 1000000000000) (65968262848 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 1) <| besselDerivativeNearFromState (400586890479699 / 4000000000000) 1 (IntervalRat.scale (231 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (31041352239 / 1000000000000) (31041352240 / 1000000000000), orderedInterval (73284526179 / 1000000000000) (73284526180 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 1) <| besselDerivativeNearFromState (250668676216497 / 4000000000000) 1 (IntervalRat.scale (231 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (58456882610 / 1000000000000) (58456882611 / 1000000000000), orderedInterval (81641133066 / 1000000000000) (81641133067 / 1000000000000)))) (orderedInterval (-12943167547 / 1000000000000) (-12943167057 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 1) <| besselDerivativeNearFromState (134810447755599 / 4000000000000) 1 (IntervalRat.scale (231 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (10053195484 / 1000000000000) (10053195517 / 1000000000000), orderedInterval (-137226891353 / 1000000000000) (-137226891320 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 1) <| besselDerivativeNearFromState (366036590023797 / 4000000000000) 1 (IntervalRat.scale (231 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-77339268470 / 1000000000000) (-77339268469 / 1000000000000), orderedInterval (-30809798642 / 1000000000000) (-30809798641 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 1) <| besselDerivativeNearFromState (499791670246869 / 4000000000000) 1 (IntervalRat.scale (231 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (4893452548 / 1000000000000) (4893452550 / 1000000000000), orderedInterval (71192605658 / 1000000000000) (71192605661 / 1000000000000)))) (orderedInterval (-4609252678 / 1000000000000) (-4609252664 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 1) <| besselDerivativeNearFromState (211331323783503 / 4000000000000) 1 (IntervalRat.scale (231 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-22752284493 / 1000000000000) (-22752284492 / 1000000000000), orderedInterval (-107174298267 / 1000000000000) (-107174298266 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 1) <| besselDerivativeNearFromState (859050098415663 / 4000000000000) 1 (IntervalRat.scale (231 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (51177110890 / 1000000000000) (51177116295 / 1000000000000), orderedInterval (-18698526909 / 1000000000000) (-18698521504 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 1) <| besselDerivativeNearFromState (573805653869217 / 4000000000000) 1 (IntervalRat.scale (231 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-18238505079 / 1000000000000) (-18238504801 / 1000000000000), orderedInterval (64135850134 / 1000000000000) (64135850411 / 1000000000000)))) (orderedInterval (-12411089790 / 1000000000000) (-12411088861 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate238_chunkChecks1 :
    compactCertificate238.chunkChecks (1 : Fin 5) 0 9 = true :=
  compactCertificate238.chunkChecks_nine_of_three (1 : Fin 5) compactCertificate238_chunkChecks1_0
    compactCertificate238_chunkChecks1_1 compactCertificate238_chunkChecks1_2

theorem compactCertificate238_chunkChecks2_0 :
    compactCertificate238.chunkChecks (2 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 2) <| besselDerivativeNearFromState (231 / 2) 2 (IntervalRat.scale (231 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-3368501736 / 1000000000000) (-3368501733 / 1000000000000), orderedInterval (-74151206122 / 1000000000000) (-74151206118 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 2) <| besselDerivativeNearFromState (340307108965131 / 4000000000000) 2 (IntervalRat.scale (231 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-74499778082 / 1000000000000) (-74499778081 / 1000000000000), orderedInterval (-43523591289 / 1000000000000) (-43523591288 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 2) <| besselDerivativeNearFromState (110048326988523 / 800000000000) 2 (IntervalRat.scale (231 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (7793998364 / 1000000000000) (7793998366 / 1000000000000), orderedInterval (67552823109 / 1000000000000) (67552823111 / 1000000000000)))) (orderedInterval (1279227213 / 1000000000000) (1279227226 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 2) <| besselDerivativeNearFromState (99300765658017 / 4000000000000) 2 (IntervalRat.scale (231 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (72918779631 / 1000000000000) (72918779632 / 1000000000000), orderedInterval (141115226498 / 1000000000000) (141115226499 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 2) <| besselDerivativeNearFromState (266735824365549 / 4000000000000) 2 (IntervalRat.scale (231 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-97418738204 / 1000000000000) (-97418738196 / 1000000000000), orderedInterval (-6762589290 / 1000000000000) (-6762589282 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 2) <| besselDerivativeNearFromState (724239650659833 / 4000000000000) 2 (IntervalRat.scale (231 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-21318229895 / 1000000000000) (-21318229208 / 1000000000000), orderedInterval (55390736683 / 1000000000000) (55390737370 / 1000000000000)))) (orderedInterval (-2444525562 / 1000000000000) (-2444525419 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 2) <| besselDerivativeNearFromState (533471648731329 / 4000000000000) 2 (IntervalRat.scale (231 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (55634968091 / 1000000000000) (55635024359 / 1000000000000), orderedInterval (-41173798873 / 1000000000000) (-41173742604 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 2) <| besselDerivativeNearFromState (914112762834117 / 4000000000000) 2 (IntervalRat.scale (231 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (1225537892 / 1000000000000) (1225537895 / 1000000000000), orderedInterval (-52768609640 / 1000000000000) (-52768609637 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 2) <| besselDerivativeNearFromState (673331323783503 / 4000000000000) 2 (IntervalRat.scale (231 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-31010104705 / 1000000000000) (-31010100107 / 1000000000000), orderedInterval (53198534016 / 1000000000000) (53198538614 / 1000000000000)))) (orderedInterval (1695786289 / 1000000000000) (1695786548 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate238_chunkChecks2_1 :
    compactCertificate238.chunkChecks (2 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 2) <| besselDerivativeNearFromState (1033063405604769 / 4000000000000) 2 (IntervalRat.scale (231 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (49225510137 / 1000000000000) (49225510152 / 1000000000000), orderedInterval (6371785693 / 1000000000000) (6371785708 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 2) <| besselDerivativeNearFromState (596439435315801 / 4000000000000) 2 (IntervalRat.scale (231 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-51265680902 / 1000000000000) (-51265600137 / 1000000000000), orderedInterval (40684777617 / 1000000000000) (40684858382 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 2) <| besselDerivativeNearFromState (1058392244480109 / 4000000000000) 2 (IntervalRat.scale (231 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (48887645441 / 1000000000000) (48887645475 / 1000000000000), orderedInterval (3905359993 / 1000000000000) (3905360027 / 1000000000000)))) (orderedInterval (13568551476 / 1000000000000) (13568561759 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 2) <| besselDerivativeNearFromState (988887325824321 / 4000000000000) 2 (IntervalRat.scale (231 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (9039762521 / 1000000000000) (9039762554 / 1000000000000), orderedInterval (-49952067890 / 1000000000000) (-49952067857 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 2) <| besselDerivativeNearFromState (705716657022993 / 4000000000000) 2 (IntervalRat.scale (231 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (57627255277 / 1000000000000) (57627255278 / 1000000000000), orderedInterval (16790927784 / 1000000000000) (16790927786 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 2) <| besselDerivativeNearFromState (800207473096647 / 4000000000000) 2 (IntervalRat.scale (231 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-12601625746 / 1000000000000) (-12601625653 / 1000000000000), orderedInterval (55017689768 / 1000000000000) (55017689861 / 1000000000000)))) (orderedInterval (-12192429245 / 1000000000000) (-12192429203 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 2) <| besselDerivativeNearFromState (667129565245143 / 4000000000000) 2 (IntervalRat.scale (231 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-53975347739 / 1000000000000) (-53975347738 / 1000000000000), orderedInterval (-29900141583 / 1000000000000) (-29900141582 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 2) <| besselDerivativeNearFromState (589429202904003 / 4000000000000) 2 (IntervalRat.scale (231 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-30759121781 / 1000000000000) (-30759121780 / 1000000000000), orderedInterval (-57982948107 / 1000000000000) (-57982948106 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 2) <| besselDerivativeNearFromState (170839557108297 / 800000000000) 2 (IntervalRat.scale (231 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (35422304313 / 1000000000000) (35422304314 / 1000000000000), orderedInterval (41466995500 / 1000000000000) (41466995501 / 1000000000000)))) (orderedInterval (-4715254504 / 1000000000000) (-4715254479 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate238_chunkChecks2_2 :
    compactCertificate238.chunkChecks (2 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 2) <| besselDerivativeNearFromState (472551205754859 / 4000000000000) 2 (IntervalRat.scale (231 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-32482715667 / 1000000000000) (-32482712837 / 1000000000000), orderedInterval (65968260017 / 1000000000000) (65968262848 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 2) <| besselDerivativeNearFromState (400586890479699 / 4000000000000) 2 (IntervalRat.scale (231 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (31041352239 / 1000000000000) (31041352240 / 1000000000000), orderedInterval (73284526179 / 1000000000000) (73284526180 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 2) <| besselDerivativeNearFromState (250668676216497 / 4000000000000) 2 (IntervalRat.scale (231 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (58456882610 / 1000000000000) (58456882611 / 1000000000000), orderedInterval (81641133066 / 1000000000000) (81641133067 / 1000000000000)))) (orderedInterval (-4560968072 / 1000000000000) (-4560967568 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 2) <| besselDerivativeNearFromState (134810447755599 / 4000000000000) 2 (IntervalRat.scale (231 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (10053195484 / 1000000000000) (10053195517 / 1000000000000), orderedInterval (-137226891353 / 1000000000000) (-137226891320 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 2) <| besselDerivativeNearFromState (366036590023797 / 4000000000000) 2 (IntervalRat.scale (231 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-77339268470 / 1000000000000) (-77339268469 / 1000000000000), orderedInterval (-30809798642 / 1000000000000) (-30809798641 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 2) <| besselDerivativeNearFromState (499791670246869 / 4000000000000) 2 (IntervalRat.scale (231 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (4893452548 / 1000000000000) (4893452550 / 1000000000000), orderedInterval (71192605658 / 1000000000000) (71192605661 / 1000000000000)))) (orderedInterval (-606780228 / 1000000000000) (-606780214 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 2) <| besselDerivativeNearFromState (211331323783503 / 4000000000000) 2 (IntervalRat.scale (231 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-22752284493 / 1000000000000) (-22752284492 / 1000000000000), orderedInterval (-107174298267 / 1000000000000) (-107174298266 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 2) <| besselDerivativeNearFromState (859050098415663 / 4000000000000) 2 (IntervalRat.scale (231 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (51177110890 / 1000000000000) (51177116295 / 1000000000000), orderedInterval (-18698526909 / 1000000000000) (-18698521504 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 2) <| besselDerivativeNearFromState (573805653869217 / 4000000000000) 2 (IntervalRat.scale (231 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-18238505079 / 1000000000000) (-18238504801 / 1000000000000), orderedInterval (64135850134 / 1000000000000) (64135850411 / 1000000000000)))) (orderedInterval (9260750005 / 1000000000000) (9260751681 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate238_chunkChecks2 :
    compactCertificate238.chunkChecks (2 : Fin 5) 0 9 = true :=
  compactCertificate238.chunkChecks_nine_of_three (2 : Fin 5) compactCertificate238_chunkChecks2_0
    compactCertificate238_chunkChecks2_1 compactCertificate238_chunkChecks2_2

theorem compactCertificate238_chunkChecks3_0 :
    compactCertificate238.chunkChecks (3 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 3) <| besselDerivativeNearFromState (231 / 2) 3 (IntervalRat.scale (231 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-3368501736 / 1000000000000) (-3368501733 / 1000000000000), orderedInterval (-74151206122 / 1000000000000) (-74151206118 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 3) <| besselDerivativeNearFromState (340307108965131 / 4000000000000) 3 (IntervalRat.scale (231 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-74499778082 / 1000000000000) (-74499778081 / 1000000000000), orderedInterval (-43523591289 / 1000000000000) (-43523591288 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 3) <| besselDerivativeNearFromState (110048326988523 / 800000000000) 3 (IntervalRat.scale (231 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (7793998364 / 1000000000000) (7793998366 / 1000000000000), orderedInterval (67552823109 / 1000000000000) (67552823111 / 1000000000000)))) (orderedInterval (22843137134 / 1000000000000) (22843137149 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 3) <| besselDerivativeNearFromState (99300765658017 / 4000000000000) 3 (IntervalRat.scale (231 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (72918779631 / 1000000000000) (72918779632 / 1000000000000), orderedInterval (141115226498 / 1000000000000) (141115226499 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 3) <| besselDerivativeNearFromState (266735824365549 / 4000000000000) 3 (IntervalRat.scale (231 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-97418738204 / 1000000000000) (-97418738196 / 1000000000000), orderedInterval (-6762589290 / 1000000000000) (-6762589282 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 3) <| besselDerivativeNearFromState (724239650659833 / 4000000000000) 3 (IntervalRat.scale (231 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-21318229895 / 1000000000000) (-21318229208 / 1000000000000), orderedInterval (55390736683 / 1000000000000) (55390737370 / 1000000000000)))) (orderedInterval (15252648653 / 1000000000000) (15252648876 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 3) <| besselDerivativeNearFromState (533471648731329 / 4000000000000) 3 (IntervalRat.scale (231 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (55634968091 / 1000000000000) (55635024359 / 1000000000000), orderedInterval (-41173798873 / 1000000000000) (-41173742604 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 3) <| besselDerivativeNearFromState (914112762834117 / 4000000000000) 3 (IntervalRat.scale (231 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (1225537892 / 1000000000000) (1225537895 / 1000000000000), orderedInterval (-52768609640 / 1000000000000) (-52768609637 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 3) <| besselDerivativeNearFromState (673331323783503 / 4000000000000) 3 (IntervalRat.scale (231 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-31010104705 / 1000000000000) (-31010100107 / 1000000000000), orderedInterval (53198534016 / 1000000000000) (53198538614 / 1000000000000)))) (orderedInterval (-16601700699 / 1000000000000) (-16601700314 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate238_chunkChecks3_1 :
    compactCertificate238.chunkChecks (3 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 3) <| besselDerivativeNearFromState (1033063405604769 / 4000000000000) 3 (IntervalRat.scale (231 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (49225510137 / 1000000000000) (49225510152 / 1000000000000), orderedInterval (6371785693 / 1000000000000) (6371785708 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 3) <| besselDerivativeNearFromState (596439435315801 / 4000000000000) 3 (IntervalRat.scale (231 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-51265680902 / 1000000000000) (-51265600137 / 1000000000000), orderedInterval (40684777617 / 1000000000000) (40684858382 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 3) <| besselDerivativeNearFromState (1058392244480109 / 4000000000000) 3 (IntervalRat.scale (231 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (48887645441 / 1000000000000) (48887645475 / 1000000000000), orderedInterval (3905359993 / 1000000000000) (3905360027 / 1000000000000)))) (orderedInterval (-619828254 / 1000000000000) (-619814759 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 3) <| besselDerivativeNearFromState (988887325824321 / 4000000000000) 3 (IntervalRat.scale (231 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (9039762521 / 1000000000000) (9039762554 / 1000000000000), orderedInterval (-49952067890 / 1000000000000) (-49952067857 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 3) <| besselDerivativeNearFromState (705716657022993 / 4000000000000) 3 (IntervalRat.scale (231 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (57627255277 / 1000000000000) (57627255278 / 1000000000000), orderedInterval (16790927784 / 1000000000000) (16790927786 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 3) <| besselDerivativeNearFromState (800207473096647 / 4000000000000) 3 (IntervalRat.scale (231 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-12601625746 / 1000000000000) (-12601625653 / 1000000000000), orderedInterval (55017689768 / 1000000000000) (55017689861 / 1000000000000)))) (orderedInterval (-12950102853 / 1000000000000) (-12950102781 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 3) <| besselDerivativeNearFromState (667129565245143 / 4000000000000) 3 (IntervalRat.scale (231 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-53975347739 / 1000000000000) (-53975347738 / 1000000000000), orderedInterval (-29900141583 / 1000000000000) (-29900141582 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 3) <| besselDerivativeNearFromState (589429202904003 / 4000000000000) 3 (IntervalRat.scale (231 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-30759121781 / 1000000000000) (-30759121780 / 1000000000000), orderedInterval (-57982948107 / 1000000000000) (-57982948106 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 3) <| besselDerivativeNearFromState (170839557108297 / 800000000000) 3 (IntervalRat.scale (231 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (35422304313 / 1000000000000) (35422304314 / 1000000000000), orderedInterval (41466995500 / 1000000000000) (41466995501 / 1000000000000)))) (orderedInterval (-12520467943 / 1000000000000) (-12520467905 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate238_chunkChecks3_2 :
    compactCertificate238.chunkChecks (3 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 3) <| besselDerivativeNearFromState (472551205754859 / 4000000000000) 3 (IntervalRat.scale (231 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-32482715667 / 1000000000000) (-32482712837 / 1000000000000), orderedInterval (65968260017 / 1000000000000) (65968262848 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 3) <| besselDerivativeNearFromState (400586890479699 / 4000000000000) 3 (IntervalRat.scale (231 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (31041352239 / 1000000000000) (31041352240 / 1000000000000), orderedInterval (73284526179 / 1000000000000) (73284526180 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 3) <| besselDerivativeNearFromState (250668676216497 / 4000000000000) 3 (IntervalRat.scale (231 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (58456882610 / 1000000000000) (58456882611 / 1000000000000), orderedInterval (81641133066 / 1000000000000) (81641133067 / 1000000000000)))) (orderedInterval (13605038515 / 1000000000000) (13605039030 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 3) <| besselDerivativeNearFromState (134810447755599 / 4000000000000) 3 (IntervalRat.scale (231 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (10053195484 / 1000000000000) (10053195517 / 1000000000000), orderedInterval (-137226891353 / 1000000000000) (-137226891320 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 3) <| besselDerivativeNearFromState (366036590023797 / 4000000000000) 3 (IntervalRat.scale (231 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-77339268470 / 1000000000000) (-77339268469 / 1000000000000), orderedInterval (-30809798642 / 1000000000000) (-30809798641 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 3) <| besselDerivativeNearFromState (499791670246869 / 4000000000000) 3 (IntervalRat.scale (231 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (4893452548 / 1000000000000) (4893452550 / 1000000000000), orderedInterval (71192605658 / 1000000000000) (71192605661 / 1000000000000)))) (orderedInterval (6501894091 / 1000000000000) (6501894105 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 3) <| besselDerivativeNearFromState (211331323783503 / 4000000000000) 3 (IntervalRat.scale (231 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-22752284493 / 1000000000000) (-22752284492 / 1000000000000), orderedInterval (-107174298267 / 1000000000000) (-107174298266 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 3) <| besselDerivativeNearFromState (859050098415663 / 4000000000000) 3 (IntervalRat.scale (231 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (51177110890 / 1000000000000) (51177116295 / 1000000000000), orderedInterval (-18698526909 / 1000000000000) (-18698521504 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 3) <| besselDerivativeNearFromState (573805653869217 / 4000000000000) 3 (IntervalRat.scale (231 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-18238505079 / 1000000000000) (-18238504801 / 1000000000000), orderedInterval (64135850134 / 1000000000000) (64135850411 / 1000000000000)))) (orderedInterval (13250423338 / 1000000000000) (13250426383 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate238_chunkChecks3 :
    compactCertificate238.chunkChecks (3 : Fin 5) 0 9 = true :=
  compactCertificate238.chunkChecks_nine_of_three (3 : Fin 5) compactCertificate238_chunkChecks3_0
    compactCertificate238_chunkChecks3_1 compactCertificate238_chunkChecks3_2

theorem compactCertificate238_chunkChecks4_0 :
    compactCertificate238.chunkChecks (4 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 4) <| besselDerivativeNearFromState (231 / 2) 4 (IntervalRat.scale (231 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-3368501736 / 1000000000000) (-3368501733 / 1000000000000), orderedInterval (-74151206122 / 1000000000000) (-74151206118 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 4) <| besselDerivativeNearFromState (340307108965131 / 4000000000000) 4 (IntervalRat.scale (231 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-74499778082 / 1000000000000) (-74499778081 / 1000000000000), orderedInterval (-43523591289 / 1000000000000) (-43523591288 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 4) <| besselDerivativeNearFromState (110048326988523 / 800000000000) 4 (IntervalRat.scale (231 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (7793998364 / 1000000000000) (7793998366 / 1000000000000), orderedInterval (67552823109 / 1000000000000) (67552823111 / 1000000000000)))) (orderedInterval (-1014708887 / 1000000000000) (-1014708871 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 4) <| besselDerivativeNearFromState (99300765658017 / 4000000000000) 4 (IntervalRat.scale (231 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (72918779631 / 1000000000000) (72918779632 / 1000000000000), orderedInterval (141115226498 / 1000000000000) (141115226499 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 4) <| besselDerivativeNearFromState (266735824365549 / 4000000000000) 4 (IntervalRat.scale (231 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-97418738204 / 1000000000000) (-97418738196 / 1000000000000), orderedInterval (-6762589290 / 1000000000000) (-6762589282 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 4) <| besselDerivativeNearFromState (724239650659833 / 4000000000000) 4 (IntervalRat.scale (231 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-21318229895 / 1000000000000) (-21318229208 / 1000000000000), orderedInterval (55390736683 / 1000000000000) (55390737370 / 1000000000000)))) (orderedInterval (8490860683 / 1000000000000) (8490861033 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 4) <| besselDerivativeNearFromState (533471648731329 / 4000000000000) 4 (IntervalRat.scale (231 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (55634968091 / 1000000000000) (55635024359 / 1000000000000), orderedInterval (-41173798873 / 1000000000000) (-41173742604 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 4) <| besselDerivativeNearFromState (914112762834117 / 4000000000000) 4 (IntervalRat.scale (231 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (1225537892 / 1000000000000) (1225537895 / 1000000000000), orderedInterval (-52768609640 / 1000000000000) (-52768609637 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 4) <| besselDerivativeNearFromState (673331323783503 / 4000000000000) 4 (IntervalRat.scale (231 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-31010104705 / 1000000000000) (-31010100107 / 1000000000000), orderedInterval (53198534016 / 1000000000000) (53198538614 / 1000000000000)))) (orderedInterval (-3673097437 / 1000000000000) (-3673096861 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate238_chunkChecks4_1 :
    compactCertificate238.chunkChecks (4 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 4) <| besselDerivativeNearFromState (1033063405604769 / 4000000000000) 4 (IntervalRat.scale (231 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (49225510137 / 1000000000000) (49225510152 / 1000000000000), orderedInterval (6371785693 / 1000000000000) (6371785708 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 4) <| besselDerivativeNearFromState (596439435315801 / 4000000000000) 4 (IntervalRat.scale (231 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-51265680902 / 1000000000000) (-51265600137 / 1000000000000), orderedInterval (40684777617 / 1000000000000) (40684858382 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 4) <| besselDerivativeNearFromState (1058392244480109 / 4000000000000) 4 (IntervalRat.scale (231 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (48887645441 / 1000000000000) (48887645475 / 1000000000000), orderedInterval (3905359993 / 1000000000000) (3905360027 / 1000000000000)))) (orderedInterval (-37790778654 / 1000000000000) (-37790760619 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 4) <| besselDerivativeNearFromState (988887325824321 / 4000000000000) 4 (IntervalRat.scale (231 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (9039762521 / 1000000000000) (9039762554 / 1000000000000), orderedInterval (-49952067890 / 1000000000000) (-49952067857 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 4) <| besselDerivativeNearFromState (705716657022993 / 4000000000000) 4 (IntervalRat.scale (231 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (57627255277 / 1000000000000) (57627255278 / 1000000000000), orderedInterval (16790927784 / 1000000000000) (16790927786 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 4) <| besselDerivativeNearFromState (800207473096647 / 4000000000000) 4 (IntervalRat.scale (231 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-12601625746 / 1000000000000) (-12601625653 / 1000000000000), orderedInterval (55017689768 / 1000000000000) (55017689861 / 1000000000000)))) (orderedInterval (27040687671 / 1000000000000) (27040687798 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 4) <| besselDerivativeNearFromState (667129565245143 / 4000000000000) 4 (IntervalRat.scale (231 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-53975347739 / 1000000000000) (-53975347738 / 1000000000000), orderedInterval (-29900141583 / 1000000000000) (-29900141582 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 4) <| besselDerivativeNearFromState (589429202904003 / 4000000000000) 4 (IntervalRat.scale (231 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-30759121781 / 1000000000000) (-30759121780 / 1000000000000), orderedInterval (-57982948107 / 1000000000000) (-57982948106 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 4) <| besselDerivativeNearFromState (170839557108297 / 800000000000) 4 (IntervalRat.scale (231 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (35422304313 / 1000000000000) (35422304314 / 1000000000000), orderedInterval (41466995500 / 1000000000000) (41466995501 / 1000000000000)))) (orderedInterval (12768822535 / 1000000000000) (12768822594 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate238_chunkChecks4_2 :
    compactCertificate238.chunkChecks (4 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 4) <| besselDerivativeNearFromState (472551205754859 / 4000000000000) 4 (IntervalRat.scale (231 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-32482715667 / 1000000000000) (-32482712837 / 1000000000000), orderedInterval (65968260017 / 1000000000000) (65968262848 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 4) <| besselDerivativeNearFromState (400586890479699 / 4000000000000) 4 (IntervalRat.scale (231 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (31041352239 / 1000000000000) (31041352240 / 1000000000000), orderedInterval (73284526179 / 1000000000000) (73284526180 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 4) <| besselDerivativeNearFromState (250668676216497 / 4000000000000) 4 (IntervalRat.scale (231 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (58456882610 / 1000000000000) (58456882611 / 1000000000000), orderedInterval (81641133066 / 1000000000000) (81641133067 / 1000000000000)))) (orderedInterval (4620650515 / 1000000000000) (4620651044 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 4) <| besselDerivativeNearFromState (134810447755599 / 4000000000000) 4 (IntervalRat.scale (231 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (10053195484 / 1000000000000) (10053195517 / 1000000000000), orderedInterval (-137226891353 / 1000000000000) (-137226891320 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 4) <| besselDerivativeNearFromState (366036590023797 / 4000000000000) 4 (IntervalRat.scale (231 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-77339268470 / 1000000000000) (-77339268469 / 1000000000000), orderedInterval (-30809798642 / 1000000000000) (-30809798641 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 4) <| besselDerivativeNearFromState (499791670246869 / 4000000000000) 4 (IntervalRat.scale (231 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (4893452548 / 1000000000000) (4893452550 / 1000000000000), orderedInterval (71192605658 / 1000000000000) (71192605661 / 1000000000000)))) (orderedInterval (63752671 / 1000000000000) (63752686 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 4) <| besselDerivativeNearFromState (211331323783503 / 4000000000000) 4 (IntervalRat.scale (231 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-22752284493 / 1000000000000) (-22752284492 / 1000000000000), orderedInterval (-107174298267 / 1000000000000) (-107174298266 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 4) <| besselDerivativeNearFromState (859050098415663 / 4000000000000) 4 (IntervalRat.scale (231 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (51177110890 / 1000000000000) (51177116295 / 1000000000000), orderedInterval (-18698526909 / 1000000000000) (-18698521504 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 4) <| besselDerivativeNearFromState (573805653869217 / 4000000000000) 4 (IntervalRat.scale (231 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-18238505079 / 1000000000000) (-18238504801 / 1000000000000), orderedInterval (64135850134 / 1000000000000) (64135850411 / 1000000000000)))) (orderedInterval (-41890369607 / 1000000000000) (-41890364008 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate238_chunkChecks4 :
    compactCertificate238.chunkChecks (4 : Fin 5) 0 9 = true :=
  compactCertificate238.chunkChecks_nine_of_three (4 : Fin 5) compactCertificate238_chunkChecks4_0
    compactCertificate238_chunkChecks4_1 compactCertificate238_chunkChecks4_2

theorem compactCertificate238_chunks :
    ∀ r : Fin 5, ∀ b, compactCertificate238.chunkCheck r b = true :=
  compactCertificate238.chunkChecks_all (by
    intro r
    fin_cases r
    · exact compactCertificate238_chunkChecks0
    · exact compactCertificate238_chunkChecks1
    · exact compactCertificate238_chunkChecks2
    · exact compactCertificate238_chunkChecks3
    · exact compactCertificate238_chunkChecks4)

theorem compactCertificate238_coefficient0 :
    compactCertificate238.coefficientCheck (0 : Fin 5) = true := by
  norm_num [CompactCertificate.coefficientCheck, intervalFinSumHull,
    compactCertificate238, rationalIntervalSubset, orderedInterval, Fin.sum_univ_succ]

theorem compactCertificate238_coefficient1 :
    compactCertificate238.coefficientCheck (1 : Fin 5) = true := by
  norm_num [CompactCertificate.coefficientCheck, intervalFinSumHull,
    compactCertificate238, rationalIntervalSubset, orderedInterval, Fin.sum_univ_succ]

theorem compactCertificate238_coefficient2 :
    compactCertificate238.coefficientCheck (2 : Fin 5) = true := by
  norm_num [CompactCertificate.coefficientCheck, intervalFinSumHull,
    compactCertificate238, rationalIntervalSubset, orderedInterval, Fin.sum_univ_succ]

theorem compactCertificate238_coefficient3 :
    compactCertificate238.coefficientCheck (3 : Fin 5) = true := by
  norm_num [CompactCertificate.coefficientCheck, intervalFinSumHull,
    compactCertificate238, rationalIntervalSubset, orderedInterval, Fin.sum_univ_succ]

theorem compactCertificate238_coefficient4 :
    compactCertificate238.coefficientCheck (4 : Fin 5) = true := by
  norm_num [CompactCertificate.coefficientCheck, intervalFinSumHull,
    compactCertificate238, rationalIntervalSubset, orderedInterval, Fin.sum_univ_succ]

theorem compactCertificate238_coefficients : ∀ r : Fin 5,
    compactCertificate238.coefficientCheck r = true := by
  intro r
  fin_cases r
  · exact compactCertificate238_coefficient0
  · exact compactCertificate238_coefficient1
  · exact compactCertificate238_coefficient2
  · exact compactCertificate238_coefficient3
  · exact compactCertificate238_coefficient4

theorem compactCertificate238_lower : (1 : ℚ) ≤ compactCertificate238.output.lo := by
  norm_num [CompactCertificate.output, CompactCertificate.interval,
    CompactCertificate.coefficientTargetNat, compactCertificate238, dualConstant,
    intervalTaylorSum, intervalPow, intervalSub, intervalMaxAbs, widenInterval,
    rationalErrorInterval, orderedInterval, IntervalRat.add, IntervalRat.mul, IntervalRat.scale,
    IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4]

theorem compactCertificate238_proves {t : ℝ} (ht : t ∈ compactCertificate238.interval) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t :=
  compactCertificate238.proves compactCertificate238_states compactCertificate238_chunks
    compactCertificate238_coefficients compactCertificate238_lower ht

end Erdos232
