/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, OpenAI Codex
-/
import ErdosProblems.Erdos232.CompactBase

open LeanCert.Core
namespace Erdos232

def compactCertificate215 : CompactCertificate where
  left := 96
  right := 97
  center := 193 / 2
  grid := fun i =>
    match i.val with
    | 0 => 31
    | 1 => 23
    | 2 => 37
    | 3 => 7
    | 4 => 18
    | 5 => 48
    | 6 => 35
    | 7 => 61
    | 8 => 45
    | 9 => 69
    | 10 => 40
    | 11 => 70
    | 12 => 66
    | 13 => 47
    | 14 => 53
    | 15 => 44
    | 16 => 39
    | 17 => 57
    | 18 => 31
    | 19 => 27
    | 20 => 17
    | 21 => 9
    | 22 => 24
    | 23 => 33
    | 24 => 14
    | 25 => 57
    | _ => 38
  point := fun i =>
    match i.val with
    | 0 => 193 / 2
    | 1 => 284325852944893 / 4000000000000
    | 2 => 91945138999069 / 800000000000
    | 3 => 82965574770551 / 4000000000000
    | 4 => 222857203907147 / 4000000000000
    | 5 => 605100660507999 / 4000000000000
    | 6 => 445714407814487 / 4000000000000
    | 7 => 763739234748851 / 4000000000000
    | 8 => 562566863594009 / 4000000000000
    | 9 => 863122239314807 / 4000000000000
    | 10 => 498323857211903 / 4000000000000
    | 11 => 884284429370827 / 4000000000000
    | 12 => 826213220277463 / 4000000000000
    | 13 => 589624739417479 / 4000000000000
    | 14 => 668571611721441 / 4000000000000
    | 15 => 557385307758929 / 4000000000000
    | 16 => 492466823205509 / 4000000000000
    | 17 => 142736080181391 / 800000000000
    | 18 => 394815509570077 / 4000000000000
    | 19 => 334689479924597 / 4000000000000
    | 20 => 209433136405991 / 4000000000000
    | 21 => 112633837302297 / 4000000000000
    | 22 => 305822778677891 / 4000000000000
    | 23 => 417574858691107 / 4000000000000
    | 24 => 176566863594009 / 4000000000000
    | 25 => 717734497810489 / 4000000000000
    | _ => 479413381804151 / 4000000000000
  state := fun i =>
    match i.val with
    | 0 => (orderedInterval (8534401478 / 1000000000000) (8534401512 / 1000000000000), orderedInterval (-80817646471 / 1000000000000) (-80817646437 / 1000000000000))
    | 1 => (orderedInterval (36113224312 / 1000000000000) (36113226048 / 1000000000000), orderedInterval (-87730821091 / 1000000000000) (-87730819355 / 1000000000000))
    | 2 => (orderedInterval (37186374071 / 1000000000000) (37186379828 / 1000000000000), orderedInterval (-64631356266 / 1000000000000) (-64631350509 / 1000000000000))
    | 3 => (orderedInterval (79390542472 / 1000000000000) (79390547660 / 1000000000000), orderedInterval (-158103558079 / 1000000000000) (-158103552892 / 1000000000000))
    | 4 => (orderedInterval (-5471778236 / 1000000000000) (-5471778215 / 1000000000000), orderedInterval (106805941069 / 1000000000000) (106805941089 / 1000000000000))
    | 5 => (orderedInterval (61828615662 / 1000000000000) (61828615663 / 1000000000000), orderedInterval (19431317445 / 1000000000000) (19431317446 / 1000000000000))
    | 6 => (orderedInterval (-58470936937 / 1000000000000) (-58470857030 / 1000000000000), orderedInterval (48162170069 / 1000000000000) (48162249975 / 1000000000000))
    | 7 => (orderedInterval (-4752630726 / 1000000000000) (-4752630725 / 1000000000000), orderedInterval (-57534488420 / 1000000000000) (-57534488418 / 1000000000000))
    | 8 => (orderedInterval (-3668662868 / 1000000000000) (-3668662865 / 1000000000000), orderedInterval (-67166606432 / 1000000000000) (-67166606429 / 1000000000000))
    | 9 => (orderedInterval (11031269243 / 1000000000000) (11031269305 / 1000000000000), orderedInterval (-53210422077 / 1000000000000) (-53210422016 / 1000000000000))
    | 10 => (orderedInterval (-21012228117 / 1000000000000) (-21012227705 / 1000000000000), orderedInterval (68411549904 / 1000000000000) (68411550316 / 1000000000000))
    | 11 => (orderedInterval (49959993961 / 1000000000000) (49960001225 / 1000000000000), orderedInterval (-19701237698 / 1000000000000) (-19701230434 / 1000000000000))
    | 12 => (orderedInterval (-389560970 / 1000000000000) (-389560967 / 1000000000000), orderedInterval (55516401517 / 1000000000000) (55516401521 / 1000000000000))
    | 13 => (orderedInterval (-33555228534 / 1000000000000) (-33555228533 / 1000000000000), orderedInterval (-56391683854 / 1000000000000) (-56391683853 / 1000000000000))
    | 14 => (orderedInterval (-61044094340 / 1000000000000) (-61044094334 / 1000000000000), orderedInterval (-8896897994 / 1000000000000) (-8896897989 / 1000000000000))
    | 15 => (orderedInterval (63945230871 / 1000000000000) (63945233832 / 1000000000000), orderedInterval (-22129203515 / 1000000000000) (-22129200553 / 1000000000000))
    | 16 => (orderedInterval (-70589529258 / 1000000000000) (-70589529255 / 1000000000000), orderedInterval (-13422560429 / 1000000000000) (-13422560426 / 1000000000000))
    | 17 => (orderedInterval (-7981324431 / 1000000000000) (-7981324430 / 1000000000000), orderedInterval (-59175660818 / 1000000000000) (-59175660817 / 1000000000000))
    | 18 => (orderedInterval (-69379639062 / 1000000000000) (-69379620913 / 1000000000000), orderedInterval (40801664601 / 1000000000000) (40801682750 / 1000000000000))
    | 19 => (orderedInterval (31275895169 / 1000000000000) (31275896383 / 1000000000000), orderedInterval (-81614168416 / 1000000000000) (-81614167202 / 1000000000000))
    | 20 => (orderedInterval (28962383929 / 1000000000000) (28962384355 / 1000000000000), orderedInterval (-106674721165 / 1000000000000) (-106674720739 / 1000000000000))
    | 21 => (orderedInterval (-92784751829 / 1000000000000) (-92784751828 / 1000000000000), orderedInterval (-116675880265 / 1000000000000) (-116675880264 / 1000000000000))
    | 22 => (orderedInterval (87932943438 / 1000000000000) (87932944493 / 1000000000000), orderedInterval (-24953185588 / 1000000000000) (-24953184533 / 1000000000000))
    | 23 => (orderedInterval (-77923754033 / 1000000000000) (-77923754020 / 1000000000000), orderedInterval (-4733342829 / 1000000000000) (-4733342816 / 1000000000000))
    | 24 => (orderedInterval (97118929104 / 1000000000000) (97118929105 / 1000000000000), orderedInterval (69538638844 / 1000000000000) (69538638845 / 1000000000000))
    | 25 => (orderedInterval (-54308399396 / 1000000000000) (-54308399395 / 1000000000000), orderedInterval (-24313517506 / 1000000000000) (-24313517505 / 1000000000000))
    | _ => (orderedInterval (69325968147 / 1000000000000) (69325968148 / 1000000000000), orderedInterval (22194764991 / 1000000000000) (22194764992 / 1000000000000))
  chunkTarget := fun r b =>
    match r.val with
    | 0 =>
      match b.val with
      | 0 => orderedInterval (5901381992 / 1000000000000) (5901382367 / 1000000000000)
      | 1 => orderedInterval (-5456489429 / 1000000000000) (-5456489359 / 1000000000000)
      | 2 => orderedInterval (57925800 / 1000000000000) (57925807 / 1000000000000)
      | 3 => orderedInterval (3585150929 / 1000000000000) (3585152042 / 1000000000000)
      | 4 => orderedInterval (-2857127529 / 1000000000000) (-2857127517 / 1000000000000)
      | 5 => orderedInterval (4573669178 / 1000000000000) (4573669222 / 1000000000000)
      | 6 => orderedInterval (10265940899 / 1000000000000) (10265943908 / 1000000000000)
      | 7 => orderedInterval (5690347169 / 1000000000000) (5690347207 / 1000000000000)
      | _ => orderedInterval (-8001125672 / 1000000000000) (-8001125644 / 1000000000000)
    | 1 =>
      match b.val with
      | 0 => orderedInterval (-37152471954 / 1000000000000) (-37152471518 / 1000000000000)
      | 1 => orderedInterval (454706103 / 1000000000000) (454706130 / 1000000000000)
      | 2 => orderedInterval (1145391018 / 1000000000000) (1145391028 / 1000000000000)
      | 3 => orderedInterval (21269411546 / 1000000000000) (21269414056 / 1000000000000)
      | 4 => orderedInterval (-10212884376 / 1000000000000) (-10212884356 / 1000000000000)
      | 5 => orderedInterval (-2190352065 / 1000000000000) (-2190352001 / 1000000000000)
      | 6 => orderedInterval (-4551821722 / 1000000000000) (-4551818664 / 1000000000000)
      | 7 => orderedInterval (1469611262 / 1000000000000) (1469611294 / 1000000000000)
      | _ => orderedInterval (-1300266489 / 1000000000000) (-1300266450 / 1000000000000)
    | 2 =>
      match b.val with
      | 0 => orderedInterval (-6275635731 / 1000000000000) (-6275635215 / 1000000000000)
      | 1 => orderedInterval (10902985772 / 1000000000000) (10902985795 / 1000000000000)
      | 2 => orderedInterval (-397417021 / 1000000000000) (-397417003 / 1000000000000)
      | 3 => orderedInterval (-25098267419 / 1000000000000) (-25098261698 / 1000000000000)
      | 4 => orderedInterval (6550707347 / 1000000000000) (6550707379 / 1000000000000)
      | 5 => orderedInterval (-7393773446 / 1000000000000) (-7393773353 / 1000000000000)
      | 6 => orderedInterval (-10505296286 / 1000000000000) (-10505293140 / 1000000000000)
      | 7 => orderedInterval (-5897825412 / 1000000000000) (-5897825385 / 1000000000000)
      | _ => orderedInterval (4671225531 / 1000000000000) (4671225588 / 1000000000000)
    | 3 =>
      match b.val with
      | 0 => orderedInterval (38828357254 / 1000000000000) (38828357861 / 1000000000000)
      | 1 => orderedInterval (4440984508 / 1000000000000) (4440984537 / 1000000000000)
      | 2 => orderedInterval (-8716411990 / 1000000000000) (-8716411958 / 1000000000000)
      | 3 => orderedInterval (-82679981150 / 1000000000000) (-82679968118 / 1000000000000)
      | 4 => orderedInterval (28532016050 / 1000000000000) (28532016104 / 1000000000000)
      | 5 => orderedInterval (8826989698 / 1000000000000) (8826989833 / 1000000000000)
      | 6 => orderedInterval (4632971868 / 1000000000000) (4632975073 / 1000000000000)
      | 7 => orderedInterval (-733057081 / 1000000000000) (-733057056 / 1000000000000)
      | _ => orderedInterval (-4833949930 / 1000000000000) (-4833949843 / 1000000000000)
    | _ =>
      match b.val with
      | 0 => orderedInterval (7067079244 / 1000000000000) (7067079967 / 1000000000000)
      | 1 => orderedInterval (-26658342894 / 1000000000000) (-26658342850 / 1000000000000)
      | 2 => orderedInterval (2027226370 / 1000000000000) (2027226427 / 1000000000000)
      | 3 => orderedInterval (143999937574 / 1000000000000) (143999967464 / 1000000000000)
      | 4 => orderedInterval (-14938387538 / 1000000000000) (-14938387444 / 1000000000000)
      | 5 => orderedInterval (11341513890 / 1000000000000) (11341514091 / 1000000000000)
      | 6 => orderedInterval (11125927654 / 1000000000000) (11125930956 / 1000000000000)
      | 7 => orderedInterval (7420048071 / 1000000000000) (7420048094 / 1000000000000)
      | _ => orderedInterval (22020201309 / 1000000000000) (22020201448 / 1000000000000)
  coefficientTarget := fun i =>
    match i.val with
    | 0 => orderedInterval (13759673337 / 1000000000000) (13759678033 / 1000000000000)
    | 1 => orderedInterval (-31068676677 / 1000000000000) (-31068670481 / 1000000000000)
    | 2 => orderedInterval (-33443296665 / 1000000000000) (-33443287032 / 1000000000000)
    | 3 => orderedInterval (-11702080773 / 1000000000000) (-11702063567 / 1000000000000)
    | _ => orderedInterval (163405203680 / 1000000000000) (163405238153 / 1000000000000)

theorem compactCertificate215_stateChecks0 :
    compactCertificate215.stateChecks 0 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 31 12 (193 / 2)) (orderedInterval (8534401478 / 1000000000000) (8534401512 / 1000000000000), orderedInterval (-80817646471 / 1000000000000) (-80817646437 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 23 12 (284325852944893 / 4000000000000)) (orderedInterval (36113224312 / 1000000000000) (36113226048 / 1000000000000), orderedInterval (-87730821091 / 1000000000000) (-87730819355 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 37 12 (91945138999069 / 800000000000)) (orderedInterval (37186374071 / 1000000000000) (37186379828 / 1000000000000), orderedInterval (-64631356266 / 1000000000000) (-64631350509 / 1000000000000))) = true
  norm_num [besselStateAtRationalPoint, besselIntervalStepZero,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, besselZeroTransition,
    besselInitial, besselGridStateAt, besselGridStateBlock00, besselGridStateBlock01,
    besselGridStateBlock02, besselGridStateBlock03, besselGridStateBlock04,
    besselGridStateBlock05, besselGridStateBlock06, besselGridStateBlock07,
    besselGridStateBlock08, besselGridStateBlock09, besselGridStateBlock10,
    besselGridStateBlock11, besselGridStateBlock12, besselGridStateBlock13,
    besselGridStateBlock14, besselGridState007, besselGridState009, besselGridState014, besselGridState017, besselGridState018, besselGridState023, besselGridState024, besselGridState027, besselGridState031, besselGridState033, besselGridState035, besselGridState037, besselGridState038, besselGridState039, besselGridState040, besselGridState044, besselGridState045, besselGridState047, besselGridState048, besselGridState053, besselGridState057, besselGridState061, besselGridState066, besselGridState069, besselGridState070, besselStateSubset, linearInterval, widenInterval,
    rationalErrorInterval, rationalIntervalSubset, orderedInterval, Finset.sum_range_succ,
    IntervalRat.add, IntervalRat.mul, IntervalRat.scale, IntervalRat.singleton]

theorem compactCertificate215_stateChecks1 :
    compactCertificate215.stateChecks 3 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 7 12 (82965574770551 / 4000000000000)) (orderedInterval (79390542472 / 1000000000000) (79390547660 / 1000000000000), orderedInterval (-158103558079 / 1000000000000) (-158103552892 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 18 12 (222857203907147 / 4000000000000)) (orderedInterval (-5471778236 / 1000000000000) (-5471778215 / 1000000000000), orderedInterval (106805941069 / 1000000000000) (106805941089 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 48 12 (605100660507999 / 4000000000000)) (orderedInterval (61828615662 / 1000000000000) (61828615663 / 1000000000000), orderedInterval (19431317445 / 1000000000000) (19431317446 / 1000000000000))) = true
  norm_num [besselStateAtRationalPoint, besselIntervalStepZero,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, besselZeroTransition,
    besselInitial, besselGridStateAt, besselGridStateBlock00, besselGridStateBlock01,
    besselGridStateBlock02, besselGridStateBlock03, besselGridStateBlock04,
    besselGridStateBlock05, besselGridStateBlock06, besselGridStateBlock07,
    besselGridStateBlock08, besselGridStateBlock09, besselGridStateBlock10,
    besselGridStateBlock11, besselGridStateBlock12, besselGridStateBlock13,
    besselGridStateBlock14, besselGridState007, besselGridState009, besselGridState014, besselGridState017, besselGridState018, besselGridState023, besselGridState024, besselGridState027, besselGridState031, besselGridState033, besselGridState035, besselGridState037, besselGridState038, besselGridState039, besselGridState040, besselGridState044, besselGridState045, besselGridState047, besselGridState048, besselGridState053, besselGridState057, besselGridState061, besselGridState066, besselGridState069, besselGridState070, besselStateSubset, linearInterval, widenInterval,
    rationalErrorInterval, rationalIntervalSubset, orderedInterval, Finset.sum_range_succ,
    IntervalRat.add, IntervalRat.mul, IntervalRat.scale, IntervalRat.singleton]

theorem compactCertificate215_stateChecks2 :
    compactCertificate215.stateChecks 6 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 35 12 (445714407814487 / 4000000000000)) (orderedInterval (-58470936937 / 1000000000000) (-58470857030 / 1000000000000), orderedInterval (48162170069 / 1000000000000) (48162249975 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 61 12 (763739234748851 / 4000000000000)) (orderedInterval (-4752630726 / 1000000000000) (-4752630725 / 1000000000000), orderedInterval (-57534488420 / 1000000000000) (-57534488418 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 45 12 (562566863594009 / 4000000000000)) (orderedInterval (-3668662868 / 1000000000000) (-3668662865 / 1000000000000), orderedInterval (-67166606432 / 1000000000000) (-67166606429 / 1000000000000))) = true
  norm_num [besselStateAtRationalPoint, besselIntervalStepZero,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, besselZeroTransition,
    besselInitial, besselGridStateAt, besselGridStateBlock00, besselGridStateBlock01,
    besselGridStateBlock02, besselGridStateBlock03, besselGridStateBlock04,
    besselGridStateBlock05, besselGridStateBlock06, besselGridStateBlock07,
    besselGridStateBlock08, besselGridStateBlock09, besselGridStateBlock10,
    besselGridStateBlock11, besselGridStateBlock12, besselGridStateBlock13,
    besselGridStateBlock14, besselGridState007, besselGridState009, besselGridState014, besselGridState017, besselGridState018, besselGridState023, besselGridState024, besselGridState027, besselGridState031, besselGridState033, besselGridState035, besselGridState037, besselGridState038, besselGridState039, besselGridState040, besselGridState044, besselGridState045, besselGridState047, besselGridState048, besselGridState053, besselGridState057, besselGridState061, besselGridState066, besselGridState069, besselGridState070, besselStateSubset, linearInterval, widenInterval,
    rationalErrorInterval, rationalIntervalSubset, orderedInterval, Finset.sum_range_succ,
    IntervalRat.add, IntervalRat.mul, IntervalRat.scale, IntervalRat.singleton]

theorem compactCertificate215_stateChecks3 :
    compactCertificate215.stateChecks 9 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 69 12 (863122239314807 / 4000000000000)) (orderedInterval (11031269243 / 1000000000000) (11031269305 / 1000000000000), orderedInterval (-53210422077 / 1000000000000) (-53210422016 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 40 12 (498323857211903 / 4000000000000)) (orderedInterval (-21012228117 / 1000000000000) (-21012227705 / 1000000000000), orderedInterval (68411549904 / 1000000000000) (68411550316 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 70 12 (884284429370827 / 4000000000000)) (orderedInterval (49959993961 / 1000000000000) (49960001225 / 1000000000000), orderedInterval (-19701237698 / 1000000000000) (-19701230434 / 1000000000000))) = true
  norm_num [besselStateAtRationalPoint, besselIntervalStepZero,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, besselZeroTransition,
    besselInitial, besselGridStateAt, besselGridStateBlock00, besselGridStateBlock01,
    besselGridStateBlock02, besselGridStateBlock03, besselGridStateBlock04,
    besselGridStateBlock05, besselGridStateBlock06, besselGridStateBlock07,
    besselGridStateBlock08, besselGridStateBlock09, besselGridStateBlock10,
    besselGridStateBlock11, besselGridStateBlock12, besselGridStateBlock13,
    besselGridStateBlock14, besselGridState007, besselGridState009, besselGridState014, besselGridState017, besselGridState018, besselGridState023, besselGridState024, besselGridState027, besselGridState031, besselGridState033, besselGridState035, besselGridState037, besselGridState038, besselGridState039, besselGridState040, besselGridState044, besselGridState045, besselGridState047, besselGridState048, besselGridState053, besselGridState057, besselGridState061, besselGridState066, besselGridState069, besselGridState070, besselStateSubset, linearInterval, widenInterval,
    rationalErrorInterval, rationalIntervalSubset, orderedInterval, Finset.sum_range_succ,
    IntervalRat.add, IntervalRat.mul, IntervalRat.scale, IntervalRat.singleton]

theorem compactCertificate215_stateChecks4 :
    compactCertificate215.stateChecks 12 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 66 12 (826213220277463 / 4000000000000)) (orderedInterval (-389560970 / 1000000000000) (-389560967 / 1000000000000), orderedInterval (55516401517 / 1000000000000) (55516401521 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 47 12 (589624739417479 / 4000000000000)) (orderedInterval (-33555228534 / 1000000000000) (-33555228533 / 1000000000000), orderedInterval (-56391683854 / 1000000000000) (-56391683853 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 53 12 (668571611721441 / 4000000000000)) (orderedInterval (-61044094340 / 1000000000000) (-61044094334 / 1000000000000), orderedInterval (-8896897994 / 1000000000000) (-8896897989 / 1000000000000))) = true
  norm_num [besselStateAtRationalPoint, besselIntervalStepZero,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, besselZeroTransition,
    besselInitial, besselGridStateAt, besselGridStateBlock00, besselGridStateBlock01,
    besselGridStateBlock02, besselGridStateBlock03, besselGridStateBlock04,
    besselGridStateBlock05, besselGridStateBlock06, besselGridStateBlock07,
    besselGridStateBlock08, besselGridStateBlock09, besselGridStateBlock10,
    besselGridStateBlock11, besselGridStateBlock12, besselGridStateBlock13,
    besselGridStateBlock14, besselGridState007, besselGridState009, besselGridState014, besselGridState017, besselGridState018, besselGridState023, besselGridState024, besselGridState027, besselGridState031, besselGridState033, besselGridState035, besselGridState037, besselGridState038, besselGridState039, besselGridState040, besselGridState044, besselGridState045, besselGridState047, besselGridState048, besselGridState053, besselGridState057, besselGridState061, besselGridState066, besselGridState069, besselGridState070, besselStateSubset, linearInterval, widenInterval,
    rationalErrorInterval, rationalIntervalSubset, orderedInterval, Finset.sum_range_succ,
    IntervalRat.add, IntervalRat.mul, IntervalRat.scale, IntervalRat.singleton]

theorem compactCertificate215_stateChecks5 :
    compactCertificate215.stateChecks 15 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 44 12 (557385307758929 / 4000000000000)) (orderedInterval (63945230871 / 1000000000000) (63945233832 / 1000000000000), orderedInterval (-22129203515 / 1000000000000) (-22129200553 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 39 12 (492466823205509 / 4000000000000)) (orderedInterval (-70589529258 / 1000000000000) (-70589529255 / 1000000000000), orderedInterval (-13422560429 / 1000000000000) (-13422560426 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 57 12 (142736080181391 / 800000000000)) (orderedInterval (-7981324431 / 1000000000000) (-7981324430 / 1000000000000), orderedInterval (-59175660818 / 1000000000000) (-59175660817 / 1000000000000))) = true
  norm_num [besselStateAtRationalPoint, besselIntervalStepZero,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, besselZeroTransition,
    besselInitial, besselGridStateAt, besselGridStateBlock00, besselGridStateBlock01,
    besselGridStateBlock02, besselGridStateBlock03, besselGridStateBlock04,
    besselGridStateBlock05, besselGridStateBlock06, besselGridStateBlock07,
    besselGridStateBlock08, besselGridStateBlock09, besselGridStateBlock10,
    besselGridStateBlock11, besselGridStateBlock12, besselGridStateBlock13,
    besselGridStateBlock14, besselGridState007, besselGridState009, besselGridState014, besselGridState017, besselGridState018, besselGridState023, besselGridState024, besselGridState027, besselGridState031, besselGridState033, besselGridState035, besselGridState037, besselGridState038, besselGridState039, besselGridState040, besselGridState044, besselGridState045, besselGridState047, besselGridState048, besselGridState053, besselGridState057, besselGridState061, besselGridState066, besselGridState069, besselGridState070, besselStateSubset, linearInterval, widenInterval,
    rationalErrorInterval, rationalIntervalSubset, orderedInterval, Finset.sum_range_succ,
    IntervalRat.add, IntervalRat.mul, IntervalRat.scale, IntervalRat.singleton]

theorem compactCertificate215_stateChecks6 :
    compactCertificate215.stateChecks 18 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 31 12 (394815509570077 / 4000000000000)) (orderedInterval (-69379639062 / 1000000000000) (-69379620913 / 1000000000000), orderedInterval (40801664601 / 1000000000000) (40801682750 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 27 12 (334689479924597 / 4000000000000)) (orderedInterval (31275895169 / 1000000000000) (31275896383 / 1000000000000), orderedInterval (-81614168416 / 1000000000000) (-81614167202 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 17 12 (209433136405991 / 4000000000000)) (orderedInterval (28962383929 / 1000000000000) (28962384355 / 1000000000000), orderedInterval (-106674721165 / 1000000000000) (-106674720739 / 1000000000000))) = true
  norm_num [besselStateAtRationalPoint, besselIntervalStepZero,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, besselZeroTransition,
    besselInitial, besselGridStateAt, besselGridStateBlock00, besselGridStateBlock01,
    besselGridStateBlock02, besselGridStateBlock03, besselGridStateBlock04,
    besselGridStateBlock05, besselGridStateBlock06, besselGridStateBlock07,
    besselGridStateBlock08, besselGridStateBlock09, besselGridStateBlock10,
    besselGridStateBlock11, besselGridStateBlock12, besselGridStateBlock13,
    besselGridStateBlock14, besselGridState007, besselGridState009, besselGridState014, besselGridState017, besselGridState018, besselGridState023, besselGridState024, besselGridState027, besselGridState031, besselGridState033, besselGridState035, besselGridState037, besselGridState038, besselGridState039, besselGridState040, besselGridState044, besselGridState045, besselGridState047, besselGridState048, besselGridState053, besselGridState057, besselGridState061, besselGridState066, besselGridState069, besselGridState070, besselStateSubset, linearInterval, widenInterval,
    rationalErrorInterval, rationalIntervalSubset, orderedInterval, Finset.sum_range_succ,
    IntervalRat.add, IntervalRat.mul, IntervalRat.scale, IntervalRat.singleton]

theorem compactCertificate215_stateChecks7 :
    compactCertificate215.stateChecks 21 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 9 12 (112633837302297 / 4000000000000)) (orderedInterval (-92784751829 / 1000000000000) (-92784751828 / 1000000000000), orderedInterval (-116675880265 / 1000000000000) (-116675880264 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 24 12 (305822778677891 / 4000000000000)) (orderedInterval (87932943438 / 1000000000000) (87932944493 / 1000000000000), orderedInterval (-24953185588 / 1000000000000) (-24953184533 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 33 12 (417574858691107 / 4000000000000)) (orderedInterval (-77923754033 / 1000000000000) (-77923754020 / 1000000000000), orderedInterval (-4733342829 / 1000000000000) (-4733342816 / 1000000000000))) = true
  norm_num [besselStateAtRationalPoint, besselIntervalStepZero,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, besselZeroTransition,
    besselInitial, besselGridStateAt, besselGridStateBlock00, besselGridStateBlock01,
    besselGridStateBlock02, besselGridStateBlock03, besselGridStateBlock04,
    besselGridStateBlock05, besselGridStateBlock06, besselGridStateBlock07,
    besselGridStateBlock08, besselGridStateBlock09, besselGridStateBlock10,
    besselGridStateBlock11, besselGridStateBlock12, besselGridStateBlock13,
    besselGridStateBlock14, besselGridState007, besselGridState009, besselGridState014, besselGridState017, besselGridState018, besselGridState023, besselGridState024, besselGridState027, besselGridState031, besselGridState033, besselGridState035, besselGridState037, besselGridState038, besselGridState039, besselGridState040, besselGridState044, besselGridState045, besselGridState047, besselGridState048, besselGridState053, besselGridState057, besselGridState061, besselGridState066, besselGridState069, besselGridState070, besselStateSubset, linearInterval, widenInterval,
    rationalErrorInterval, rationalIntervalSubset, orderedInterval, Finset.sum_range_succ,
    IntervalRat.add, IntervalRat.mul, IntervalRat.scale, IntervalRat.singleton]

theorem compactCertificate215_stateChecks8 :
    compactCertificate215.stateChecks 24 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 14 12 (176566863594009 / 4000000000000)) (orderedInterval (97118929104 / 1000000000000) (97118929105 / 1000000000000), orderedInterval (69538638844 / 1000000000000) (69538638845 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 57 12 (717734497810489 / 4000000000000)) (orderedInterval (-54308399396 / 1000000000000) (-54308399395 / 1000000000000), orderedInterval (-24313517506 / 1000000000000) (-24313517505 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 38 12 (479413381804151 / 4000000000000)) (orderedInterval (69325968147 / 1000000000000) (69325968148 / 1000000000000), orderedInterval (22194764991 / 1000000000000) (22194764992 / 1000000000000))) = true
  norm_num [besselStateAtRationalPoint, besselIntervalStepZero,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, besselZeroTransition,
    besselInitial, besselGridStateAt, besselGridStateBlock00, besselGridStateBlock01,
    besselGridStateBlock02, besselGridStateBlock03, besselGridStateBlock04,
    besselGridStateBlock05, besselGridStateBlock06, besselGridStateBlock07,
    besselGridStateBlock08, besselGridStateBlock09, besselGridStateBlock10,
    besselGridStateBlock11, besselGridStateBlock12, besselGridStateBlock13,
    besselGridStateBlock14, besselGridState007, besselGridState009, besselGridState014, besselGridState017, besselGridState018, besselGridState023, besselGridState024, besselGridState027, besselGridState031, besselGridState033, besselGridState035, besselGridState037, besselGridState038, besselGridState039, besselGridState040, besselGridState044, besselGridState045, besselGridState047, besselGridState048, besselGridState053, besselGridState057, besselGridState061, besselGridState066, besselGridState069, besselGridState070, besselStateSubset, linearInterval, widenInterval,
    rationalErrorInterval, rationalIntervalSubset, orderedInterval, Finset.sum_range_succ,
    IntervalRat.add, IntervalRat.mul, IntervalRat.scale, IntervalRat.singleton]

theorem compactCertificate215_states : ∀ j,
    BesselStateValid (compactCertificate215.point j) (compactCertificate215.state j) :=
  compactCertificate215.statesValid_of_checks3 compactCertificate215_stateChecks0
    compactCertificate215_stateChecks1 compactCertificate215_stateChecks2
    compactCertificate215_stateChecks3 compactCertificate215_stateChecks4
    compactCertificate215_stateChecks5 compactCertificate215_stateChecks6
    compactCertificate215_stateChecks7 compactCertificate215_stateChecks8

theorem compactCertificate215_chunkChecks0_0 :
    compactCertificate215.chunkChecks (0 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 0) <| besselDerivativeNearFromState (193 / 2) 0 (IntervalRat.scale (193 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (8534401478 / 1000000000000) (8534401512 / 1000000000000), orderedInterval (-80817646471 / 1000000000000) (-80817646437 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 0) <| besselDerivativeNearFromState (284325852944893 / 4000000000000) 0 (IntervalRat.scale (193 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (36113224312 / 1000000000000) (36113226048 / 1000000000000), orderedInterval (-87730821091 / 1000000000000) (-87730819355 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 0) <| besselDerivativeNearFromState (91945138999069 / 800000000000) 0 (IntervalRat.scale (193 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (37186374071 / 1000000000000) (37186379828 / 1000000000000), orderedInterval (-64631356266 / 1000000000000) (-64631350509 / 1000000000000)))) (orderedInterval (5901381992 / 1000000000000) (5901382367 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 0) <| besselDerivativeNearFromState (82965574770551 / 4000000000000) 0 (IntervalRat.scale (193 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (79390542472 / 1000000000000) (79390547660 / 1000000000000), orderedInterval (-158103558079 / 1000000000000) (-158103552892 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 0) <| besselDerivativeNearFromState (222857203907147 / 4000000000000) 0 (IntervalRat.scale (193 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-5471778236 / 1000000000000) (-5471778215 / 1000000000000), orderedInterval (106805941069 / 1000000000000) (106805941089 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 0) <| besselDerivativeNearFromState (605100660507999 / 4000000000000) 0 (IntervalRat.scale (193 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (61828615662 / 1000000000000) (61828615663 / 1000000000000), orderedInterval (19431317445 / 1000000000000) (19431317446 / 1000000000000)))) (orderedInterval (-5456489429 / 1000000000000) (-5456489359 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 0) <| besselDerivativeNearFromState (445714407814487 / 4000000000000) 0 (IntervalRat.scale (193 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-58470936937 / 1000000000000) (-58470857030 / 1000000000000), orderedInterval (48162170069 / 1000000000000) (48162249975 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 0) <| besselDerivativeNearFromState (763739234748851 / 4000000000000) 0 (IntervalRat.scale (193 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-4752630726 / 1000000000000) (-4752630725 / 1000000000000), orderedInterval (-57534488420 / 1000000000000) (-57534488418 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 0) <| besselDerivativeNearFromState (562566863594009 / 4000000000000) 0 (IntervalRat.scale (193 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-3668662868 / 1000000000000) (-3668662865 / 1000000000000), orderedInterval (-67166606432 / 1000000000000) (-67166606429 / 1000000000000)))) (orderedInterval (57925800 / 1000000000000) (57925807 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate215_chunkChecks0_1 :
    compactCertificate215.chunkChecks (0 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 0) <| besselDerivativeNearFromState (863122239314807 / 4000000000000) 0 (IntervalRat.scale (193 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (11031269243 / 1000000000000) (11031269305 / 1000000000000), orderedInterval (-53210422077 / 1000000000000) (-53210422016 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 0) <| besselDerivativeNearFromState (498323857211903 / 4000000000000) 0 (IntervalRat.scale (193 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-21012228117 / 1000000000000) (-21012227705 / 1000000000000), orderedInterval (68411549904 / 1000000000000) (68411550316 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 0) <| besselDerivativeNearFromState (884284429370827 / 4000000000000) 0 (IntervalRat.scale (193 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (49959993961 / 1000000000000) (49960001225 / 1000000000000), orderedInterval (-19701237698 / 1000000000000) (-19701230434 / 1000000000000)))) (orderedInterval (3585150929 / 1000000000000) (3585152042 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 0) <| besselDerivativeNearFromState (826213220277463 / 4000000000000) 0 (IntervalRat.scale (193 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-389560970 / 1000000000000) (-389560967 / 1000000000000), orderedInterval (55516401517 / 1000000000000) (55516401521 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 0) <| besselDerivativeNearFromState (589624739417479 / 4000000000000) 0 (IntervalRat.scale (193 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-33555228534 / 1000000000000) (-33555228533 / 1000000000000), orderedInterval (-56391683854 / 1000000000000) (-56391683853 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 0) <| besselDerivativeNearFromState (668571611721441 / 4000000000000) 0 (IntervalRat.scale (193 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-61044094340 / 1000000000000) (-61044094334 / 1000000000000), orderedInterval (-8896897994 / 1000000000000) (-8896897989 / 1000000000000)))) (orderedInterval (-2857127529 / 1000000000000) (-2857127517 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 0) <| besselDerivativeNearFromState (557385307758929 / 4000000000000) 0 (IntervalRat.scale (193 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (63945230871 / 1000000000000) (63945233832 / 1000000000000), orderedInterval (-22129203515 / 1000000000000) (-22129200553 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 0) <| besselDerivativeNearFromState (492466823205509 / 4000000000000) 0 (IntervalRat.scale (193 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-70589529258 / 1000000000000) (-70589529255 / 1000000000000), orderedInterval (-13422560429 / 1000000000000) (-13422560426 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 0) <| besselDerivativeNearFromState (142736080181391 / 800000000000) 0 (IntervalRat.scale (193 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-7981324431 / 1000000000000) (-7981324430 / 1000000000000), orderedInterval (-59175660818 / 1000000000000) (-59175660817 / 1000000000000)))) (orderedInterval (4573669178 / 1000000000000) (4573669222 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate215_chunkChecks0_2 :
    compactCertificate215.chunkChecks (0 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 0) <| besselDerivativeNearFromState (394815509570077 / 4000000000000) 0 (IntervalRat.scale (193 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-69379639062 / 1000000000000) (-69379620913 / 1000000000000), orderedInterval (40801664601 / 1000000000000) (40801682750 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 0) <| besselDerivativeNearFromState (334689479924597 / 4000000000000) 0 (IntervalRat.scale (193 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (31275895169 / 1000000000000) (31275896383 / 1000000000000), orderedInterval (-81614168416 / 1000000000000) (-81614167202 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 0) <| besselDerivativeNearFromState (209433136405991 / 4000000000000) 0 (IntervalRat.scale (193 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (28962383929 / 1000000000000) (28962384355 / 1000000000000), orderedInterval (-106674721165 / 1000000000000) (-106674720739 / 1000000000000)))) (orderedInterval (10265940899 / 1000000000000) (10265943908 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 0) <| besselDerivativeNearFromState (112633837302297 / 4000000000000) 0 (IntervalRat.scale (193 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-92784751829 / 1000000000000) (-92784751828 / 1000000000000), orderedInterval (-116675880265 / 1000000000000) (-116675880264 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 0) <| besselDerivativeNearFromState (305822778677891 / 4000000000000) 0 (IntervalRat.scale (193 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (87932943438 / 1000000000000) (87932944493 / 1000000000000), orderedInterval (-24953185588 / 1000000000000) (-24953184533 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 0) <| besselDerivativeNearFromState (417574858691107 / 4000000000000) 0 (IntervalRat.scale (193 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-77923754033 / 1000000000000) (-77923754020 / 1000000000000), orderedInterval (-4733342829 / 1000000000000) (-4733342816 / 1000000000000)))) (orderedInterval (5690347169 / 1000000000000) (5690347207 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 0) <| besselDerivativeNearFromState (176566863594009 / 4000000000000) 0 (IntervalRat.scale (193 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (97118929104 / 1000000000000) (97118929105 / 1000000000000), orderedInterval (69538638844 / 1000000000000) (69538638845 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 0) <| besselDerivativeNearFromState (717734497810489 / 4000000000000) 0 (IntervalRat.scale (193 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-54308399396 / 1000000000000) (-54308399395 / 1000000000000), orderedInterval (-24313517506 / 1000000000000) (-24313517505 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 0) <| besselDerivativeNearFromState (479413381804151 / 4000000000000) 0 (IntervalRat.scale (193 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (69325968147 / 1000000000000) (69325968148 / 1000000000000), orderedInterval (22194764991 / 1000000000000) (22194764992 / 1000000000000)))) (orderedInterval (-8001125672 / 1000000000000) (-8001125644 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate215_chunkChecks0 :
    compactCertificate215.chunkChecks (0 : Fin 5) 0 9 = true :=
  compactCertificate215.chunkChecks_nine_of_three (0 : Fin 5) compactCertificate215_chunkChecks0_0
    compactCertificate215_chunkChecks0_1 compactCertificate215_chunkChecks0_2

theorem compactCertificate215_chunkChecks1_0 :
    compactCertificate215.chunkChecks (1 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 1) <| besselDerivativeNearFromState (193 / 2) 1 (IntervalRat.scale (193 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (8534401478 / 1000000000000) (8534401512 / 1000000000000), orderedInterval (-80817646471 / 1000000000000) (-80817646437 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 1) <| besselDerivativeNearFromState (284325852944893 / 4000000000000) 1 (IntervalRat.scale (193 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (36113224312 / 1000000000000) (36113226048 / 1000000000000), orderedInterval (-87730821091 / 1000000000000) (-87730819355 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 1) <| besselDerivativeNearFromState (91945138999069 / 800000000000) 1 (IntervalRat.scale (193 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (37186374071 / 1000000000000) (37186379828 / 1000000000000), orderedInterval (-64631356266 / 1000000000000) (-64631350509 / 1000000000000)))) (orderedInterval (-37152471954 / 1000000000000) (-37152471518 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 1) <| besselDerivativeNearFromState (82965574770551 / 4000000000000) 1 (IntervalRat.scale (193 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (79390542472 / 1000000000000) (79390547660 / 1000000000000), orderedInterval (-158103558079 / 1000000000000) (-158103552892 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 1) <| besselDerivativeNearFromState (222857203907147 / 4000000000000) 1 (IntervalRat.scale (193 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-5471778236 / 1000000000000) (-5471778215 / 1000000000000), orderedInterval (106805941069 / 1000000000000) (106805941089 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 1) <| besselDerivativeNearFromState (605100660507999 / 4000000000000) 1 (IntervalRat.scale (193 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (61828615662 / 1000000000000) (61828615663 / 1000000000000), orderedInterval (19431317445 / 1000000000000) (19431317446 / 1000000000000)))) (orderedInterval (454706103 / 1000000000000) (454706130 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 1) <| besselDerivativeNearFromState (445714407814487 / 4000000000000) 1 (IntervalRat.scale (193 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-58470936937 / 1000000000000) (-58470857030 / 1000000000000), orderedInterval (48162170069 / 1000000000000) (48162249975 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 1) <| besselDerivativeNearFromState (763739234748851 / 4000000000000) 1 (IntervalRat.scale (193 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-4752630726 / 1000000000000) (-4752630725 / 1000000000000), orderedInterval (-57534488420 / 1000000000000) (-57534488418 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 1) <| besselDerivativeNearFromState (562566863594009 / 4000000000000) 1 (IntervalRat.scale (193 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-3668662868 / 1000000000000) (-3668662865 / 1000000000000), orderedInterval (-67166606432 / 1000000000000) (-67166606429 / 1000000000000)))) (orderedInterval (1145391018 / 1000000000000) (1145391028 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate215_chunkChecks1_1 :
    compactCertificate215.chunkChecks (1 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 1) <| besselDerivativeNearFromState (863122239314807 / 4000000000000) 1 (IntervalRat.scale (193 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (11031269243 / 1000000000000) (11031269305 / 1000000000000), orderedInterval (-53210422077 / 1000000000000) (-53210422016 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 1) <| besselDerivativeNearFromState (498323857211903 / 4000000000000) 1 (IntervalRat.scale (193 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-21012228117 / 1000000000000) (-21012227705 / 1000000000000), orderedInterval (68411549904 / 1000000000000) (68411550316 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 1) <| besselDerivativeNearFromState (884284429370827 / 4000000000000) 1 (IntervalRat.scale (193 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (49959993961 / 1000000000000) (49960001225 / 1000000000000), orderedInterval (-19701237698 / 1000000000000) (-19701230434 / 1000000000000)))) (orderedInterval (21269411546 / 1000000000000) (21269414056 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 1) <| besselDerivativeNearFromState (826213220277463 / 4000000000000) 1 (IntervalRat.scale (193 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-389560970 / 1000000000000) (-389560967 / 1000000000000), orderedInterval (55516401517 / 1000000000000) (55516401521 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 1) <| besselDerivativeNearFromState (589624739417479 / 4000000000000) 1 (IntervalRat.scale (193 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-33555228534 / 1000000000000) (-33555228533 / 1000000000000), orderedInterval (-56391683854 / 1000000000000) (-56391683853 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 1) <| besselDerivativeNearFromState (668571611721441 / 4000000000000) 1 (IntervalRat.scale (193 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-61044094340 / 1000000000000) (-61044094334 / 1000000000000), orderedInterval (-8896897994 / 1000000000000) (-8896897989 / 1000000000000)))) (orderedInterval (-10212884376 / 1000000000000) (-10212884356 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 1) <| besselDerivativeNearFromState (557385307758929 / 4000000000000) 1 (IntervalRat.scale (193 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (63945230871 / 1000000000000) (63945233832 / 1000000000000), orderedInterval (-22129203515 / 1000000000000) (-22129200553 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 1) <| besselDerivativeNearFromState (492466823205509 / 4000000000000) 1 (IntervalRat.scale (193 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-70589529258 / 1000000000000) (-70589529255 / 1000000000000), orderedInterval (-13422560429 / 1000000000000) (-13422560426 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 1) <| besselDerivativeNearFromState (142736080181391 / 800000000000) 1 (IntervalRat.scale (193 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-7981324431 / 1000000000000) (-7981324430 / 1000000000000), orderedInterval (-59175660818 / 1000000000000) (-59175660817 / 1000000000000)))) (orderedInterval (-2190352065 / 1000000000000) (-2190352001 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate215_chunkChecks1_2 :
    compactCertificate215.chunkChecks (1 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 1) <| besselDerivativeNearFromState (394815509570077 / 4000000000000) 1 (IntervalRat.scale (193 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-69379639062 / 1000000000000) (-69379620913 / 1000000000000), orderedInterval (40801664601 / 1000000000000) (40801682750 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 1) <| besselDerivativeNearFromState (334689479924597 / 4000000000000) 1 (IntervalRat.scale (193 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (31275895169 / 1000000000000) (31275896383 / 1000000000000), orderedInterval (-81614168416 / 1000000000000) (-81614167202 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 1) <| besselDerivativeNearFromState (209433136405991 / 4000000000000) 1 (IntervalRat.scale (193 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (28962383929 / 1000000000000) (28962384355 / 1000000000000), orderedInterval (-106674721165 / 1000000000000) (-106674720739 / 1000000000000)))) (orderedInterval (-4551821722 / 1000000000000) (-4551818664 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 1) <| besselDerivativeNearFromState (112633837302297 / 4000000000000) 1 (IntervalRat.scale (193 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-92784751829 / 1000000000000) (-92784751828 / 1000000000000), orderedInterval (-116675880265 / 1000000000000) (-116675880264 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 1) <| besselDerivativeNearFromState (305822778677891 / 4000000000000) 1 (IntervalRat.scale (193 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (87932943438 / 1000000000000) (87932944493 / 1000000000000), orderedInterval (-24953185588 / 1000000000000) (-24953184533 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 1) <| besselDerivativeNearFromState (417574858691107 / 4000000000000) 1 (IntervalRat.scale (193 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-77923754033 / 1000000000000) (-77923754020 / 1000000000000), orderedInterval (-4733342829 / 1000000000000) (-4733342816 / 1000000000000)))) (orderedInterval (1469611262 / 1000000000000) (1469611294 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 1) <| besselDerivativeNearFromState (176566863594009 / 4000000000000) 1 (IntervalRat.scale (193 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (97118929104 / 1000000000000) (97118929105 / 1000000000000), orderedInterval (69538638844 / 1000000000000) (69538638845 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 1) <| besselDerivativeNearFromState (717734497810489 / 4000000000000) 1 (IntervalRat.scale (193 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-54308399396 / 1000000000000) (-54308399395 / 1000000000000), orderedInterval (-24313517506 / 1000000000000) (-24313517505 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 1) <| besselDerivativeNearFromState (479413381804151 / 4000000000000) 1 (IntervalRat.scale (193 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (69325968147 / 1000000000000) (69325968148 / 1000000000000), orderedInterval (22194764991 / 1000000000000) (22194764992 / 1000000000000)))) (orderedInterval (-1300266489 / 1000000000000) (-1300266450 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate215_chunkChecks1 :
    compactCertificate215.chunkChecks (1 : Fin 5) 0 9 = true :=
  compactCertificate215.chunkChecks_nine_of_three (1 : Fin 5) compactCertificate215_chunkChecks1_0
    compactCertificate215_chunkChecks1_1 compactCertificate215_chunkChecks1_2

theorem compactCertificate215_chunkChecks2_0 :
    compactCertificate215.chunkChecks (2 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 2) <| besselDerivativeNearFromState (193 / 2) 2 (IntervalRat.scale (193 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (8534401478 / 1000000000000) (8534401512 / 1000000000000), orderedInterval (-80817646471 / 1000000000000) (-80817646437 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 2) <| besselDerivativeNearFromState (284325852944893 / 4000000000000) 2 (IntervalRat.scale (193 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (36113224312 / 1000000000000) (36113226048 / 1000000000000), orderedInterval (-87730821091 / 1000000000000) (-87730819355 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 2) <| besselDerivativeNearFromState (91945138999069 / 800000000000) 2 (IntervalRat.scale (193 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (37186374071 / 1000000000000) (37186379828 / 1000000000000), orderedInterval (-64631356266 / 1000000000000) (-64631350509 / 1000000000000)))) (orderedInterval (-6275635731 / 1000000000000) (-6275635215 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 2) <| besselDerivativeNearFromState (82965574770551 / 4000000000000) 2 (IntervalRat.scale (193 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (79390542472 / 1000000000000) (79390547660 / 1000000000000), orderedInterval (-158103558079 / 1000000000000) (-158103552892 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 2) <| besselDerivativeNearFromState (222857203907147 / 4000000000000) 2 (IntervalRat.scale (193 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-5471778236 / 1000000000000) (-5471778215 / 1000000000000), orderedInterval (106805941069 / 1000000000000) (106805941089 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 2) <| besselDerivativeNearFromState (605100660507999 / 4000000000000) 2 (IntervalRat.scale (193 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (61828615662 / 1000000000000) (61828615663 / 1000000000000), orderedInterval (19431317445 / 1000000000000) (19431317446 / 1000000000000)))) (orderedInterval (10902985772 / 1000000000000) (10902985795 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 2) <| besselDerivativeNearFromState (445714407814487 / 4000000000000) 2 (IntervalRat.scale (193 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-58470936937 / 1000000000000) (-58470857030 / 1000000000000), orderedInterval (48162170069 / 1000000000000) (48162249975 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 2) <| besselDerivativeNearFromState (763739234748851 / 4000000000000) 2 (IntervalRat.scale (193 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-4752630726 / 1000000000000) (-4752630725 / 1000000000000), orderedInterval (-57534488420 / 1000000000000) (-57534488418 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 2) <| besselDerivativeNearFromState (562566863594009 / 4000000000000) 2 (IntervalRat.scale (193 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-3668662868 / 1000000000000) (-3668662865 / 1000000000000), orderedInterval (-67166606432 / 1000000000000) (-67166606429 / 1000000000000)))) (orderedInterval (-397417021 / 1000000000000) (-397417003 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate215_chunkChecks2_1 :
    compactCertificate215.chunkChecks (2 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 2) <| besselDerivativeNearFromState (863122239314807 / 4000000000000) 2 (IntervalRat.scale (193 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (11031269243 / 1000000000000) (11031269305 / 1000000000000), orderedInterval (-53210422077 / 1000000000000) (-53210422016 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 2) <| besselDerivativeNearFromState (498323857211903 / 4000000000000) 2 (IntervalRat.scale (193 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-21012228117 / 1000000000000) (-21012227705 / 1000000000000), orderedInterval (68411549904 / 1000000000000) (68411550316 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 2) <| besselDerivativeNearFromState (884284429370827 / 4000000000000) 2 (IntervalRat.scale (193 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (49959993961 / 1000000000000) (49960001225 / 1000000000000), orderedInterval (-19701237698 / 1000000000000) (-19701230434 / 1000000000000)))) (orderedInterval (-25098267419 / 1000000000000) (-25098261698 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 2) <| besselDerivativeNearFromState (826213220277463 / 4000000000000) 2 (IntervalRat.scale (193 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-389560970 / 1000000000000) (-389560967 / 1000000000000), orderedInterval (55516401517 / 1000000000000) (55516401521 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 2) <| besselDerivativeNearFromState (589624739417479 / 4000000000000) 2 (IntervalRat.scale (193 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-33555228534 / 1000000000000) (-33555228533 / 1000000000000), orderedInterval (-56391683854 / 1000000000000) (-56391683853 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 2) <| besselDerivativeNearFromState (668571611721441 / 4000000000000) 2 (IntervalRat.scale (193 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-61044094340 / 1000000000000) (-61044094334 / 1000000000000), orderedInterval (-8896897994 / 1000000000000) (-8896897989 / 1000000000000)))) (orderedInterval (6550707347 / 1000000000000) (6550707379 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 2) <| besselDerivativeNearFromState (557385307758929 / 4000000000000) 2 (IntervalRat.scale (193 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (63945230871 / 1000000000000) (63945233832 / 1000000000000), orderedInterval (-22129203515 / 1000000000000) (-22129200553 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 2) <| besselDerivativeNearFromState (492466823205509 / 4000000000000) 2 (IntervalRat.scale (193 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-70589529258 / 1000000000000) (-70589529255 / 1000000000000), orderedInterval (-13422560429 / 1000000000000) (-13422560426 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 2) <| besselDerivativeNearFromState (142736080181391 / 800000000000) 2 (IntervalRat.scale (193 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-7981324431 / 1000000000000) (-7981324430 / 1000000000000), orderedInterval (-59175660818 / 1000000000000) (-59175660817 / 1000000000000)))) (orderedInterval (-7393773446 / 1000000000000) (-7393773353 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate215_chunkChecks2_2 :
    compactCertificate215.chunkChecks (2 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 2) <| besselDerivativeNearFromState (394815509570077 / 4000000000000) 2 (IntervalRat.scale (193 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-69379639062 / 1000000000000) (-69379620913 / 1000000000000), orderedInterval (40801664601 / 1000000000000) (40801682750 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 2) <| besselDerivativeNearFromState (334689479924597 / 4000000000000) 2 (IntervalRat.scale (193 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (31275895169 / 1000000000000) (31275896383 / 1000000000000), orderedInterval (-81614168416 / 1000000000000) (-81614167202 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 2) <| besselDerivativeNearFromState (209433136405991 / 4000000000000) 2 (IntervalRat.scale (193 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (28962383929 / 1000000000000) (28962384355 / 1000000000000), orderedInterval (-106674721165 / 1000000000000) (-106674720739 / 1000000000000)))) (orderedInterval (-10505296286 / 1000000000000) (-10505293140 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 2) <| besselDerivativeNearFromState (112633837302297 / 4000000000000) 2 (IntervalRat.scale (193 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-92784751829 / 1000000000000) (-92784751828 / 1000000000000), orderedInterval (-116675880265 / 1000000000000) (-116675880264 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 2) <| besselDerivativeNearFromState (305822778677891 / 4000000000000) 2 (IntervalRat.scale (193 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (87932943438 / 1000000000000) (87932944493 / 1000000000000), orderedInterval (-24953185588 / 1000000000000) (-24953184533 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 2) <| besselDerivativeNearFromState (417574858691107 / 4000000000000) 2 (IntervalRat.scale (193 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-77923754033 / 1000000000000) (-77923754020 / 1000000000000), orderedInterval (-4733342829 / 1000000000000) (-4733342816 / 1000000000000)))) (orderedInterval (-5897825412 / 1000000000000) (-5897825385 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 2) <| besselDerivativeNearFromState (176566863594009 / 4000000000000) 2 (IntervalRat.scale (193 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (97118929104 / 1000000000000) (97118929105 / 1000000000000), orderedInterval (69538638844 / 1000000000000) (69538638845 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 2) <| besselDerivativeNearFromState (717734497810489 / 4000000000000) 2 (IntervalRat.scale (193 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-54308399396 / 1000000000000) (-54308399395 / 1000000000000), orderedInterval (-24313517506 / 1000000000000) (-24313517505 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 2) <| besselDerivativeNearFromState (479413381804151 / 4000000000000) 2 (IntervalRat.scale (193 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (69325968147 / 1000000000000) (69325968148 / 1000000000000), orderedInterval (22194764991 / 1000000000000) (22194764992 / 1000000000000)))) (orderedInterval (4671225531 / 1000000000000) (4671225588 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate215_chunkChecks2 :
    compactCertificate215.chunkChecks (2 : Fin 5) 0 9 = true :=
  compactCertificate215.chunkChecks_nine_of_three (2 : Fin 5) compactCertificate215_chunkChecks2_0
    compactCertificate215_chunkChecks2_1 compactCertificate215_chunkChecks2_2

theorem compactCertificate215_chunkChecks3_0 :
    compactCertificate215.chunkChecks (3 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 3) <| besselDerivativeNearFromState (193 / 2) 3 (IntervalRat.scale (193 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (8534401478 / 1000000000000) (8534401512 / 1000000000000), orderedInterval (-80817646471 / 1000000000000) (-80817646437 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 3) <| besselDerivativeNearFromState (284325852944893 / 4000000000000) 3 (IntervalRat.scale (193 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (36113224312 / 1000000000000) (36113226048 / 1000000000000), orderedInterval (-87730821091 / 1000000000000) (-87730819355 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 3) <| besselDerivativeNearFromState (91945138999069 / 800000000000) 3 (IntervalRat.scale (193 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (37186374071 / 1000000000000) (37186379828 / 1000000000000), orderedInterval (-64631356266 / 1000000000000) (-64631350509 / 1000000000000)))) (orderedInterval (38828357254 / 1000000000000) (38828357861 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 3) <| besselDerivativeNearFromState (82965574770551 / 4000000000000) 3 (IntervalRat.scale (193 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (79390542472 / 1000000000000) (79390547660 / 1000000000000), orderedInterval (-158103558079 / 1000000000000) (-158103552892 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 3) <| besselDerivativeNearFromState (222857203907147 / 4000000000000) 3 (IntervalRat.scale (193 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-5471778236 / 1000000000000) (-5471778215 / 1000000000000), orderedInterval (106805941069 / 1000000000000) (106805941089 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 3) <| besselDerivativeNearFromState (605100660507999 / 4000000000000) 3 (IntervalRat.scale (193 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (61828615662 / 1000000000000) (61828615663 / 1000000000000), orderedInterval (19431317445 / 1000000000000) (19431317446 / 1000000000000)))) (orderedInterval (4440984508 / 1000000000000) (4440984537 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 3) <| besselDerivativeNearFromState (445714407814487 / 4000000000000) 3 (IntervalRat.scale (193 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-58470936937 / 1000000000000) (-58470857030 / 1000000000000), orderedInterval (48162170069 / 1000000000000) (48162249975 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 3) <| besselDerivativeNearFromState (763739234748851 / 4000000000000) 3 (IntervalRat.scale (193 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-4752630726 / 1000000000000) (-4752630725 / 1000000000000), orderedInterval (-57534488420 / 1000000000000) (-57534488418 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 3) <| besselDerivativeNearFromState (562566863594009 / 4000000000000) 3 (IntervalRat.scale (193 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-3668662868 / 1000000000000) (-3668662865 / 1000000000000), orderedInterval (-67166606432 / 1000000000000) (-67166606429 / 1000000000000)))) (orderedInterval (-8716411990 / 1000000000000) (-8716411958 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate215_chunkChecks3_1 :
    compactCertificate215.chunkChecks (3 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 3) <| besselDerivativeNearFromState (863122239314807 / 4000000000000) 3 (IntervalRat.scale (193 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (11031269243 / 1000000000000) (11031269305 / 1000000000000), orderedInterval (-53210422077 / 1000000000000) (-53210422016 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 3) <| besselDerivativeNearFromState (498323857211903 / 4000000000000) 3 (IntervalRat.scale (193 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-21012228117 / 1000000000000) (-21012227705 / 1000000000000), orderedInterval (68411549904 / 1000000000000) (68411550316 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 3) <| besselDerivativeNearFromState (884284429370827 / 4000000000000) 3 (IntervalRat.scale (193 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (49959993961 / 1000000000000) (49960001225 / 1000000000000), orderedInterval (-19701237698 / 1000000000000) (-19701230434 / 1000000000000)))) (orderedInterval (-82679981150 / 1000000000000) (-82679968118 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 3) <| besselDerivativeNearFromState (826213220277463 / 4000000000000) 3 (IntervalRat.scale (193 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-389560970 / 1000000000000) (-389560967 / 1000000000000), orderedInterval (55516401517 / 1000000000000) (55516401521 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 3) <| besselDerivativeNearFromState (589624739417479 / 4000000000000) 3 (IntervalRat.scale (193 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-33555228534 / 1000000000000) (-33555228533 / 1000000000000), orderedInterval (-56391683854 / 1000000000000) (-56391683853 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 3) <| besselDerivativeNearFromState (668571611721441 / 4000000000000) 3 (IntervalRat.scale (193 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-61044094340 / 1000000000000) (-61044094334 / 1000000000000), orderedInterval (-8896897994 / 1000000000000) (-8896897989 / 1000000000000)))) (orderedInterval (28532016050 / 1000000000000) (28532016104 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 3) <| besselDerivativeNearFromState (557385307758929 / 4000000000000) 3 (IntervalRat.scale (193 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (63945230871 / 1000000000000) (63945233832 / 1000000000000), orderedInterval (-22129203515 / 1000000000000) (-22129200553 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 3) <| besselDerivativeNearFromState (492466823205509 / 4000000000000) 3 (IntervalRat.scale (193 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-70589529258 / 1000000000000) (-70589529255 / 1000000000000), orderedInterval (-13422560429 / 1000000000000) (-13422560426 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 3) <| besselDerivativeNearFromState (142736080181391 / 800000000000) 3 (IntervalRat.scale (193 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-7981324431 / 1000000000000) (-7981324430 / 1000000000000), orderedInterval (-59175660818 / 1000000000000) (-59175660817 / 1000000000000)))) (orderedInterval (8826989698 / 1000000000000) (8826989833 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate215_chunkChecks3_2 :
    compactCertificate215.chunkChecks (3 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 3) <| besselDerivativeNearFromState (394815509570077 / 4000000000000) 3 (IntervalRat.scale (193 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-69379639062 / 1000000000000) (-69379620913 / 1000000000000), orderedInterval (40801664601 / 1000000000000) (40801682750 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 3) <| besselDerivativeNearFromState (334689479924597 / 4000000000000) 3 (IntervalRat.scale (193 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (31275895169 / 1000000000000) (31275896383 / 1000000000000), orderedInterval (-81614168416 / 1000000000000) (-81614167202 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 3) <| besselDerivativeNearFromState (209433136405991 / 4000000000000) 3 (IntervalRat.scale (193 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (28962383929 / 1000000000000) (28962384355 / 1000000000000), orderedInterval (-106674721165 / 1000000000000) (-106674720739 / 1000000000000)))) (orderedInterval (4632971868 / 1000000000000) (4632975073 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 3) <| besselDerivativeNearFromState (112633837302297 / 4000000000000) 3 (IntervalRat.scale (193 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-92784751829 / 1000000000000) (-92784751828 / 1000000000000), orderedInterval (-116675880265 / 1000000000000) (-116675880264 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 3) <| besselDerivativeNearFromState (305822778677891 / 4000000000000) 3 (IntervalRat.scale (193 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (87932943438 / 1000000000000) (87932944493 / 1000000000000), orderedInterval (-24953185588 / 1000000000000) (-24953184533 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 3) <| besselDerivativeNearFromState (417574858691107 / 4000000000000) 3 (IntervalRat.scale (193 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-77923754033 / 1000000000000) (-77923754020 / 1000000000000), orderedInterval (-4733342829 / 1000000000000) (-4733342816 / 1000000000000)))) (orderedInterval (-733057081 / 1000000000000) (-733057056 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 3) <| besselDerivativeNearFromState (176566863594009 / 4000000000000) 3 (IntervalRat.scale (193 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (97118929104 / 1000000000000) (97118929105 / 1000000000000), orderedInterval (69538638844 / 1000000000000) (69538638845 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 3) <| besselDerivativeNearFromState (717734497810489 / 4000000000000) 3 (IntervalRat.scale (193 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-54308399396 / 1000000000000) (-54308399395 / 1000000000000), orderedInterval (-24313517506 / 1000000000000) (-24313517505 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 3) <| besselDerivativeNearFromState (479413381804151 / 4000000000000) 3 (IntervalRat.scale (193 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (69325968147 / 1000000000000) (69325968148 / 1000000000000), orderedInterval (22194764991 / 1000000000000) (22194764992 / 1000000000000)))) (orderedInterval (-4833949930 / 1000000000000) (-4833949843 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate215_chunkChecks3 :
    compactCertificate215.chunkChecks (3 : Fin 5) 0 9 = true :=
  compactCertificate215.chunkChecks_nine_of_three (3 : Fin 5) compactCertificate215_chunkChecks3_0
    compactCertificate215_chunkChecks3_1 compactCertificate215_chunkChecks3_2

theorem compactCertificate215_chunkChecks4_0 :
    compactCertificate215.chunkChecks (4 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 4) <| besselDerivativeNearFromState (193 / 2) 4 (IntervalRat.scale (193 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (8534401478 / 1000000000000) (8534401512 / 1000000000000), orderedInterval (-80817646471 / 1000000000000) (-80817646437 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 4) <| besselDerivativeNearFromState (284325852944893 / 4000000000000) 4 (IntervalRat.scale (193 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (36113224312 / 1000000000000) (36113226048 / 1000000000000), orderedInterval (-87730821091 / 1000000000000) (-87730819355 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 4) <| besselDerivativeNearFromState (91945138999069 / 800000000000) 4 (IntervalRat.scale (193 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (37186374071 / 1000000000000) (37186379828 / 1000000000000), orderedInterval (-64631356266 / 1000000000000) (-64631350509 / 1000000000000)))) (orderedInterval (7067079244 / 1000000000000) (7067079967 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 4) <| besselDerivativeNearFromState (82965574770551 / 4000000000000) 4 (IntervalRat.scale (193 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (79390542472 / 1000000000000) (79390547660 / 1000000000000), orderedInterval (-158103558079 / 1000000000000) (-158103552892 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 4) <| besselDerivativeNearFromState (222857203907147 / 4000000000000) 4 (IntervalRat.scale (193 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-5471778236 / 1000000000000) (-5471778215 / 1000000000000), orderedInterval (106805941069 / 1000000000000) (106805941089 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 4) <| besselDerivativeNearFromState (605100660507999 / 4000000000000) 4 (IntervalRat.scale (193 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (61828615662 / 1000000000000) (61828615663 / 1000000000000), orderedInterval (19431317445 / 1000000000000) (19431317446 / 1000000000000)))) (orderedInterval (-26658342894 / 1000000000000) (-26658342850 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 4) <| besselDerivativeNearFromState (445714407814487 / 4000000000000) 4 (IntervalRat.scale (193 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-58470936937 / 1000000000000) (-58470857030 / 1000000000000), orderedInterval (48162170069 / 1000000000000) (48162249975 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 4) <| besselDerivativeNearFromState (763739234748851 / 4000000000000) 4 (IntervalRat.scale (193 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-4752630726 / 1000000000000) (-4752630725 / 1000000000000), orderedInterval (-57534488420 / 1000000000000) (-57534488418 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 4) <| besselDerivativeNearFromState (562566863594009 / 4000000000000) 4 (IntervalRat.scale (193 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-3668662868 / 1000000000000) (-3668662865 / 1000000000000), orderedInterval (-67166606432 / 1000000000000) (-67166606429 / 1000000000000)))) (orderedInterval (2027226370 / 1000000000000) (2027226427 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate215_chunkChecks4_1 :
    compactCertificate215.chunkChecks (4 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 4) <| besselDerivativeNearFromState (863122239314807 / 4000000000000) 4 (IntervalRat.scale (193 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (11031269243 / 1000000000000) (11031269305 / 1000000000000), orderedInterval (-53210422077 / 1000000000000) (-53210422016 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 4) <| besselDerivativeNearFromState (498323857211903 / 4000000000000) 4 (IntervalRat.scale (193 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-21012228117 / 1000000000000) (-21012227705 / 1000000000000), orderedInterval (68411549904 / 1000000000000) (68411550316 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 4) <| besselDerivativeNearFromState (884284429370827 / 4000000000000) 4 (IntervalRat.scale (193 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (49959993961 / 1000000000000) (49960001225 / 1000000000000), orderedInterval (-19701237698 / 1000000000000) (-19701230434 / 1000000000000)))) (orderedInterval (143999937574 / 1000000000000) (143999967464 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 4) <| besselDerivativeNearFromState (826213220277463 / 4000000000000) 4 (IntervalRat.scale (193 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-389560970 / 1000000000000) (-389560967 / 1000000000000), orderedInterval (55516401517 / 1000000000000) (55516401521 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 4) <| besselDerivativeNearFromState (589624739417479 / 4000000000000) 4 (IntervalRat.scale (193 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-33555228534 / 1000000000000) (-33555228533 / 1000000000000), orderedInterval (-56391683854 / 1000000000000) (-56391683853 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 4) <| besselDerivativeNearFromState (668571611721441 / 4000000000000) 4 (IntervalRat.scale (193 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-61044094340 / 1000000000000) (-61044094334 / 1000000000000), orderedInterval (-8896897994 / 1000000000000) (-8896897989 / 1000000000000)))) (orderedInterval (-14938387538 / 1000000000000) (-14938387444 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 4) <| besselDerivativeNearFromState (557385307758929 / 4000000000000) 4 (IntervalRat.scale (193 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (63945230871 / 1000000000000) (63945233832 / 1000000000000), orderedInterval (-22129203515 / 1000000000000) (-22129200553 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 4) <| besselDerivativeNearFromState (492466823205509 / 4000000000000) 4 (IntervalRat.scale (193 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-70589529258 / 1000000000000) (-70589529255 / 1000000000000), orderedInterval (-13422560429 / 1000000000000) (-13422560426 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 4) <| besselDerivativeNearFromState (142736080181391 / 800000000000) 4 (IntervalRat.scale (193 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-7981324431 / 1000000000000) (-7981324430 / 1000000000000), orderedInterval (-59175660818 / 1000000000000) (-59175660817 / 1000000000000)))) (orderedInterval (11341513890 / 1000000000000) (11341514091 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate215_chunkChecks4_2 :
    compactCertificate215.chunkChecks (4 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 4) <| besselDerivativeNearFromState (394815509570077 / 4000000000000) 4 (IntervalRat.scale (193 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-69379639062 / 1000000000000) (-69379620913 / 1000000000000), orderedInterval (40801664601 / 1000000000000) (40801682750 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 4) <| besselDerivativeNearFromState (334689479924597 / 4000000000000) 4 (IntervalRat.scale (193 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (31275895169 / 1000000000000) (31275896383 / 1000000000000), orderedInterval (-81614168416 / 1000000000000) (-81614167202 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 4) <| besselDerivativeNearFromState (209433136405991 / 4000000000000) 4 (IntervalRat.scale (193 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (28962383929 / 1000000000000) (28962384355 / 1000000000000), orderedInterval (-106674721165 / 1000000000000) (-106674720739 / 1000000000000)))) (orderedInterval (11125927654 / 1000000000000) (11125930956 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 4) <| besselDerivativeNearFromState (112633837302297 / 4000000000000) 4 (IntervalRat.scale (193 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-92784751829 / 1000000000000) (-92784751828 / 1000000000000), orderedInterval (-116675880265 / 1000000000000) (-116675880264 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 4) <| besselDerivativeNearFromState (305822778677891 / 4000000000000) 4 (IntervalRat.scale (193 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (87932943438 / 1000000000000) (87932944493 / 1000000000000), orderedInterval (-24953185588 / 1000000000000) (-24953184533 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 4) <| besselDerivativeNearFromState (417574858691107 / 4000000000000) 4 (IntervalRat.scale (193 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-77923754033 / 1000000000000) (-77923754020 / 1000000000000), orderedInterval (-4733342829 / 1000000000000) (-4733342816 / 1000000000000)))) (orderedInterval (7420048071 / 1000000000000) (7420048094 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 4) <| besselDerivativeNearFromState (176566863594009 / 4000000000000) 4 (IntervalRat.scale (193 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (97118929104 / 1000000000000) (97118929105 / 1000000000000), orderedInterval (69538638844 / 1000000000000) (69538638845 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 4) <| besselDerivativeNearFromState (717734497810489 / 4000000000000) 4 (IntervalRat.scale (193 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-54308399396 / 1000000000000) (-54308399395 / 1000000000000), orderedInterval (-24313517506 / 1000000000000) (-24313517505 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 4) <| besselDerivativeNearFromState (479413381804151 / 4000000000000) 4 (IntervalRat.scale (193 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (69325968147 / 1000000000000) (69325968148 / 1000000000000), orderedInterval (22194764991 / 1000000000000) (22194764992 / 1000000000000)))) (orderedInterval (22020201309 / 1000000000000) (22020201448 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate215_chunkChecks4 :
    compactCertificate215.chunkChecks (4 : Fin 5) 0 9 = true :=
  compactCertificate215.chunkChecks_nine_of_three (4 : Fin 5) compactCertificate215_chunkChecks4_0
    compactCertificate215_chunkChecks4_1 compactCertificate215_chunkChecks4_2

theorem compactCertificate215_chunks :
    ∀ r : Fin 5, ∀ b, compactCertificate215.chunkCheck r b = true :=
  compactCertificate215.chunkChecks_all (by
    intro r
    fin_cases r
    · exact compactCertificate215_chunkChecks0
    · exact compactCertificate215_chunkChecks1
    · exact compactCertificate215_chunkChecks2
    · exact compactCertificate215_chunkChecks3
    · exact compactCertificate215_chunkChecks4)

theorem compactCertificate215_coefficient0 :
    compactCertificate215.coefficientCheck (0 : Fin 5) = true := by
  norm_num [CompactCertificate.coefficientCheck, intervalFinSumHull,
    compactCertificate215, rationalIntervalSubset, orderedInterval, Fin.sum_univ_succ]

theorem compactCertificate215_coefficient1 :
    compactCertificate215.coefficientCheck (1 : Fin 5) = true := by
  norm_num [CompactCertificate.coefficientCheck, intervalFinSumHull,
    compactCertificate215, rationalIntervalSubset, orderedInterval, Fin.sum_univ_succ]

theorem compactCertificate215_coefficient2 :
    compactCertificate215.coefficientCheck (2 : Fin 5) = true := by
  norm_num [CompactCertificate.coefficientCheck, intervalFinSumHull,
    compactCertificate215, rationalIntervalSubset, orderedInterval, Fin.sum_univ_succ]

theorem compactCertificate215_coefficient3 :
    compactCertificate215.coefficientCheck (3 : Fin 5) = true := by
  norm_num [CompactCertificate.coefficientCheck, intervalFinSumHull,
    compactCertificate215, rationalIntervalSubset, orderedInterval, Fin.sum_univ_succ]

theorem compactCertificate215_coefficient4 :
    compactCertificate215.coefficientCheck (4 : Fin 5) = true := by
  norm_num [CompactCertificate.coefficientCheck, intervalFinSumHull,
    compactCertificate215, rationalIntervalSubset, orderedInterval, Fin.sum_univ_succ]

theorem compactCertificate215_coefficients : ∀ r : Fin 5,
    compactCertificate215.coefficientCheck r = true := by
  intro r
  fin_cases r
  · exact compactCertificate215_coefficient0
  · exact compactCertificate215_coefficient1
  · exact compactCertificate215_coefficient2
  · exact compactCertificate215_coefficient3
  · exact compactCertificate215_coefficient4

theorem compactCertificate215_lower : (1 : ℚ) ≤ compactCertificate215.output.lo := by
  norm_num [CompactCertificate.output, CompactCertificate.interval,
    CompactCertificate.coefficientTargetNat, compactCertificate215, dualConstant,
    intervalTaylorSum, intervalPow, intervalSub, intervalMaxAbs, widenInterval,
    rationalErrorInterval, orderedInterval, IntervalRat.add, IntervalRat.mul, IntervalRat.scale,
    IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4]

theorem compactCertificate215_proves {t : ℝ} (ht : t ∈ compactCertificate215.interval) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t :=
  compactCertificate215.proves compactCertificate215_states compactCertificate215_chunks
    compactCertificate215_coefficients compactCertificate215_lower ht

end Erdos232
