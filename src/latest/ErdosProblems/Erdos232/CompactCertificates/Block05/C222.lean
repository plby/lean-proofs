/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, OpenAI Codex
-/
import ErdosProblems.Erdos232.CompactBase

open LeanCert.Core
namespace Erdos232

def compactCertificate222 : CompactCertificate where
  left := 101
  right := 102
  center := 203 / 2
  grid := fun i =>
    match i.val with
    | 0 => 32
    | 1 => 24
    | 2 => 38
    | 3 => 7
    | 4 => 19
    | 5 => 51
    | 6 => 37
    | 7 => 64
    | 8 => 47
    | 9 => 72
    | 10 => 42
    | 11 => 74
    | 12 => 69
    | 13 => 49
    | 14 => 56
    | 15 => 47
    | 16 => 41
    | 17 => 60
    | 18 => 33
    | 19 => 28
    | 20 => 18
    | 21 => 9
    | 22 => 26
    | 23 => 35
    | 24 => 15
    | 25 => 60
    | _ => 40
  point := fun i =>
    match i.val with
    | 0 => 203 / 2
    | 1 => 299057762423903 / 4000000000000
    | 2 => 96709135838399 / 800000000000
    | 3 => 87264309214621 / 4000000000000
    | 4 => 234404209290937 / 4000000000000
    | 5 => 636453026337429 / 4000000000000
    | 6 => 468808418582077 / 4000000000000
    | 7 => 803311215823921 / 4000000000000
    | 8 => 591715405749139 / 4000000000000
    | 9 => 907843598864797 / 4000000000000
    | 10 => 524143746186613 / 4000000000000
    | 11 => 930102275452217 / 4000000000000
    | 12 => 869022195421373 / 4000000000000
    | 13 => 620175244050509 / 4000000000000
    | 14 => 703212627872811 / 4000000000000
    | 15 => 586265375518459 / 4000000000000
    | 16 => 517983238915639 / 4000000000000
    | 17 => 150131732004261 / 800000000000
    | 18 => 415272271723967 / 4000000000000
    | 19 => 352030903754887 / 4000000000000
    | 20 => 220284594250861 / 4000000000000
    | 21 => 118469787421587 / 4000000000000
    | 22 => 321668518505761 / 4000000000000
    | 23 => 439210861732097 / 4000000000000
    | 24 => 185715405749139 / 4000000000000
    | 25 => 754922813759219 / 4000000000000
    | _ => 504253453400221 / 4000000000000
  state := fun i =>
    match i.val with
    | 0 => (orderedInterval (77882361756 / 1000000000000) (77882362173 / 1000000000000), orderedInterval (-14749670105 / 1000000000000) (-14749669689 / 1000000000000))
    | 1 => (orderedInterval (13784346880 / 1000000000000) (13784346882 / 1000000000000), orderedInterval (91150249568 / 1000000000000) (91150249570 / 1000000000000))
    | 2 => (orderedInterval (54583025918 / 1000000000000) (54583135707 / 1000000000000), orderedInterval (-48047822077 / 1000000000000) (-48047712288 / 1000000000000))
    | 3 => (orderedInterval (-97090409879 / 1000000000000) (-97090409878 / 1000000000000), orderedInterval (-138336892530 / 1000000000000) (-138336892529 / 1000000000000))
    | 4 => (orderedInterval (31392303514 / 1000000000000) (31392304191 / 1000000000000), orderedInterval (-99658322737 / 1000000000000) (-99658322060 / 1000000000000))
    | 5 => (orderedInterval (20098893818 / 1000000000000) (20098894272 / 1000000000000), orderedInterval (-60038972076 / 1000000000000) (-60038971622 / 1000000000000))
    | 6 => (orderedInterval (-72552757525 / 1000000000000) (-72552757097 / 1000000000000), orderedInterval (13265702256 / 1000000000000) (13265702684 / 1000000000000))
    | 7 => (orderedInterval (29459770685 / 1000000000000) (29459770686 / 1000000000000), orderedInterval (47906906953 / 1000000000000) (47906906954 / 1000000000000))
    | 8 => (orderedInterval (-57181079105 / 1000000000000) (-57181079104 / 1000000000000), orderedInterval (-31960504760 / 1000000000000) (-31960504759 / 1000000000000))
    | 9 => (orderedInterval (52951657689 / 1000000000000) (52951657751 / 1000000000000), orderedInterval (927704985 / 1000000000000) (927705048 / 1000000000000))
    | 10 => (orderedInterval (-8794502166 / 1000000000000) (-8794502129 / 1000000000000), orderedInterval (69178702411 / 1000000000000) (69178702448 / 1000000000000))
    | 11 => (orderedInterval (38702545571 / 1000000000000) (38702545572 / 1000000000000), orderedInterval (35129855905 / 1000000000000) (35129855906 / 1000000000000))
    | 12 => (orderedInterval (-51709185973 / 1000000000000) (-51709185972 / 1000000000000), orderedInterval (-15894568337 / 1000000000000) (-15894568335 / 1000000000000))
    | 13 => (orderedInterval (-60834225965 / 1000000000000) (-60834223084 / 1000000000000), orderedInterval (20326846970 / 1000000000000) (20326849851 / 1000000000000))
    | 14 => (orderedInterval (36831186465 / 1000000000000) (36831186466 / 1000000000000), orderedInterval (47483853609 / 1000000000000) (47483853610 / 1000000000000))
    | 15 => (orderedInterval (19725929745 / 1000000000000) (19725930129 / 1000000000000), orderedInterval (-62951860720 / 1000000000000) (-62951860336 / 1000000000000))
    | 16 => (orderedInterval (-69793092038 / 1000000000000) (-69793092028 / 1000000000000), orderedInterval (-6440978808 / 1000000000000) (-6440978799 / 1000000000000))
    | 17 => (orderedInterval (-2687692104 / 1000000000000) (-2687692097 / 1000000000000), orderedInterval (58188898230 / 1000000000000) (58188898237 / 1000000000000))
    | 18 => (orderedInterval (-62758689083 / 1000000000000) (-62758689082 / 1000000000000), orderedInterval (-46531478726 / 1000000000000) (-46531478725 / 1000000000000))
    | 19 => (orderedInterval (62595160806 / 1000000000000) (62595160807 / 1000000000000), orderedInterval (57224911423 / 1000000000000) (57224911424 / 1000000000000))
    | 20 => (orderedInterval (-68800708773 / 1000000000000) (-68800668956 / 1000000000000), orderedInterval (83247228760 / 1000000000000) (83247268578 / 1000000000000))
    | 21 => (orderedInterval (-124711792900 / 1000000000000) (-124711775832 / 1000000000000), orderedInterval (79178490691 / 1000000000000) (79178507758 / 1000000000000))
    | 22 => (orderedInterval (-41120560621 / 1000000000000) (-41120556228 / 1000000000000), orderedInterval (79158490975 / 1000000000000) (79158495368 / 1000000000000))
    | 23 => (orderedInterval (-44935170343 / 1000000000000) (-44935170342 / 1000000000000), orderedInterval (-61266514707 / 1000000000000) (-61266514706 / 1000000000000))
    | 24 => (orderedInterval (-10252243747 / 1000000000000) (-10252243744 / 1000000000000), orderedInterval (-116540372511 / 1000000000000) (-116540372508 / 1000000000000))
    | 25 => (orderedInterval (49485809765 / 1000000000000) (49485809766 / 1000000000000), orderedInterval (30271434013 / 1000000000000) (30271434014 / 1000000000000))
    | _ => (orderedInterval (65814797128 / 1000000000000) (65814797129 / 1000000000000), orderedInterval (26541621676 / 1000000000000) (26541621677 / 1000000000000))
  chunkTarget := fun r b =>
    match r.val with
    | 0 =>
      match b.val with
      | 0 => orderedInterval (34201279325 / 1000000000000) (34201285941 / 1000000000000)
      | 1 => orderedInterval (770726738 / 1000000000000) (770726808 / 1000000000000)
      | 2 => orderedInterval (-2290611063 / 1000000000000) (-2290611057 / 1000000000000)
      | 3 => orderedInterval (-4558675617 / 1000000000000) (-4558675562 / 1000000000000)
      | 4 => orderedInterval (-5005535402 / 1000000000000) (-5005535116 / 1000000000000)
      | 5 => orderedInterval (4152999722 / 1000000000000) (4152999738 / 1000000000000)
      | 6 => orderedInterval (4251930974 / 1000000000000) (4251932297 / 1000000000000)
      | 7 => orderedInterval (6679494588 / 1000000000000) (6679495016 / 1000000000000)
      | _ => orderedInterval (-16438638564 / 1000000000000) (-16438638535 / 1000000000000)
    | 1 =>
      match b.val with
      | 0 => orderedInterval (-8578653751 / 1000000000000) (-8578645904 / 1000000000000)
      | 1 => orderedInterval (4912613608 / 1000000000000) (4912613688 / 1000000000000)
      | 2 => orderedInterval (-4049407728 / 1000000000000) (-4049407717 / 1000000000000)
      | 3 => orderedInterval (17689011552 / 1000000000000) (17689011665 / 1000000000000)
      | 4 => orderedInterval (3134144337 / 1000000000000) (3134144774 / 1000000000000)
      | 5 => orderedInterval (2175179695 / 1000000000000) (2175179717 / 1000000000000)
      | 6 => orderedInterval (6272013676 / 1000000000000) (6272014404 / 1000000000000)
      | 7 => orderedInterval (3230026028 / 1000000000000) (3230026210 / 1000000000000)
      | _ => orderedInterval (-11088308089 / 1000000000000) (-11088308049 / 1000000000000)
    | 2 =>
      match b.val with
      | 0 => orderedInterval (-35398402660 / 1000000000000) (-35398393269 / 1000000000000)
      | 1 => orderedInterval (3032102968 / 1000000000000) (3032103076 / 1000000000000)
      | 2 => orderedInterval (6532555688 / 1000000000000) (6532555706 / 1000000000000)
      | 3 => orderedInterval (19081624065 / 1000000000000) (19081624305 / 1000000000000)
      | 4 => orderedInterval (9674255259 / 1000000000000) (9674255932 / 1000000000000)
      | 5 => orderedInterval (-6762310095 / 1000000000000) (-6762310062 / 1000000000000)
      | 6 => orderedInterval (-7237056255 / 1000000000000) (-7237055843 / 1000000000000)
      | 7 => orderedInterval (-4843722196 / 1000000000000) (-4843722093 / 1000000000000)
      | _ => orderedInterval (33098116069 / 1000000000000) (33098116129 / 1000000000000)
    | 3 =>
      match b.val with
      | 0 => orderedInterval (10618002047 / 1000000000000) (10618013198 / 1000000000000)
      | 1 => orderedInterval (-15786254081 / 1000000000000) (-15786253921 / 1000000000000)
      | 2 => orderedInterval (13772140421 / 1000000000000) (13772140455 / 1000000000000)
      | 3 => orderedInterval (-69413780655 / 1000000000000) (-69413780130 / 1000000000000)
      | 4 => orderedInterval (-8511365176 / 1000000000000) (-8511364143 / 1000000000000)
      | 5 => orderedInterval (-7926463774 / 1000000000000) (-7926463725 / 1000000000000)
      | 6 => orderedInterval (-6211103484 / 1000000000000) (-6211103251 / 1000000000000)
      | 7 => orderedInterval (-4966973594 / 1000000000000) (-4966973524 / 1000000000000)
      | _ => orderedInterval (25122499868 / 1000000000000) (25122499959 / 1000000000000)
    | _ =>
      match b.val with
      | 0 => orderedInterval (37139694070 / 1000000000000) (37139707427 / 1000000000000)
      | 1 => orderedInterval (-8187637751 / 1000000000000) (-8187637505 / 1000000000000)
      | 2 => orderedInterval (-20431954398 / 1000000000000) (-20431954337 / 1000000000000)
      | 3 => orderedInterval (-84123626252 / 1000000000000) (-84123625092 / 1000000000000)
      | 4 => orderedInterval (-13234172256 / 1000000000000) (-13234170657 / 1000000000000)
      | 5 => orderedInterval (10923782530 / 1000000000000) (10923782605 / 1000000000000)
      | 6 => orderedInterval (8908265726 / 1000000000000) (8908265865 / 1000000000000)
      | 7 => orderedInterval (5198224226 / 1000000000000) (5198224282 / 1000000000000)
      | _ => orderedInterval (-78031088373 / 1000000000000) (-78031088226 / 1000000000000)
  coefficientTarget := fun i =>
    match i.val with
    | 0 => orderedInterval (21762970701 / 1000000000000) (21762979530 / 1000000000000)
    | 1 => orderedInterval (13696619328 / 1000000000000) (13696628788 / 1000000000000)
    | 2 => orderedInterval (17177162843 / 1000000000000) (17177173881 / 1000000000000)
    | 3 => orderedInterval (-63303298428 / 1000000000000) (-63303285082 / 1000000000000)
    | _ => orderedInterval (-141838512478 / 1000000000000) (-141838495638 / 1000000000000)

theorem compactCertificate222_stateChecks0 :
    compactCertificate222.stateChecks 0 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 32 12 (203 / 2)) (orderedInterval (77882361756 / 1000000000000) (77882362173 / 1000000000000), orderedInterval (-14749670105 / 1000000000000) (-14749669689 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 24 12 (299057762423903 / 4000000000000)) (orderedInterval (13784346880 / 1000000000000) (13784346882 / 1000000000000), orderedInterval (91150249568 / 1000000000000) (91150249570 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 38 12 (96709135838399 / 800000000000)) (orderedInterval (54583025918 / 1000000000000) (54583135707 / 1000000000000), orderedInterval (-48047822077 / 1000000000000) (-48047712288 / 1000000000000))) = true
  norm_num [besselStateAtRationalPoint, besselIntervalStepZero,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, besselZeroTransition,
    besselInitial, besselGridStateAt, besselGridStateBlock00, besselGridStateBlock01,
    besselGridStateBlock02, besselGridStateBlock03, besselGridStateBlock04,
    besselGridStateBlock05, besselGridStateBlock06, besselGridStateBlock07,
    besselGridStateBlock08, besselGridStateBlock09, besselGridStateBlock10,
    besselGridStateBlock11, besselGridStateBlock12, besselGridStateBlock13,
    besselGridStateBlock14, besselGridState007, besselGridState009, besselGridState015, besselGridState018, besselGridState019, besselGridState024, besselGridState026, besselGridState028, besselGridState032, besselGridState033, besselGridState035, besselGridState037, besselGridState038, besselGridState040, besselGridState041, besselGridState042, besselGridState047, besselGridState049, besselGridState051, besselGridState056, besselGridState060, besselGridState064, besselGridState069, besselGridState072, besselGridState074, besselStateSubset, linearInterval, widenInterval,
    rationalErrorInterval, rationalIntervalSubset, orderedInterval, Finset.sum_range_succ,
    IntervalRat.add, IntervalRat.mul, IntervalRat.scale, IntervalRat.singleton]

theorem compactCertificate222_stateChecks1 :
    compactCertificate222.stateChecks 3 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 7 12 (87264309214621 / 4000000000000)) (orderedInterval (-97090409879 / 1000000000000) (-97090409878 / 1000000000000), orderedInterval (-138336892530 / 1000000000000) (-138336892529 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 19 12 (234404209290937 / 4000000000000)) (orderedInterval (31392303514 / 1000000000000) (31392304191 / 1000000000000), orderedInterval (-99658322737 / 1000000000000) (-99658322060 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 51 12 (636453026337429 / 4000000000000)) (orderedInterval (20098893818 / 1000000000000) (20098894272 / 1000000000000), orderedInterval (-60038972076 / 1000000000000) (-60038971622 / 1000000000000))) = true
  norm_num [besselStateAtRationalPoint, besselIntervalStepZero,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, besselZeroTransition,
    besselInitial, besselGridStateAt, besselGridStateBlock00, besselGridStateBlock01,
    besselGridStateBlock02, besselGridStateBlock03, besselGridStateBlock04,
    besselGridStateBlock05, besselGridStateBlock06, besselGridStateBlock07,
    besselGridStateBlock08, besselGridStateBlock09, besselGridStateBlock10,
    besselGridStateBlock11, besselGridStateBlock12, besselGridStateBlock13,
    besselGridStateBlock14, besselGridState007, besselGridState009, besselGridState015, besselGridState018, besselGridState019, besselGridState024, besselGridState026, besselGridState028, besselGridState032, besselGridState033, besselGridState035, besselGridState037, besselGridState038, besselGridState040, besselGridState041, besselGridState042, besselGridState047, besselGridState049, besselGridState051, besselGridState056, besselGridState060, besselGridState064, besselGridState069, besselGridState072, besselGridState074, besselStateSubset, linearInterval, widenInterval,
    rationalErrorInterval, rationalIntervalSubset, orderedInterval, Finset.sum_range_succ,
    IntervalRat.add, IntervalRat.mul, IntervalRat.scale, IntervalRat.singleton]

theorem compactCertificate222_stateChecks2 :
    compactCertificate222.stateChecks 6 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 37 12 (468808418582077 / 4000000000000)) (orderedInterval (-72552757525 / 1000000000000) (-72552757097 / 1000000000000), orderedInterval (13265702256 / 1000000000000) (13265702684 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 64 12 (803311215823921 / 4000000000000)) (orderedInterval (29459770685 / 1000000000000) (29459770686 / 1000000000000), orderedInterval (47906906953 / 1000000000000) (47906906954 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 47 12 (591715405749139 / 4000000000000)) (orderedInterval (-57181079105 / 1000000000000) (-57181079104 / 1000000000000), orderedInterval (-31960504760 / 1000000000000) (-31960504759 / 1000000000000))) = true
  norm_num [besselStateAtRationalPoint, besselIntervalStepZero,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, besselZeroTransition,
    besselInitial, besselGridStateAt, besselGridStateBlock00, besselGridStateBlock01,
    besselGridStateBlock02, besselGridStateBlock03, besselGridStateBlock04,
    besselGridStateBlock05, besselGridStateBlock06, besselGridStateBlock07,
    besselGridStateBlock08, besselGridStateBlock09, besselGridStateBlock10,
    besselGridStateBlock11, besselGridStateBlock12, besselGridStateBlock13,
    besselGridStateBlock14, besselGridState007, besselGridState009, besselGridState015, besselGridState018, besselGridState019, besselGridState024, besselGridState026, besselGridState028, besselGridState032, besselGridState033, besselGridState035, besselGridState037, besselGridState038, besselGridState040, besselGridState041, besselGridState042, besselGridState047, besselGridState049, besselGridState051, besselGridState056, besselGridState060, besselGridState064, besselGridState069, besselGridState072, besselGridState074, besselStateSubset, linearInterval, widenInterval,
    rationalErrorInterval, rationalIntervalSubset, orderedInterval, Finset.sum_range_succ,
    IntervalRat.add, IntervalRat.mul, IntervalRat.scale, IntervalRat.singleton]

theorem compactCertificate222_stateChecks3 :
    compactCertificate222.stateChecks 9 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 72 12 (907843598864797 / 4000000000000)) (orderedInterval (52951657689 / 1000000000000) (52951657751 / 1000000000000), orderedInterval (927704985 / 1000000000000) (927705048 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 42 12 (524143746186613 / 4000000000000)) (orderedInterval (-8794502166 / 1000000000000) (-8794502129 / 1000000000000), orderedInterval (69178702411 / 1000000000000) (69178702448 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 74 12 (930102275452217 / 4000000000000)) (orderedInterval (38702545571 / 1000000000000) (38702545572 / 1000000000000), orderedInterval (35129855905 / 1000000000000) (35129855906 / 1000000000000))) = true
  norm_num [besselStateAtRationalPoint, besselIntervalStepZero,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, besselZeroTransition,
    besselInitial, besselGridStateAt, besselGridStateBlock00, besselGridStateBlock01,
    besselGridStateBlock02, besselGridStateBlock03, besselGridStateBlock04,
    besselGridStateBlock05, besselGridStateBlock06, besselGridStateBlock07,
    besselGridStateBlock08, besselGridStateBlock09, besselGridStateBlock10,
    besselGridStateBlock11, besselGridStateBlock12, besselGridStateBlock13,
    besselGridStateBlock14, besselGridState007, besselGridState009, besselGridState015, besselGridState018, besselGridState019, besselGridState024, besselGridState026, besselGridState028, besselGridState032, besselGridState033, besselGridState035, besselGridState037, besselGridState038, besselGridState040, besselGridState041, besselGridState042, besselGridState047, besselGridState049, besselGridState051, besselGridState056, besselGridState060, besselGridState064, besselGridState069, besselGridState072, besselGridState074, besselStateSubset, linearInterval, widenInterval,
    rationalErrorInterval, rationalIntervalSubset, orderedInterval, Finset.sum_range_succ,
    IntervalRat.add, IntervalRat.mul, IntervalRat.scale, IntervalRat.singleton]

theorem compactCertificate222_stateChecks4 :
    compactCertificate222.stateChecks 12 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 69 12 (869022195421373 / 4000000000000)) (orderedInterval (-51709185973 / 1000000000000) (-51709185972 / 1000000000000), orderedInterval (-15894568337 / 1000000000000) (-15894568335 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 49 12 (620175244050509 / 4000000000000)) (orderedInterval (-60834225965 / 1000000000000) (-60834223084 / 1000000000000), orderedInterval (20326846970 / 1000000000000) (20326849851 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 56 12 (703212627872811 / 4000000000000)) (orderedInterval (36831186465 / 1000000000000) (36831186466 / 1000000000000), orderedInterval (47483853609 / 1000000000000) (47483853610 / 1000000000000))) = true
  norm_num [besselStateAtRationalPoint, besselIntervalStepZero,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, besselZeroTransition,
    besselInitial, besselGridStateAt, besselGridStateBlock00, besselGridStateBlock01,
    besselGridStateBlock02, besselGridStateBlock03, besselGridStateBlock04,
    besselGridStateBlock05, besselGridStateBlock06, besselGridStateBlock07,
    besselGridStateBlock08, besselGridStateBlock09, besselGridStateBlock10,
    besselGridStateBlock11, besselGridStateBlock12, besselGridStateBlock13,
    besselGridStateBlock14, besselGridState007, besselGridState009, besselGridState015, besselGridState018, besselGridState019, besselGridState024, besselGridState026, besselGridState028, besselGridState032, besselGridState033, besselGridState035, besselGridState037, besselGridState038, besselGridState040, besselGridState041, besselGridState042, besselGridState047, besselGridState049, besselGridState051, besselGridState056, besselGridState060, besselGridState064, besselGridState069, besselGridState072, besselGridState074, besselStateSubset, linearInterval, widenInterval,
    rationalErrorInterval, rationalIntervalSubset, orderedInterval, Finset.sum_range_succ,
    IntervalRat.add, IntervalRat.mul, IntervalRat.scale, IntervalRat.singleton]

theorem compactCertificate222_stateChecks5 :
    compactCertificate222.stateChecks 15 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 47 12 (586265375518459 / 4000000000000)) (orderedInterval (19725929745 / 1000000000000) (19725930129 / 1000000000000), orderedInterval (-62951860720 / 1000000000000) (-62951860336 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 41 12 (517983238915639 / 4000000000000)) (orderedInterval (-69793092038 / 1000000000000) (-69793092028 / 1000000000000), orderedInterval (-6440978808 / 1000000000000) (-6440978799 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 60 12 (150131732004261 / 800000000000)) (orderedInterval (-2687692104 / 1000000000000) (-2687692097 / 1000000000000), orderedInterval (58188898230 / 1000000000000) (58188898237 / 1000000000000))) = true
  norm_num [besselStateAtRationalPoint, besselIntervalStepZero,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, besselZeroTransition,
    besselInitial, besselGridStateAt, besselGridStateBlock00, besselGridStateBlock01,
    besselGridStateBlock02, besselGridStateBlock03, besselGridStateBlock04,
    besselGridStateBlock05, besselGridStateBlock06, besselGridStateBlock07,
    besselGridStateBlock08, besselGridStateBlock09, besselGridStateBlock10,
    besselGridStateBlock11, besselGridStateBlock12, besselGridStateBlock13,
    besselGridStateBlock14, besselGridState007, besselGridState009, besselGridState015, besselGridState018, besselGridState019, besselGridState024, besselGridState026, besselGridState028, besselGridState032, besselGridState033, besselGridState035, besselGridState037, besselGridState038, besselGridState040, besselGridState041, besselGridState042, besselGridState047, besselGridState049, besselGridState051, besselGridState056, besselGridState060, besselGridState064, besselGridState069, besselGridState072, besselGridState074, besselStateSubset, linearInterval, widenInterval,
    rationalErrorInterval, rationalIntervalSubset, orderedInterval, Finset.sum_range_succ,
    IntervalRat.add, IntervalRat.mul, IntervalRat.scale, IntervalRat.singleton]

theorem compactCertificate222_stateChecks6 :
    compactCertificate222.stateChecks 18 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 33 12 (415272271723967 / 4000000000000)) (orderedInterval (-62758689083 / 1000000000000) (-62758689082 / 1000000000000), orderedInterval (-46531478726 / 1000000000000) (-46531478725 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 28 12 (352030903754887 / 4000000000000)) (orderedInterval (62595160806 / 1000000000000) (62595160807 / 1000000000000), orderedInterval (57224911423 / 1000000000000) (57224911424 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 18 12 (220284594250861 / 4000000000000)) (orderedInterval (-68800708773 / 1000000000000) (-68800668956 / 1000000000000), orderedInterval (83247228760 / 1000000000000) (83247268578 / 1000000000000))) = true
  norm_num [besselStateAtRationalPoint, besselIntervalStepZero,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, besselZeroTransition,
    besselInitial, besselGridStateAt, besselGridStateBlock00, besselGridStateBlock01,
    besselGridStateBlock02, besselGridStateBlock03, besselGridStateBlock04,
    besselGridStateBlock05, besselGridStateBlock06, besselGridStateBlock07,
    besselGridStateBlock08, besselGridStateBlock09, besselGridStateBlock10,
    besselGridStateBlock11, besselGridStateBlock12, besselGridStateBlock13,
    besselGridStateBlock14, besselGridState007, besselGridState009, besselGridState015, besselGridState018, besselGridState019, besselGridState024, besselGridState026, besselGridState028, besselGridState032, besselGridState033, besselGridState035, besselGridState037, besselGridState038, besselGridState040, besselGridState041, besselGridState042, besselGridState047, besselGridState049, besselGridState051, besselGridState056, besselGridState060, besselGridState064, besselGridState069, besselGridState072, besselGridState074, besselStateSubset, linearInterval, widenInterval,
    rationalErrorInterval, rationalIntervalSubset, orderedInterval, Finset.sum_range_succ,
    IntervalRat.add, IntervalRat.mul, IntervalRat.scale, IntervalRat.singleton]

theorem compactCertificate222_stateChecks7 :
    compactCertificate222.stateChecks 21 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 9 12 (118469787421587 / 4000000000000)) (orderedInterval (-124711792900 / 1000000000000) (-124711775832 / 1000000000000), orderedInterval (79178490691 / 1000000000000) (79178507758 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 26 12 (321668518505761 / 4000000000000)) (orderedInterval (-41120560621 / 1000000000000) (-41120556228 / 1000000000000), orderedInterval (79158490975 / 1000000000000) (79158495368 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 35 12 (439210861732097 / 4000000000000)) (orderedInterval (-44935170343 / 1000000000000) (-44935170342 / 1000000000000), orderedInterval (-61266514707 / 1000000000000) (-61266514706 / 1000000000000))) = true
  norm_num [besselStateAtRationalPoint, besselIntervalStepZero,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, besselZeroTransition,
    besselInitial, besselGridStateAt, besselGridStateBlock00, besselGridStateBlock01,
    besselGridStateBlock02, besselGridStateBlock03, besselGridStateBlock04,
    besselGridStateBlock05, besselGridStateBlock06, besselGridStateBlock07,
    besselGridStateBlock08, besselGridStateBlock09, besselGridStateBlock10,
    besselGridStateBlock11, besselGridStateBlock12, besselGridStateBlock13,
    besselGridStateBlock14, besselGridState007, besselGridState009, besselGridState015, besselGridState018, besselGridState019, besselGridState024, besselGridState026, besselGridState028, besselGridState032, besselGridState033, besselGridState035, besselGridState037, besselGridState038, besselGridState040, besselGridState041, besselGridState042, besselGridState047, besselGridState049, besselGridState051, besselGridState056, besselGridState060, besselGridState064, besselGridState069, besselGridState072, besselGridState074, besselStateSubset, linearInterval, widenInterval,
    rationalErrorInterval, rationalIntervalSubset, orderedInterval, Finset.sum_range_succ,
    IntervalRat.add, IntervalRat.mul, IntervalRat.scale, IntervalRat.singleton]

theorem compactCertificate222_stateChecks8 :
    compactCertificate222.stateChecks 24 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 15 12 (185715405749139 / 4000000000000)) (orderedInterval (-10252243747 / 1000000000000) (-10252243744 / 1000000000000), orderedInterval (-116540372511 / 1000000000000) (-116540372508 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 60 12 (754922813759219 / 4000000000000)) (orderedInterval (49485809765 / 1000000000000) (49485809766 / 1000000000000), orderedInterval (30271434013 / 1000000000000) (30271434014 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 40 12 (504253453400221 / 4000000000000)) (orderedInterval (65814797128 / 1000000000000) (65814797129 / 1000000000000), orderedInterval (26541621676 / 1000000000000) (26541621677 / 1000000000000))) = true
  norm_num [besselStateAtRationalPoint, besselIntervalStepZero,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, besselZeroTransition,
    besselInitial, besselGridStateAt, besselGridStateBlock00, besselGridStateBlock01,
    besselGridStateBlock02, besselGridStateBlock03, besselGridStateBlock04,
    besselGridStateBlock05, besselGridStateBlock06, besselGridStateBlock07,
    besselGridStateBlock08, besselGridStateBlock09, besselGridStateBlock10,
    besselGridStateBlock11, besselGridStateBlock12, besselGridStateBlock13,
    besselGridStateBlock14, besselGridState007, besselGridState009, besselGridState015, besselGridState018, besselGridState019, besselGridState024, besselGridState026, besselGridState028, besselGridState032, besselGridState033, besselGridState035, besselGridState037, besselGridState038, besselGridState040, besselGridState041, besselGridState042, besselGridState047, besselGridState049, besselGridState051, besselGridState056, besselGridState060, besselGridState064, besselGridState069, besselGridState072, besselGridState074, besselStateSubset, linearInterval, widenInterval,
    rationalErrorInterval, rationalIntervalSubset, orderedInterval, Finset.sum_range_succ,
    IntervalRat.add, IntervalRat.mul, IntervalRat.scale, IntervalRat.singleton]

theorem compactCertificate222_states : ∀ j,
    BesselStateValid (compactCertificate222.point j) (compactCertificate222.state j) :=
  compactCertificate222.statesValid_of_checks3 compactCertificate222_stateChecks0
    compactCertificate222_stateChecks1 compactCertificate222_stateChecks2
    compactCertificate222_stateChecks3 compactCertificate222_stateChecks4
    compactCertificate222_stateChecks5 compactCertificate222_stateChecks6
    compactCertificate222_stateChecks7 compactCertificate222_stateChecks8

theorem compactCertificate222_chunkChecks0_0 :
    compactCertificate222.chunkChecks (0 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 0) <| besselDerivativeNearFromState (203 / 2) 0 (IntervalRat.scale (203 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (77882361756 / 1000000000000) (77882362173 / 1000000000000), orderedInterval (-14749670105 / 1000000000000) (-14749669689 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 0) <| besselDerivativeNearFromState (299057762423903 / 4000000000000) 0 (IntervalRat.scale (203 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (13784346880 / 1000000000000) (13784346882 / 1000000000000), orderedInterval (91150249568 / 1000000000000) (91150249570 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 0) <| besselDerivativeNearFromState (96709135838399 / 800000000000) 0 (IntervalRat.scale (203 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (54583025918 / 1000000000000) (54583135707 / 1000000000000), orderedInterval (-48047822077 / 1000000000000) (-48047712288 / 1000000000000)))) (orderedInterval (34201279325 / 1000000000000) (34201285941 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 0) <| besselDerivativeNearFromState (87264309214621 / 4000000000000) 0 (IntervalRat.scale (203 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-97090409879 / 1000000000000) (-97090409878 / 1000000000000), orderedInterval (-138336892530 / 1000000000000) (-138336892529 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 0) <| besselDerivativeNearFromState (234404209290937 / 4000000000000) 0 (IntervalRat.scale (203 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (31392303514 / 1000000000000) (31392304191 / 1000000000000), orderedInterval (-99658322737 / 1000000000000) (-99658322060 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 0) <| besselDerivativeNearFromState (636453026337429 / 4000000000000) 0 (IntervalRat.scale (203 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (20098893818 / 1000000000000) (20098894272 / 1000000000000), orderedInterval (-60038972076 / 1000000000000) (-60038971622 / 1000000000000)))) (orderedInterval (770726738 / 1000000000000) (770726808 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 0) <| besselDerivativeNearFromState (468808418582077 / 4000000000000) 0 (IntervalRat.scale (203 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-72552757525 / 1000000000000) (-72552757097 / 1000000000000), orderedInterval (13265702256 / 1000000000000) (13265702684 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 0) <| besselDerivativeNearFromState (803311215823921 / 4000000000000) 0 (IntervalRat.scale (203 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (29459770685 / 1000000000000) (29459770686 / 1000000000000), orderedInterval (47906906953 / 1000000000000) (47906906954 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 0) <| besselDerivativeNearFromState (591715405749139 / 4000000000000) 0 (IntervalRat.scale (203 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-57181079105 / 1000000000000) (-57181079104 / 1000000000000), orderedInterval (-31960504760 / 1000000000000) (-31960504759 / 1000000000000)))) (orderedInterval (-2290611063 / 1000000000000) (-2290611057 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate222_chunkChecks0_1 :
    compactCertificate222.chunkChecks (0 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 0) <| besselDerivativeNearFromState (907843598864797 / 4000000000000) 0 (IntervalRat.scale (203 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (52951657689 / 1000000000000) (52951657751 / 1000000000000), orderedInterval (927704985 / 1000000000000) (927705048 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 0) <| besselDerivativeNearFromState (524143746186613 / 4000000000000) 0 (IntervalRat.scale (203 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-8794502166 / 1000000000000) (-8794502129 / 1000000000000), orderedInterval (69178702411 / 1000000000000) (69178702448 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 0) <| besselDerivativeNearFromState (930102275452217 / 4000000000000) 0 (IntervalRat.scale (203 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (38702545571 / 1000000000000) (38702545572 / 1000000000000), orderedInterval (35129855905 / 1000000000000) (35129855906 / 1000000000000)))) (orderedInterval (-4558675617 / 1000000000000) (-4558675562 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 0) <| besselDerivativeNearFromState (869022195421373 / 4000000000000) 0 (IntervalRat.scale (203 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-51709185973 / 1000000000000) (-51709185972 / 1000000000000), orderedInterval (-15894568337 / 1000000000000) (-15894568335 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 0) <| besselDerivativeNearFromState (620175244050509 / 4000000000000) 0 (IntervalRat.scale (203 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-60834225965 / 1000000000000) (-60834223084 / 1000000000000), orderedInterval (20326846970 / 1000000000000) (20326849851 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 0) <| besselDerivativeNearFromState (703212627872811 / 4000000000000) 0 (IntervalRat.scale (203 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (36831186465 / 1000000000000) (36831186466 / 1000000000000), orderedInterval (47483853609 / 1000000000000) (47483853610 / 1000000000000)))) (orderedInterval (-5005535402 / 1000000000000) (-5005535116 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 0) <| besselDerivativeNearFromState (586265375518459 / 4000000000000) 0 (IntervalRat.scale (203 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (19725929745 / 1000000000000) (19725930129 / 1000000000000), orderedInterval (-62951860720 / 1000000000000) (-62951860336 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 0) <| besselDerivativeNearFromState (517983238915639 / 4000000000000) 0 (IntervalRat.scale (203 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-69793092038 / 1000000000000) (-69793092028 / 1000000000000), orderedInterval (-6440978808 / 1000000000000) (-6440978799 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 0) <| besselDerivativeNearFromState (150131732004261 / 800000000000) 0 (IntervalRat.scale (203 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-2687692104 / 1000000000000) (-2687692097 / 1000000000000), orderedInterval (58188898230 / 1000000000000) (58188898237 / 1000000000000)))) (orderedInterval (4152999722 / 1000000000000) (4152999738 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate222_chunkChecks0_2 :
    compactCertificate222.chunkChecks (0 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 0) <| besselDerivativeNearFromState (415272271723967 / 4000000000000) 0 (IntervalRat.scale (203 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-62758689083 / 1000000000000) (-62758689082 / 1000000000000), orderedInterval (-46531478726 / 1000000000000) (-46531478725 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 0) <| besselDerivativeNearFromState (352030903754887 / 4000000000000) 0 (IntervalRat.scale (203 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (62595160806 / 1000000000000) (62595160807 / 1000000000000), orderedInterval (57224911423 / 1000000000000) (57224911424 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 0) <| besselDerivativeNearFromState (220284594250861 / 4000000000000) 0 (IntervalRat.scale (203 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-68800708773 / 1000000000000) (-68800668956 / 1000000000000), orderedInterval (83247228760 / 1000000000000) (83247268578 / 1000000000000)))) (orderedInterval (4251930974 / 1000000000000) (4251932297 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 0) <| besselDerivativeNearFromState (118469787421587 / 4000000000000) 0 (IntervalRat.scale (203 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-124711792900 / 1000000000000) (-124711775832 / 1000000000000), orderedInterval (79178490691 / 1000000000000) (79178507758 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 0) <| besselDerivativeNearFromState (321668518505761 / 4000000000000) 0 (IntervalRat.scale (203 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-41120560621 / 1000000000000) (-41120556228 / 1000000000000), orderedInterval (79158490975 / 1000000000000) (79158495368 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 0) <| besselDerivativeNearFromState (439210861732097 / 4000000000000) 0 (IntervalRat.scale (203 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-44935170343 / 1000000000000) (-44935170342 / 1000000000000), orderedInterval (-61266514707 / 1000000000000) (-61266514706 / 1000000000000)))) (orderedInterval (6679494588 / 1000000000000) (6679495016 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 0) <| besselDerivativeNearFromState (185715405749139 / 4000000000000) 0 (IntervalRat.scale (203 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-10252243747 / 1000000000000) (-10252243744 / 1000000000000), orderedInterval (-116540372511 / 1000000000000) (-116540372508 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 0) <| besselDerivativeNearFromState (754922813759219 / 4000000000000) 0 (IntervalRat.scale (203 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (49485809765 / 1000000000000) (49485809766 / 1000000000000), orderedInterval (30271434013 / 1000000000000) (30271434014 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 0) <| besselDerivativeNearFromState (504253453400221 / 4000000000000) 0 (IntervalRat.scale (203 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (65814797128 / 1000000000000) (65814797129 / 1000000000000), orderedInterval (26541621676 / 1000000000000) (26541621677 / 1000000000000)))) (orderedInterval (-16438638564 / 1000000000000) (-16438638535 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate222_chunkChecks0 :
    compactCertificate222.chunkChecks (0 : Fin 5) 0 9 = true :=
  compactCertificate222.chunkChecks_nine_of_three (0 : Fin 5) compactCertificate222_chunkChecks0_0
    compactCertificate222_chunkChecks0_1 compactCertificate222_chunkChecks0_2

theorem compactCertificate222_chunkChecks1_0 :
    compactCertificate222.chunkChecks (1 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 1) <| besselDerivativeNearFromState (203 / 2) 1 (IntervalRat.scale (203 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (77882361756 / 1000000000000) (77882362173 / 1000000000000), orderedInterval (-14749670105 / 1000000000000) (-14749669689 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 1) <| besselDerivativeNearFromState (299057762423903 / 4000000000000) 1 (IntervalRat.scale (203 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (13784346880 / 1000000000000) (13784346882 / 1000000000000), orderedInterval (91150249568 / 1000000000000) (91150249570 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 1) <| besselDerivativeNearFromState (96709135838399 / 800000000000) 1 (IntervalRat.scale (203 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (54583025918 / 1000000000000) (54583135707 / 1000000000000), orderedInterval (-48047822077 / 1000000000000) (-48047712288 / 1000000000000)))) (orderedInterval (-8578653751 / 1000000000000) (-8578645904 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 1) <| besselDerivativeNearFromState (87264309214621 / 4000000000000) 1 (IntervalRat.scale (203 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-97090409879 / 1000000000000) (-97090409878 / 1000000000000), orderedInterval (-138336892530 / 1000000000000) (-138336892529 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 1) <| besselDerivativeNearFromState (234404209290937 / 4000000000000) 1 (IntervalRat.scale (203 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (31392303514 / 1000000000000) (31392304191 / 1000000000000), orderedInterval (-99658322737 / 1000000000000) (-99658322060 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 1) <| besselDerivativeNearFromState (636453026337429 / 4000000000000) 1 (IntervalRat.scale (203 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (20098893818 / 1000000000000) (20098894272 / 1000000000000), orderedInterval (-60038972076 / 1000000000000) (-60038971622 / 1000000000000)))) (orderedInterval (4912613608 / 1000000000000) (4912613688 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 1) <| besselDerivativeNearFromState (468808418582077 / 4000000000000) 1 (IntervalRat.scale (203 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-72552757525 / 1000000000000) (-72552757097 / 1000000000000), orderedInterval (13265702256 / 1000000000000) (13265702684 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 1) <| besselDerivativeNearFromState (803311215823921 / 4000000000000) 1 (IntervalRat.scale (203 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (29459770685 / 1000000000000) (29459770686 / 1000000000000), orderedInterval (47906906953 / 1000000000000) (47906906954 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 1) <| besselDerivativeNearFromState (591715405749139 / 4000000000000) 1 (IntervalRat.scale (203 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-57181079105 / 1000000000000) (-57181079104 / 1000000000000), orderedInterval (-31960504760 / 1000000000000) (-31960504759 / 1000000000000)))) (orderedInterval (-4049407728 / 1000000000000) (-4049407717 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate222_chunkChecks1_1 :
    compactCertificate222.chunkChecks (1 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 1) <| besselDerivativeNearFromState (907843598864797 / 4000000000000) 1 (IntervalRat.scale (203 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (52951657689 / 1000000000000) (52951657751 / 1000000000000), orderedInterval (927704985 / 1000000000000) (927705048 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 1) <| besselDerivativeNearFromState (524143746186613 / 4000000000000) 1 (IntervalRat.scale (203 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-8794502166 / 1000000000000) (-8794502129 / 1000000000000), orderedInterval (69178702411 / 1000000000000) (69178702448 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 1) <| besselDerivativeNearFromState (930102275452217 / 4000000000000) 1 (IntervalRat.scale (203 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (38702545571 / 1000000000000) (38702545572 / 1000000000000), orderedInterval (35129855905 / 1000000000000) (35129855906 / 1000000000000)))) (orderedInterval (17689011552 / 1000000000000) (17689011665 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 1) <| besselDerivativeNearFromState (869022195421373 / 4000000000000) 1 (IntervalRat.scale (203 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-51709185973 / 1000000000000) (-51709185972 / 1000000000000), orderedInterval (-15894568337 / 1000000000000) (-15894568335 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 1) <| besselDerivativeNearFromState (620175244050509 / 4000000000000) 1 (IntervalRat.scale (203 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-60834225965 / 1000000000000) (-60834223084 / 1000000000000), orderedInterval (20326846970 / 1000000000000) (20326849851 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 1) <| besselDerivativeNearFromState (703212627872811 / 4000000000000) 1 (IntervalRat.scale (203 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (36831186465 / 1000000000000) (36831186466 / 1000000000000), orderedInterval (47483853609 / 1000000000000) (47483853610 / 1000000000000)))) (orderedInterval (3134144337 / 1000000000000) (3134144774 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 1) <| besselDerivativeNearFromState (586265375518459 / 4000000000000) 1 (IntervalRat.scale (203 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (19725929745 / 1000000000000) (19725930129 / 1000000000000), orderedInterval (-62951860720 / 1000000000000) (-62951860336 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 1) <| besselDerivativeNearFromState (517983238915639 / 4000000000000) 1 (IntervalRat.scale (203 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-69793092038 / 1000000000000) (-69793092028 / 1000000000000), orderedInterval (-6440978808 / 1000000000000) (-6440978799 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 1) <| besselDerivativeNearFromState (150131732004261 / 800000000000) 1 (IntervalRat.scale (203 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-2687692104 / 1000000000000) (-2687692097 / 1000000000000), orderedInterval (58188898230 / 1000000000000) (58188898237 / 1000000000000)))) (orderedInterval (2175179695 / 1000000000000) (2175179717 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate222_chunkChecks1_2 :
    compactCertificate222.chunkChecks (1 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 1) <| besselDerivativeNearFromState (415272271723967 / 4000000000000) 1 (IntervalRat.scale (203 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-62758689083 / 1000000000000) (-62758689082 / 1000000000000), orderedInterval (-46531478726 / 1000000000000) (-46531478725 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 1) <| besselDerivativeNearFromState (352030903754887 / 4000000000000) 1 (IntervalRat.scale (203 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (62595160806 / 1000000000000) (62595160807 / 1000000000000), orderedInterval (57224911423 / 1000000000000) (57224911424 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 1) <| besselDerivativeNearFromState (220284594250861 / 4000000000000) 1 (IntervalRat.scale (203 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-68800708773 / 1000000000000) (-68800668956 / 1000000000000), orderedInterval (83247228760 / 1000000000000) (83247268578 / 1000000000000)))) (orderedInterval (6272013676 / 1000000000000) (6272014404 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 1) <| besselDerivativeNearFromState (118469787421587 / 4000000000000) 1 (IntervalRat.scale (203 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-124711792900 / 1000000000000) (-124711775832 / 1000000000000), orderedInterval (79178490691 / 1000000000000) (79178507758 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 1) <| besselDerivativeNearFromState (321668518505761 / 4000000000000) 1 (IntervalRat.scale (203 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-41120560621 / 1000000000000) (-41120556228 / 1000000000000), orderedInterval (79158490975 / 1000000000000) (79158495368 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 1) <| besselDerivativeNearFromState (439210861732097 / 4000000000000) 1 (IntervalRat.scale (203 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-44935170343 / 1000000000000) (-44935170342 / 1000000000000), orderedInterval (-61266514707 / 1000000000000) (-61266514706 / 1000000000000)))) (orderedInterval (3230026028 / 1000000000000) (3230026210 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 1) <| besselDerivativeNearFromState (185715405749139 / 4000000000000) 1 (IntervalRat.scale (203 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-10252243747 / 1000000000000) (-10252243744 / 1000000000000), orderedInterval (-116540372511 / 1000000000000) (-116540372508 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 1) <| besselDerivativeNearFromState (754922813759219 / 4000000000000) 1 (IntervalRat.scale (203 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (49485809765 / 1000000000000) (49485809766 / 1000000000000), orderedInterval (30271434013 / 1000000000000) (30271434014 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 1) <| besselDerivativeNearFromState (504253453400221 / 4000000000000) 1 (IntervalRat.scale (203 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (65814797128 / 1000000000000) (65814797129 / 1000000000000), orderedInterval (26541621676 / 1000000000000) (26541621677 / 1000000000000)))) (orderedInterval (-11088308089 / 1000000000000) (-11088308049 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate222_chunkChecks1 :
    compactCertificate222.chunkChecks (1 : Fin 5) 0 9 = true :=
  compactCertificate222.chunkChecks_nine_of_three (1 : Fin 5) compactCertificate222_chunkChecks1_0
    compactCertificate222_chunkChecks1_1 compactCertificate222_chunkChecks1_2

theorem compactCertificate222_chunkChecks2_0 :
    compactCertificate222.chunkChecks (2 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 2) <| besselDerivativeNearFromState (203 / 2) 2 (IntervalRat.scale (203 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (77882361756 / 1000000000000) (77882362173 / 1000000000000), orderedInterval (-14749670105 / 1000000000000) (-14749669689 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 2) <| besselDerivativeNearFromState (299057762423903 / 4000000000000) 2 (IntervalRat.scale (203 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (13784346880 / 1000000000000) (13784346882 / 1000000000000), orderedInterval (91150249568 / 1000000000000) (91150249570 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 2) <| besselDerivativeNearFromState (96709135838399 / 800000000000) 2 (IntervalRat.scale (203 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (54583025918 / 1000000000000) (54583135707 / 1000000000000), orderedInterval (-48047822077 / 1000000000000) (-48047712288 / 1000000000000)))) (orderedInterval (-35398402660 / 1000000000000) (-35398393269 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 2) <| besselDerivativeNearFromState (87264309214621 / 4000000000000) 2 (IntervalRat.scale (203 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-97090409879 / 1000000000000) (-97090409878 / 1000000000000), orderedInterval (-138336892530 / 1000000000000) (-138336892529 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 2) <| besselDerivativeNearFromState (234404209290937 / 4000000000000) 2 (IntervalRat.scale (203 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (31392303514 / 1000000000000) (31392304191 / 1000000000000), orderedInterval (-99658322737 / 1000000000000) (-99658322060 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 2) <| besselDerivativeNearFromState (636453026337429 / 4000000000000) 2 (IntervalRat.scale (203 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (20098893818 / 1000000000000) (20098894272 / 1000000000000), orderedInterval (-60038972076 / 1000000000000) (-60038971622 / 1000000000000)))) (orderedInterval (3032102968 / 1000000000000) (3032103076 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 2) <| besselDerivativeNearFromState (468808418582077 / 4000000000000) 2 (IntervalRat.scale (203 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-72552757525 / 1000000000000) (-72552757097 / 1000000000000), orderedInterval (13265702256 / 1000000000000) (13265702684 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 2) <| besselDerivativeNearFromState (803311215823921 / 4000000000000) 2 (IntervalRat.scale (203 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (29459770685 / 1000000000000) (29459770686 / 1000000000000), orderedInterval (47906906953 / 1000000000000) (47906906954 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 2) <| besselDerivativeNearFromState (591715405749139 / 4000000000000) 2 (IntervalRat.scale (203 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-57181079105 / 1000000000000) (-57181079104 / 1000000000000), orderedInterval (-31960504760 / 1000000000000) (-31960504759 / 1000000000000)))) (orderedInterval (6532555688 / 1000000000000) (6532555706 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate222_chunkChecks2_1 :
    compactCertificate222.chunkChecks (2 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 2) <| besselDerivativeNearFromState (907843598864797 / 4000000000000) 2 (IntervalRat.scale (203 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (52951657689 / 1000000000000) (52951657751 / 1000000000000), orderedInterval (927704985 / 1000000000000) (927705048 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 2) <| besselDerivativeNearFromState (524143746186613 / 4000000000000) 2 (IntervalRat.scale (203 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-8794502166 / 1000000000000) (-8794502129 / 1000000000000), orderedInterval (69178702411 / 1000000000000) (69178702448 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 2) <| besselDerivativeNearFromState (930102275452217 / 4000000000000) 2 (IntervalRat.scale (203 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (38702545571 / 1000000000000) (38702545572 / 1000000000000), orderedInterval (35129855905 / 1000000000000) (35129855906 / 1000000000000)))) (orderedInterval (19081624065 / 1000000000000) (19081624305 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 2) <| besselDerivativeNearFromState (869022195421373 / 4000000000000) 2 (IntervalRat.scale (203 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-51709185973 / 1000000000000) (-51709185972 / 1000000000000), orderedInterval (-15894568337 / 1000000000000) (-15894568335 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 2) <| besselDerivativeNearFromState (620175244050509 / 4000000000000) 2 (IntervalRat.scale (203 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-60834225965 / 1000000000000) (-60834223084 / 1000000000000), orderedInterval (20326846970 / 1000000000000) (20326849851 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 2) <| besselDerivativeNearFromState (703212627872811 / 4000000000000) 2 (IntervalRat.scale (203 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (36831186465 / 1000000000000) (36831186466 / 1000000000000), orderedInterval (47483853609 / 1000000000000) (47483853610 / 1000000000000)))) (orderedInterval (9674255259 / 1000000000000) (9674255932 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 2) <| besselDerivativeNearFromState (586265375518459 / 4000000000000) 2 (IntervalRat.scale (203 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (19725929745 / 1000000000000) (19725930129 / 1000000000000), orderedInterval (-62951860720 / 1000000000000) (-62951860336 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 2) <| besselDerivativeNearFromState (517983238915639 / 4000000000000) 2 (IntervalRat.scale (203 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-69793092038 / 1000000000000) (-69793092028 / 1000000000000), orderedInterval (-6440978808 / 1000000000000) (-6440978799 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 2) <| besselDerivativeNearFromState (150131732004261 / 800000000000) 2 (IntervalRat.scale (203 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-2687692104 / 1000000000000) (-2687692097 / 1000000000000), orderedInterval (58188898230 / 1000000000000) (58188898237 / 1000000000000)))) (orderedInterval (-6762310095 / 1000000000000) (-6762310062 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate222_chunkChecks2_2 :
    compactCertificate222.chunkChecks (2 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 2) <| besselDerivativeNearFromState (415272271723967 / 4000000000000) 2 (IntervalRat.scale (203 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-62758689083 / 1000000000000) (-62758689082 / 1000000000000), orderedInterval (-46531478726 / 1000000000000) (-46531478725 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 2) <| besselDerivativeNearFromState (352030903754887 / 4000000000000) 2 (IntervalRat.scale (203 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (62595160806 / 1000000000000) (62595160807 / 1000000000000), orderedInterval (57224911423 / 1000000000000) (57224911424 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 2) <| besselDerivativeNearFromState (220284594250861 / 4000000000000) 2 (IntervalRat.scale (203 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-68800708773 / 1000000000000) (-68800668956 / 1000000000000), orderedInterval (83247228760 / 1000000000000) (83247268578 / 1000000000000)))) (orderedInterval (-7237056255 / 1000000000000) (-7237055843 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 2) <| besselDerivativeNearFromState (118469787421587 / 4000000000000) 2 (IntervalRat.scale (203 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-124711792900 / 1000000000000) (-124711775832 / 1000000000000), orderedInterval (79178490691 / 1000000000000) (79178507758 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 2) <| besselDerivativeNearFromState (321668518505761 / 4000000000000) 2 (IntervalRat.scale (203 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-41120560621 / 1000000000000) (-41120556228 / 1000000000000), orderedInterval (79158490975 / 1000000000000) (79158495368 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 2) <| besselDerivativeNearFromState (439210861732097 / 4000000000000) 2 (IntervalRat.scale (203 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-44935170343 / 1000000000000) (-44935170342 / 1000000000000), orderedInterval (-61266514707 / 1000000000000) (-61266514706 / 1000000000000)))) (orderedInterval (-4843722196 / 1000000000000) (-4843722093 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 2) <| besselDerivativeNearFromState (185715405749139 / 4000000000000) 2 (IntervalRat.scale (203 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-10252243747 / 1000000000000) (-10252243744 / 1000000000000), orderedInterval (-116540372511 / 1000000000000) (-116540372508 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 2) <| besselDerivativeNearFromState (754922813759219 / 4000000000000) 2 (IntervalRat.scale (203 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (49485809765 / 1000000000000) (49485809766 / 1000000000000), orderedInterval (30271434013 / 1000000000000) (30271434014 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 2) <| besselDerivativeNearFromState (504253453400221 / 4000000000000) 2 (IntervalRat.scale (203 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (65814797128 / 1000000000000) (65814797129 / 1000000000000), orderedInterval (26541621676 / 1000000000000) (26541621677 / 1000000000000)))) (orderedInterval (33098116069 / 1000000000000) (33098116129 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate222_chunkChecks2 :
    compactCertificate222.chunkChecks (2 : Fin 5) 0 9 = true :=
  compactCertificate222.chunkChecks_nine_of_three (2 : Fin 5) compactCertificate222_chunkChecks2_0
    compactCertificate222_chunkChecks2_1 compactCertificate222_chunkChecks2_2

theorem compactCertificate222_chunkChecks3_0 :
    compactCertificate222.chunkChecks (3 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 3) <| besselDerivativeNearFromState (203 / 2) 3 (IntervalRat.scale (203 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (77882361756 / 1000000000000) (77882362173 / 1000000000000), orderedInterval (-14749670105 / 1000000000000) (-14749669689 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 3) <| besselDerivativeNearFromState (299057762423903 / 4000000000000) 3 (IntervalRat.scale (203 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (13784346880 / 1000000000000) (13784346882 / 1000000000000), orderedInterval (91150249568 / 1000000000000) (91150249570 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 3) <| besselDerivativeNearFromState (96709135838399 / 800000000000) 3 (IntervalRat.scale (203 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (54583025918 / 1000000000000) (54583135707 / 1000000000000), orderedInterval (-48047822077 / 1000000000000) (-48047712288 / 1000000000000)))) (orderedInterval (10618002047 / 1000000000000) (10618013198 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 3) <| besselDerivativeNearFromState (87264309214621 / 4000000000000) 3 (IntervalRat.scale (203 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-97090409879 / 1000000000000) (-97090409878 / 1000000000000), orderedInterval (-138336892530 / 1000000000000) (-138336892529 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 3) <| besselDerivativeNearFromState (234404209290937 / 4000000000000) 3 (IntervalRat.scale (203 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (31392303514 / 1000000000000) (31392304191 / 1000000000000), orderedInterval (-99658322737 / 1000000000000) (-99658322060 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 3) <| besselDerivativeNearFromState (636453026337429 / 4000000000000) 3 (IntervalRat.scale (203 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (20098893818 / 1000000000000) (20098894272 / 1000000000000), orderedInterval (-60038972076 / 1000000000000) (-60038971622 / 1000000000000)))) (orderedInterval (-15786254081 / 1000000000000) (-15786253921 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 3) <| besselDerivativeNearFromState (468808418582077 / 4000000000000) 3 (IntervalRat.scale (203 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-72552757525 / 1000000000000) (-72552757097 / 1000000000000), orderedInterval (13265702256 / 1000000000000) (13265702684 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 3) <| besselDerivativeNearFromState (803311215823921 / 4000000000000) 3 (IntervalRat.scale (203 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (29459770685 / 1000000000000) (29459770686 / 1000000000000), orderedInterval (47906906953 / 1000000000000) (47906906954 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 3) <| besselDerivativeNearFromState (591715405749139 / 4000000000000) 3 (IntervalRat.scale (203 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-57181079105 / 1000000000000) (-57181079104 / 1000000000000), orderedInterval (-31960504760 / 1000000000000) (-31960504759 / 1000000000000)))) (orderedInterval (13772140421 / 1000000000000) (13772140455 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate222_chunkChecks3_1 :
    compactCertificate222.chunkChecks (3 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 3) <| besselDerivativeNearFromState (907843598864797 / 4000000000000) 3 (IntervalRat.scale (203 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (52951657689 / 1000000000000) (52951657751 / 1000000000000), orderedInterval (927704985 / 1000000000000) (927705048 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 3) <| besselDerivativeNearFromState (524143746186613 / 4000000000000) 3 (IntervalRat.scale (203 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-8794502166 / 1000000000000) (-8794502129 / 1000000000000), orderedInterval (69178702411 / 1000000000000) (69178702448 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 3) <| besselDerivativeNearFromState (930102275452217 / 4000000000000) 3 (IntervalRat.scale (203 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (38702545571 / 1000000000000) (38702545572 / 1000000000000), orderedInterval (35129855905 / 1000000000000) (35129855906 / 1000000000000)))) (orderedInterval (-69413780655 / 1000000000000) (-69413780130 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 3) <| besselDerivativeNearFromState (869022195421373 / 4000000000000) 3 (IntervalRat.scale (203 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-51709185973 / 1000000000000) (-51709185972 / 1000000000000), orderedInterval (-15894568337 / 1000000000000) (-15894568335 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 3) <| besselDerivativeNearFromState (620175244050509 / 4000000000000) 3 (IntervalRat.scale (203 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-60834225965 / 1000000000000) (-60834223084 / 1000000000000), orderedInterval (20326846970 / 1000000000000) (20326849851 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 3) <| besselDerivativeNearFromState (703212627872811 / 4000000000000) 3 (IntervalRat.scale (203 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (36831186465 / 1000000000000) (36831186466 / 1000000000000), orderedInterval (47483853609 / 1000000000000) (47483853610 / 1000000000000)))) (orderedInterval (-8511365176 / 1000000000000) (-8511364143 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 3) <| besselDerivativeNearFromState (586265375518459 / 4000000000000) 3 (IntervalRat.scale (203 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (19725929745 / 1000000000000) (19725930129 / 1000000000000), orderedInterval (-62951860720 / 1000000000000) (-62951860336 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 3) <| besselDerivativeNearFromState (517983238915639 / 4000000000000) 3 (IntervalRat.scale (203 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-69793092038 / 1000000000000) (-69793092028 / 1000000000000), orderedInterval (-6440978808 / 1000000000000) (-6440978799 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 3) <| besselDerivativeNearFromState (150131732004261 / 800000000000) 3 (IntervalRat.scale (203 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-2687692104 / 1000000000000) (-2687692097 / 1000000000000), orderedInterval (58188898230 / 1000000000000) (58188898237 / 1000000000000)))) (orderedInterval (-7926463774 / 1000000000000) (-7926463725 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate222_chunkChecks3_2 :
    compactCertificate222.chunkChecks (3 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 3) <| besselDerivativeNearFromState (415272271723967 / 4000000000000) 3 (IntervalRat.scale (203 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-62758689083 / 1000000000000) (-62758689082 / 1000000000000), orderedInterval (-46531478726 / 1000000000000) (-46531478725 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 3) <| besselDerivativeNearFromState (352030903754887 / 4000000000000) 3 (IntervalRat.scale (203 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (62595160806 / 1000000000000) (62595160807 / 1000000000000), orderedInterval (57224911423 / 1000000000000) (57224911424 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 3) <| besselDerivativeNearFromState (220284594250861 / 4000000000000) 3 (IntervalRat.scale (203 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-68800708773 / 1000000000000) (-68800668956 / 1000000000000), orderedInterval (83247228760 / 1000000000000) (83247268578 / 1000000000000)))) (orderedInterval (-6211103484 / 1000000000000) (-6211103251 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 3) <| besselDerivativeNearFromState (118469787421587 / 4000000000000) 3 (IntervalRat.scale (203 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-124711792900 / 1000000000000) (-124711775832 / 1000000000000), orderedInterval (79178490691 / 1000000000000) (79178507758 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 3) <| besselDerivativeNearFromState (321668518505761 / 4000000000000) 3 (IntervalRat.scale (203 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-41120560621 / 1000000000000) (-41120556228 / 1000000000000), orderedInterval (79158490975 / 1000000000000) (79158495368 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 3) <| besselDerivativeNearFromState (439210861732097 / 4000000000000) 3 (IntervalRat.scale (203 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-44935170343 / 1000000000000) (-44935170342 / 1000000000000), orderedInterval (-61266514707 / 1000000000000) (-61266514706 / 1000000000000)))) (orderedInterval (-4966973594 / 1000000000000) (-4966973524 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 3) <| besselDerivativeNearFromState (185715405749139 / 4000000000000) 3 (IntervalRat.scale (203 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-10252243747 / 1000000000000) (-10252243744 / 1000000000000), orderedInterval (-116540372511 / 1000000000000) (-116540372508 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 3) <| besselDerivativeNearFromState (754922813759219 / 4000000000000) 3 (IntervalRat.scale (203 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (49485809765 / 1000000000000) (49485809766 / 1000000000000), orderedInterval (30271434013 / 1000000000000) (30271434014 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 3) <| besselDerivativeNearFromState (504253453400221 / 4000000000000) 3 (IntervalRat.scale (203 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (65814797128 / 1000000000000) (65814797129 / 1000000000000), orderedInterval (26541621676 / 1000000000000) (26541621677 / 1000000000000)))) (orderedInterval (25122499868 / 1000000000000) (25122499959 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate222_chunkChecks3 :
    compactCertificate222.chunkChecks (3 : Fin 5) 0 9 = true :=
  compactCertificate222.chunkChecks_nine_of_three (3 : Fin 5) compactCertificate222_chunkChecks3_0
    compactCertificate222_chunkChecks3_1 compactCertificate222_chunkChecks3_2

theorem compactCertificate222_chunkChecks4_0 :
    compactCertificate222.chunkChecks (4 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 4) <| besselDerivativeNearFromState (203 / 2) 4 (IntervalRat.scale (203 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (77882361756 / 1000000000000) (77882362173 / 1000000000000), orderedInterval (-14749670105 / 1000000000000) (-14749669689 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 4) <| besselDerivativeNearFromState (299057762423903 / 4000000000000) 4 (IntervalRat.scale (203 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (13784346880 / 1000000000000) (13784346882 / 1000000000000), orderedInterval (91150249568 / 1000000000000) (91150249570 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 4) <| besselDerivativeNearFromState (96709135838399 / 800000000000) 4 (IntervalRat.scale (203 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (54583025918 / 1000000000000) (54583135707 / 1000000000000), orderedInterval (-48047822077 / 1000000000000) (-48047712288 / 1000000000000)))) (orderedInterval (37139694070 / 1000000000000) (37139707427 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 4) <| besselDerivativeNearFromState (87264309214621 / 4000000000000) 4 (IntervalRat.scale (203 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-97090409879 / 1000000000000) (-97090409878 / 1000000000000), orderedInterval (-138336892530 / 1000000000000) (-138336892529 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 4) <| besselDerivativeNearFromState (234404209290937 / 4000000000000) 4 (IntervalRat.scale (203 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (31392303514 / 1000000000000) (31392304191 / 1000000000000), orderedInterval (-99658322737 / 1000000000000) (-99658322060 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 4) <| besselDerivativeNearFromState (636453026337429 / 4000000000000) 4 (IntervalRat.scale (203 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (20098893818 / 1000000000000) (20098894272 / 1000000000000), orderedInterval (-60038972076 / 1000000000000) (-60038971622 / 1000000000000)))) (orderedInterval (-8187637751 / 1000000000000) (-8187637505 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 4) <| besselDerivativeNearFromState (468808418582077 / 4000000000000) 4 (IntervalRat.scale (203 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-72552757525 / 1000000000000) (-72552757097 / 1000000000000), orderedInterval (13265702256 / 1000000000000) (13265702684 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 4) <| besselDerivativeNearFromState (803311215823921 / 4000000000000) 4 (IntervalRat.scale (203 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (29459770685 / 1000000000000) (29459770686 / 1000000000000), orderedInterval (47906906953 / 1000000000000) (47906906954 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 4) <| besselDerivativeNearFromState (591715405749139 / 4000000000000) 4 (IntervalRat.scale (203 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-57181079105 / 1000000000000) (-57181079104 / 1000000000000), orderedInterval (-31960504760 / 1000000000000) (-31960504759 / 1000000000000)))) (orderedInterval (-20431954398 / 1000000000000) (-20431954337 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate222_chunkChecks4_1 :
    compactCertificate222.chunkChecks (4 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 4) <| besselDerivativeNearFromState (907843598864797 / 4000000000000) 4 (IntervalRat.scale (203 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (52951657689 / 1000000000000) (52951657751 / 1000000000000), orderedInterval (927704985 / 1000000000000) (927705048 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 4) <| besselDerivativeNearFromState (524143746186613 / 4000000000000) 4 (IntervalRat.scale (203 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-8794502166 / 1000000000000) (-8794502129 / 1000000000000), orderedInterval (69178702411 / 1000000000000) (69178702448 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 4) <| besselDerivativeNearFromState (930102275452217 / 4000000000000) 4 (IntervalRat.scale (203 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (38702545571 / 1000000000000) (38702545572 / 1000000000000), orderedInterval (35129855905 / 1000000000000) (35129855906 / 1000000000000)))) (orderedInterval (-84123626252 / 1000000000000) (-84123625092 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 4) <| besselDerivativeNearFromState (869022195421373 / 4000000000000) 4 (IntervalRat.scale (203 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-51709185973 / 1000000000000) (-51709185972 / 1000000000000), orderedInterval (-15894568337 / 1000000000000) (-15894568335 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 4) <| besselDerivativeNearFromState (620175244050509 / 4000000000000) 4 (IntervalRat.scale (203 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-60834225965 / 1000000000000) (-60834223084 / 1000000000000), orderedInterval (20326846970 / 1000000000000) (20326849851 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 4) <| besselDerivativeNearFromState (703212627872811 / 4000000000000) 4 (IntervalRat.scale (203 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (36831186465 / 1000000000000) (36831186466 / 1000000000000), orderedInterval (47483853609 / 1000000000000) (47483853610 / 1000000000000)))) (orderedInterval (-13234172256 / 1000000000000) (-13234170657 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 4) <| besselDerivativeNearFromState (586265375518459 / 4000000000000) 4 (IntervalRat.scale (203 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (19725929745 / 1000000000000) (19725930129 / 1000000000000), orderedInterval (-62951860720 / 1000000000000) (-62951860336 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 4) <| besselDerivativeNearFromState (517983238915639 / 4000000000000) 4 (IntervalRat.scale (203 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-69793092038 / 1000000000000) (-69793092028 / 1000000000000), orderedInterval (-6440978808 / 1000000000000) (-6440978799 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 4) <| besselDerivativeNearFromState (150131732004261 / 800000000000) 4 (IntervalRat.scale (203 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-2687692104 / 1000000000000) (-2687692097 / 1000000000000), orderedInterval (58188898230 / 1000000000000) (58188898237 / 1000000000000)))) (orderedInterval (10923782530 / 1000000000000) (10923782605 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate222_chunkChecks4_2 :
    compactCertificate222.chunkChecks (4 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 4) <| besselDerivativeNearFromState (415272271723967 / 4000000000000) 4 (IntervalRat.scale (203 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-62758689083 / 1000000000000) (-62758689082 / 1000000000000), orderedInterval (-46531478726 / 1000000000000) (-46531478725 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 4) <| besselDerivativeNearFromState (352030903754887 / 4000000000000) 4 (IntervalRat.scale (203 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (62595160806 / 1000000000000) (62595160807 / 1000000000000), orderedInterval (57224911423 / 1000000000000) (57224911424 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 4) <| besselDerivativeNearFromState (220284594250861 / 4000000000000) 4 (IntervalRat.scale (203 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-68800708773 / 1000000000000) (-68800668956 / 1000000000000), orderedInterval (83247228760 / 1000000000000) (83247268578 / 1000000000000)))) (orderedInterval (8908265726 / 1000000000000) (8908265865 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 4) <| besselDerivativeNearFromState (118469787421587 / 4000000000000) 4 (IntervalRat.scale (203 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-124711792900 / 1000000000000) (-124711775832 / 1000000000000), orderedInterval (79178490691 / 1000000000000) (79178507758 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 4) <| besselDerivativeNearFromState (321668518505761 / 4000000000000) 4 (IntervalRat.scale (203 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-41120560621 / 1000000000000) (-41120556228 / 1000000000000), orderedInterval (79158490975 / 1000000000000) (79158495368 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 4) <| besselDerivativeNearFromState (439210861732097 / 4000000000000) 4 (IntervalRat.scale (203 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-44935170343 / 1000000000000) (-44935170342 / 1000000000000), orderedInterval (-61266514707 / 1000000000000) (-61266514706 / 1000000000000)))) (orderedInterval (5198224226 / 1000000000000) (5198224282 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 4) <| besselDerivativeNearFromState (185715405749139 / 4000000000000) 4 (IntervalRat.scale (203 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-10252243747 / 1000000000000) (-10252243744 / 1000000000000), orderedInterval (-116540372511 / 1000000000000) (-116540372508 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 4) <| besselDerivativeNearFromState (754922813759219 / 4000000000000) 4 (IntervalRat.scale (203 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (49485809765 / 1000000000000) (49485809766 / 1000000000000), orderedInterval (30271434013 / 1000000000000) (30271434014 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 4) <| besselDerivativeNearFromState (504253453400221 / 4000000000000) 4 (IntervalRat.scale (203 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (65814797128 / 1000000000000) (65814797129 / 1000000000000), orderedInterval (26541621676 / 1000000000000) (26541621677 / 1000000000000)))) (orderedInterval (-78031088373 / 1000000000000) (-78031088226 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate222_chunkChecks4 :
    compactCertificate222.chunkChecks (4 : Fin 5) 0 9 = true :=
  compactCertificate222.chunkChecks_nine_of_three (4 : Fin 5) compactCertificate222_chunkChecks4_0
    compactCertificate222_chunkChecks4_1 compactCertificate222_chunkChecks4_2

theorem compactCertificate222_chunks :
    ∀ r : Fin 5, ∀ b, compactCertificate222.chunkCheck r b = true :=
  compactCertificate222.chunkChecks_all (by
    intro r
    fin_cases r
    · exact compactCertificate222_chunkChecks0
    · exact compactCertificate222_chunkChecks1
    · exact compactCertificate222_chunkChecks2
    · exact compactCertificate222_chunkChecks3
    · exact compactCertificate222_chunkChecks4)

theorem compactCertificate222_coefficient0 :
    compactCertificate222.coefficientCheck (0 : Fin 5) = true := by
  norm_num [CompactCertificate.coefficientCheck, intervalFinSumHull,
    compactCertificate222, rationalIntervalSubset, orderedInterval, Fin.sum_univ_succ]

theorem compactCertificate222_coefficient1 :
    compactCertificate222.coefficientCheck (1 : Fin 5) = true := by
  norm_num [CompactCertificate.coefficientCheck, intervalFinSumHull,
    compactCertificate222, rationalIntervalSubset, orderedInterval, Fin.sum_univ_succ]

theorem compactCertificate222_coefficient2 :
    compactCertificate222.coefficientCheck (2 : Fin 5) = true := by
  norm_num [CompactCertificate.coefficientCheck, intervalFinSumHull,
    compactCertificate222, rationalIntervalSubset, orderedInterval, Fin.sum_univ_succ]

theorem compactCertificate222_coefficient3 :
    compactCertificate222.coefficientCheck (3 : Fin 5) = true := by
  norm_num [CompactCertificate.coefficientCheck, intervalFinSumHull,
    compactCertificate222, rationalIntervalSubset, orderedInterval, Fin.sum_univ_succ]

theorem compactCertificate222_coefficient4 :
    compactCertificate222.coefficientCheck (4 : Fin 5) = true := by
  norm_num [CompactCertificate.coefficientCheck, intervalFinSumHull,
    compactCertificate222, rationalIntervalSubset, orderedInterval, Fin.sum_univ_succ]

theorem compactCertificate222_coefficients : ∀ r : Fin 5,
    compactCertificate222.coefficientCheck r = true := by
  intro r
  fin_cases r
  · exact compactCertificate222_coefficient0
  · exact compactCertificate222_coefficient1
  · exact compactCertificate222_coefficient2
  · exact compactCertificate222_coefficient3
  · exact compactCertificate222_coefficient4

theorem compactCertificate222_lower : (1 : ℚ) ≤ compactCertificate222.output.lo := by
  norm_num [CompactCertificate.output, CompactCertificate.interval,
    CompactCertificate.coefficientTargetNat, compactCertificate222, dualConstant,
    intervalTaylorSum, intervalPow, intervalSub, intervalMaxAbs, widenInterval,
    rationalErrorInterval, orderedInterval, IntervalRat.add, IntervalRat.mul, IntervalRat.scale,
    IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4]

theorem compactCertificate222_proves {t : ℝ} (ht : t ∈ compactCertificate222.interval) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t :=
  compactCertificate222.proves compactCertificate222_states compactCertificate222_chunks
    compactCertificate222_coefficients compactCertificate222_lower ht

end Erdos232
