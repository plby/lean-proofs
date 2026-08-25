/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, OpenAI Codex
-/
import ErdosProblems.Erdos232.CompactBase

open LeanCert.Core
namespace Erdos232

def compactCertificate231 : CompactCertificate where
  left := 108
  right := 109
  center := 217 / 2
  grid := fun i =>
    match i.val with
    | 0 => 35
    | 1 => 25
    | 2 => 41
    | 3 => 7
    | 4 => 20
    | 5 => 54
    | 6 => 40
    | 7 => 68
    | 8 => 50
    | 9 => 77
    | 10 => 45
    | 11 => 79
    | 12 => 74
    | 13 => 53
    | 14 => 60
    | 15 => 50
    | 16 => 44
    | 17 => 64
    | 18 => 35
    | 19 => 30
    | 20 => 19
    | 21 => 10
    | 22 => 27
    | 23 => 37
    | 24 => 16
    | 25 => 64
    | _ => 43
  point := fun i =>
    match i.val with
    | 0 => 217 / 2
    | 1 => 319682435694517 / 4000000000000
    | 2 => 103378731413461 / 800000000000
    | 3 => 93282537436319 / 4000000000000
    | 4 => 250570016828243 / 4000000000000
    | 5 => 680346338498631 / 4000000000000
    | 6 => 501140033656703 / 4000000000000
    | 7 => 858711989329019 / 4000000000000
    | 8 => 632523364766321 / 4000000000000
    | 9 => 970453502234783 / 4000000000000
    | 10 => 560291590751207 / 4000000000000
    | 11 => 994247259966163 / 4000000000000
    | 12 => 928954760622847 / 4000000000000
    | 13 => 662945950536751 / 4000000000000
    | 14 => 751710050484729 / 4000000000000
    | 15 => 626697470381801 / 4000000000000
    | 16 => 553706220909821 / 4000000000000
    | 17 => 160485644556279 / 800000000000
    | 18 => 443911738739413 / 4000000000000
    | 19 => 376308897117293 / 4000000000000
    | 20 => 235476635233679 / 4000000000000
    | 21 => 126640117588593 / 4000000000000
    | 22 => 343852554264779 / 4000000000000
    | 23 => 469501265989483 / 4000000000000
    | 24 => 198523364766321 / 4000000000000
    | 25 => 806986456087441 / 4000000000000
    | _ => 539029553634719 / 4000000000000
  state := fun i =>
    match i.val with
    | 0 => (orderedInterval (47656679352 / 1000000000000) (47656704846 / 1000000000000), orderedInterval (-60188924341 / 1000000000000) (-60188898848 / 1000000000000))
    | 1 => (orderedInterval (-73970415229 / 1000000000000) (-73970384402 / 1000000000000), orderedInterval (50402440733 / 1000000000000) (50402471560 / 1000000000000))
    | 2 => (orderedInterval (-65483257181 / 1000000000000) (-65483257180 / 1000000000000), orderedInterval (-25013616415 / 1000000000000) (-25013616414 / 1000000000000))
    | 3 => (orderedInterval (-141804298856 / 1000000000000) (-141804284341 / 1000000000000), orderedInterval (87815936808 / 1000000000000) (87815951322 / 1000000000000))
    | 4 => (orderedInterval (56425241684 / 1000000000000) (56425241685 / 1000000000000), orderedInterval (83090407494 / 1000000000000) (83090407495 / 1000000000000))
    | 5 => (orderedInterval (57562858424 / 1000000000000) (57562858425 / 1000000000000), orderedInterval (20553253909 / 1000000000000) (20553253910 / 1000000000000))
    | 6 => (orderedInterval (28133055497 / 1000000000000) (28133055498 / 1000000000000), orderedInterval (65385293104 / 1000000000000) (65385293105 / 1000000000000))
    | 7 => (orderedInterval (52573335327 / 1000000000000) (52573337490 / 1000000000000), orderedInterval (-14317547807 / 1000000000000) (-14317545643 / 1000000000000))
    | 8 => (orderedInterval (61234655286 / 1000000000000) (61234656875 / 1000000000000), orderedInterval (-16813026552 / 1000000000000) (-16813024963 / 1000000000000))
    | 9 => (orderedInterval (-51080366654 / 1000000000000) (-51080366623 / 1000000000000), orderedInterval (-3741807608 / 1000000000000) (-3741807577 / 1000000000000))
    | 10 => (orderedInterval (33161545083 / 1000000000000) (33161549678 / 1000000000000), orderedInterval (-58814576349 / 1000000000000) (-58814571754 / 1000000000000))
    | 11 => (orderedInterval (-46415899286 / 1000000000000) (-46415899285 / 1000000000000), orderedInterval (-20075266513 / 1000000000000) (-20075266512 / 1000000000000))
    | 12 => (orderedInterval (27173713236 / 1000000000000) (27173713237 / 1000000000000), orderedInterval (44694403629 / 1000000000000) (44694403630 / 1000000000000))
    | 13 => (orderedInterval (-1036265500 / 1000000000000) (-1036265496 / 1000000000000), orderedInterval (-61965414482 / 1000000000000) (-61965414478 / 1000000000000))
    | 14 => (orderedInterval (12513301690 / 1000000000000) (12513301692 / 1000000000000), orderedInterval (56808678635 / 1000000000000) (56808678636 / 1000000000000))
    | 15 => (orderedInterval (23604635205 / 1000000000000) (23604635206 / 1000000000000), orderedInterval (59137565596 / 1000000000000) (59137565597 / 1000000000000))
    | 16 => (orderedInterval (56357343441 / 1000000000000) (56357343442 / 1000000000000), orderedInterval (37516590123 / 1000000000000) (37516590124 / 1000000000000))
    | 17 => (orderedInterval (18249179043 / 1000000000000) (18249179044 / 1000000000000), orderedInterval (53250310345 / 1000000000000) (53250310346 / 1000000000000))
    | 18 => (orderedInterval (-73645474160 / 1000000000000) (-73645473307 / 1000000000000), orderedInterval (18016419103 / 1000000000000) (18016419956 / 1000000000000))
    | 19 => (orderedInterval (47361388204 / 1000000000000) (47361388205 / 1000000000000), orderedInterval (67008402863 / 1000000000000) (67008402864 / 1000000000000))
    | 20 => (orderedInterval (3932608186 / 1000000000000) (3932608202 / 1000000000000), orderedInterval (-103951977356 / 1000000000000) (-103951977340 / 1000000000000))
    | 21 => (orderedInterval (121234031158 / 1000000000000) (121234031159 / 1000000000000), orderedInterval (71632776574 / 1000000000000) (71632776575 / 1000000000000))
    | 22 => (orderedInterval (-80741128944 / 1000000000000) (-80741126084 / 1000000000000), orderedInterval (30243839562 / 1000000000000) (30243842422 / 1000000000000))
    | 23 => (orderedInterval (-69183018286 / 1000000000000) (-69183015019 / 1000000000000), orderedInterval (25542841197 / 1000000000000) (25542844464 / 1000000000000))
    | 24 => (orderedInterval (16727208475 / 1000000000000) (16727208476 / 1000000000000), orderedInterval (111849012045 / 1000000000000) (111849012047 / 1000000000000))
    | 25 => (orderedInterval (55885953713 / 1000000000000) (55885953728 / 1000000000000), orderedInterval (5544099061 / 1000000000000) (5544099076 / 1000000000000))
    | _ => (orderedInterval (-30104979738 / 1000000000000) (-30104979737 / 1000000000000), orderedInterval (-61677476349 / 1000000000000) (-61677476348 / 1000000000000))
  chunkTarget := fun r b =>
    match r.val with
    | 0 =>
      match b.val with
      | 0 => orderedInterval (14357546424 / 1000000000000) (14357556825 / 1000000000000)
      | 1 => orderedInterval (-493462909 / 1000000000000) (-493462738 / 1000000000000)
      | 2 => orderedInterval (-141651275 / 1000000000000) (-141651163 / 1000000000000)
      | 3 => orderedInterval (4935068421 / 1000000000000) (4935068811 / 1000000000000)
      | 4 => orderedInterval (-651886139 / 1000000000000) (-651886125 / 1000000000000)
      | 5 => orderedInterval (-2485313890 / 1000000000000) (-2485313878 / 1000000000000)
      | 6 => orderedInterval (9222729192 / 1000000000000) (9222729357 / 1000000000000)
      | 7 => orderedInterval (4895270303 / 1000000000000) (4895270632 / 1000000000000)
      | _ => orderedInterval (1200113934 / 1000000000000) (1200113967 / 1000000000000)
    | 1 =>
      match b.val with
      | 0 => orderedInterval (-25259019755 / 1000000000000) (-25259009429 / 1000000000000)
      | 1 => orderedInterval (-743711523 / 1000000000000) (-743711473 / 1000000000000)
      | 2 => orderedInterval (281562349 / 1000000000000) (281562549 / 1000000000000)
      | 3 => orderedInterval (-10676820566 / 1000000000000) (-10676820024 / 1000000000000)
      | 4 => orderedInterval (-11175734364 / 1000000000000) (-11175734341 / 1000000000000)
      | 5 => orderedInterval (767830050 / 1000000000000) (767830066 / 1000000000000)
      | 6 => orderedInterval (-8071163019 / 1000000000000) (-8071162853 / 1000000000000)
      | 7 => orderedInterval (-3047285549 / 1000000000000) (-3047285214 / 1000000000000)
      | _ => orderedInterval (13842148620 / 1000000000000) (13842148666 / 1000000000000)
    | 2 =>
      match b.val with
      | 0 => orderedInterval (-12831979998 / 1000000000000) (-12831969631 / 1000000000000)
      | 1 => orderedInterval (9305146081 / 1000000000000) (9305146110 / 1000000000000)
      | 2 => orderedInterval (3202132308 / 1000000000000) (3202132672 / 1000000000000)
      | 3 => orderedInterval (-14749332713 / 1000000000000) (-14749331922 / 1000000000000)
      | 4 => orderedInterval (2769178101 / 1000000000000) (2769178138 / 1000000000000)
      | 5 => orderedInterval (3076895500 / 1000000000000) (3076895523 / 1000000000000)
      | 6 => orderedInterval (-10267302929 / 1000000000000) (-10267302760 / 1000000000000)
      | 7 => orderedInterval (-7136151472 / 1000000000000) (-7136151123 / 1000000000000)
      | _ => orderedInterval (6866694101 / 1000000000000) (6866694169 / 1000000000000)
    | 3 =>
      match b.val with
      | 0 => orderedInterval (26264952585 / 1000000000000) (26264962909 / 1000000000000)
      | 1 => orderedInterval (4968482057 / 1000000000000) (4968482090 / 1000000000000)
      | 2 => orderedInterval (-2192266903 / 1000000000000) (-2192266229 / 1000000000000)
      | 3 => orderedInterval (36389278588 / 1000000000000) (36389279808 / 1000000000000)
      | 4 => orderedInterval (30264973148 / 1000000000000) (30264973209 / 1000000000000)
      | 5 => orderedInterval (-6243402377 / 1000000000000) (-6243402341 / 1000000000000)
      | 6 => orderedInterval (6189432261 / 1000000000000) (6189432433 / 1000000000000)
      | 7 => orderedInterval (2917946012 / 1000000000000) (2917946377 / 1000000000000)
      | _ => orderedInterval (-19396543862 / 1000000000000) (-19396543756 / 1000000000000)
    | _ =>
      match b.val with
      | 0 => orderedInterval (10469619161 / 1000000000000) (10469629551 / 1000000000000)
      | 1 => orderedInterval (-24570718725 / 1000000000000) (-24570718676 / 1000000000000)
      | 2 => orderedInterval (-18134598129 / 1000000000000) (-18134596858 / 1000000000000)
      | 3 => orderedInterval (51322170635 / 1000000000000) (51322172668 / 1000000000000)
      | 4 => orderedInterval (-11958284653 / 1000000000000) (-11958284547 / 1000000000000)
      | 5 => orderedInterval (-1784146586 / 1000000000000) (-1784146530 / 1000000000000)
      | 6 => orderedInterval (11269451527 / 1000000000000) (11269451703 / 1000000000000)
      | 7 => orderedInterval (7912824287 / 1000000000000) (7912824675 / 1000000000000)
      | _ => orderedInterval (-40577136016 / 1000000000000) (-40577135845 / 1000000000000)
  coefficientTarget := fun i =>
    match i.val with
    | 0 => orderedInterval (30838414061 / 1000000000000) (30838425688 / 1000000000000)
    | 1 => orderedInterval (-44082193757 / 1000000000000) (-44082182053 / 1000000000000)
    | 2 => orderedInterval (-19764721021 / 1000000000000) (-19764708824 / 1000000000000)
    | 3 => orderedInterval (79162851509 / 1000000000000) (79162864500 / 1000000000000)
    | _ => orderedInterval (-16050818499 / 1000000000000) (-16050803859 / 1000000000000)

theorem compactCertificate231_stateChecks0 :
    compactCertificate231.stateChecks 0 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 35 12 (217 / 2)) (orderedInterval (47656679352 / 1000000000000) (47656704846 / 1000000000000), orderedInterval (-60188924341 / 1000000000000) (-60188898848 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 25 12 (319682435694517 / 4000000000000)) (orderedInterval (-73970415229 / 1000000000000) (-73970384402 / 1000000000000), orderedInterval (50402440733 / 1000000000000) (50402471560 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 41 12 (103378731413461 / 800000000000)) (orderedInterval (-65483257181 / 1000000000000) (-65483257180 / 1000000000000), orderedInterval (-25013616415 / 1000000000000) (-25013616414 / 1000000000000))) = true
  norm_num [besselStateAtRationalPoint, besselIntervalStepZero,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, besselZeroTransition,
    besselInitial, besselGridStateAt, besselGridStateBlock00, besselGridStateBlock01,
    besselGridStateBlock02, besselGridStateBlock03, besselGridStateBlock04,
    besselGridStateBlock05, besselGridStateBlock06, besselGridStateBlock07,
    besselGridStateBlock08, besselGridStateBlock09, besselGridStateBlock10,
    besselGridStateBlock11, besselGridStateBlock12, besselGridStateBlock13,
    besselGridStateBlock14, besselGridState007, besselGridState010, besselGridState016, besselGridState019, besselGridState020, besselGridState025, besselGridState027, besselGridState030, besselGridState035, besselGridState037, besselGridState040, besselGridState041, besselGridState043, besselGridState044, besselGridState045, besselGridState050, besselGridState053, besselGridState054, besselGridState060, besselGridState064, besselGridState068, besselGridState074, besselGridState077, besselGridState079, besselStateSubset, linearInterval, widenInterval,
    rationalErrorInterval, rationalIntervalSubset, orderedInterval, Finset.sum_range_succ,
    IntervalRat.add, IntervalRat.mul, IntervalRat.scale, IntervalRat.singleton]

theorem compactCertificate231_stateChecks1 :
    compactCertificate231.stateChecks 3 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 7 12 (93282537436319 / 4000000000000)) (orderedInterval (-141804298856 / 1000000000000) (-141804284341 / 1000000000000), orderedInterval (87815936808 / 1000000000000) (87815951322 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 20 12 (250570016828243 / 4000000000000)) (orderedInterval (56425241684 / 1000000000000) (56425241685 / 1000000000000), orderedInterval (83090407494 / 1000000000000) (83090407495 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 54 12 (680346338498631 / 4000000000000)) (orderedInterval (57562858424 / 1000000000000) (57562858425 / 1000000000000), orderedInterval (20553253909 / 1000000000000) (20553253910 / 1000000000000))) = true
  norm_num [besselStateAtRationalPoint, besselIntervalStepZero,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, besselZeroTransition,
    besselInitial, besselGridStateAt, besselGridStateBlock00, besselGridStateBlock01,
    besselGridStateBlock02, besselGridStateBlock03, besselGridStateBlock04,
    besselGridStateBlock05, besselGridStateBlock06, besselGridStateBlock07,
    besselGridStateBlock08, besselGridStateBlock09, besselGridStateBlock10,
    besselGridStateBlock11, besselGridStateBlock12, besselGridStateBlock13,
    besselGridStateBlock14, besselGridState007, besselGridState010, besselGridState016, besselGridState019, besselGridState020, besselGridState025, besselGridState027, besselGridState030, besselGridState035, besselGridState037, besselGridState040, besselGridState041, besselGridState043, besselGridState044, besselGridState045, besselGridState050, besselGridState053, besselGridState054, besselGridState060, besselGridState064, besselGridState068, besselGridState074, besselGridState077, besselGridState079, besselStateSubset, linearInterval, widenInterval,
    rationalErrorInterval, rationalIntervalSubset, orderedInterval, Finset.sum_range_succ,
    IntervalRat.add, IntervalRat.mul, IntervalRat.scale, IntervalRat.singleton]

theorem compactCertificate231_stateChecks2 :
    compactCertificate231.stateChecks 6 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 40 12 (501140033656703 / 4000000000000)) (orderedInterval (28133055497 / 1000000000000) (28133055498 / 1000000000000), orderedInterval (65385293104 / 1000000000000) (65385293105 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 68 12 (858711989329019 / 4000000000000)) (orderedInterval (52573335327 / 1000000000000) (52573337490 / 1000000000000), orderedInterval (-14317547807 / 1000000000000) (-14317545643 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 50 12 (632523364766321 / 4000000000000)) (orderedInterval (61234655286 / 1000000000000) (61234656875 / 1000000000000), orderedInterval (-16813026552 / 1000000000000) (-16813024963 / 1000000000000))) = true
  norm_num [besselStateAtRationalPoint, besselIntervalStepZero,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, besselZeroTransition,
    besselInitial, besselGridStateAt, besselGridStateBlock00, besselGridStateBlock01,
    besselGridStateBlock02, besselGridStateBlock03, besselGridStateBlock04,
    besselGridStateBlock05, besselGridStateBlock06, besselGridStateBlock07,
    besselGridStateBlock08, besselGridStateBlock09, besselGridStateBlock10,
    besselGridStateBlock11, besselGridStateBlock12, besselGridStateBlock13,
    besselGridStateBlock14, besselGridState007, besselGridState010, besselGridState016, besselGridState019, besselGridState020, besselGridState025, besselGridState027, besselGridState030, besselGridState035, besselGridState037, besselGridState040, besselGridState041, besselGridState043, besselGridState044, besselGridState045, besselGridState050, besselGridState053, besselGridState054, besselGridState060, besselGridState064, besselGridState068, besselGridState074, besselGridState077, besselGridState079, besselStateSubset, linearInterval, widenInterval,
    rationalErrorInterval, rationalIntervalSubset, orderedInterval, Finset.sum_range_succ,
    IntervalRat.add, IntervalRat.mul, IntervalRat.scale, IntervalRat.singleton]

theorem compactCertificate231_stateChecks3 :
    compactCertificate231.stateChecks 9 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 77 12 (970453502234783 / 4000000000000)) (orderedInterval (-51080366654 / 1000000000000) (-51080366623 / 1000000000000), orderedInterval (-3741807608 / 1000000000000) (-3741807577 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 45 12 (560291590751207 / 4000000000000)) (orderedInterval (33161545083 / 1000000000000) (33161549678 / 1000000000000), orderedInterval (-58814576349 / 1000000000000) (-58814571754 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 79 12 (994247259966163 / 4000000000000)) (orderedInterval (-46415899286 / 1000000000000) (-46415899285 / 1000000000000), orderedInterval (-20075266513 / 1000000000000) (-20075266512 / 1000000000000))) = true
  norm_num [besselStateAtRationalPoint, besselIntervalStepZero,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, besselZeroTransition,
    besselInitial, besselGridStateAt, besselGridStateBlock00, besselGridStateBlock01,
    besselGridStateBlock02, besselGridStateBlock03, besselGridStateBlock04,
    besselGridStateBlock05, besselGridStateBlock06, besselGridStateBlock07,
    besselGridStateBlock08, besselGridStateBlock09, besselGridStateBlock10,
    besselGridStateBlock11, besselGridStateBlock12, besselGridStateBlock13,
    besselGridStateBlock14, besselGridState007, besselGridState010, besselGridState016, besselGridState019, besselGridState020, besselGridState025, besselGridState027, besselGridState030, besselGridState035, besselGridState037, besselGridState040, besselGridState041, besselGridState043, besselGridState044, besselGridState045, besselGridState050, besselGridState053, besselGridState054, besselGridState060, besselGridState064, besselGridState068, besselGridState074, besselGridState077, besselGridState079, besselStateSubset, linearInterval, widenInterval,
    rationalErrorInterval, rationalIntervalSubset, orderedInterval, Finset.sum_range_succ,
    IntervalRat.add, IntervalRat.mul, IntervalRat.scale, IntervalRat.singleton]

theorem compactCertificate231_stateChecks4 :
    compactCertificate231.stateChecks 12 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 74 12 (928954760622847 / 4000000000000)) (orderedInterval (27173713236 / 1000000000000) (27173713237 / 1000000000000), orderedInterval (44694403629 / 1000000000000) (44694403630 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 53 12 (662945950536751 / 4000000000000)) (orderedInterval (-1036265500 / 1000000000000) (-1036265496 / 1000000000000), orderedInterval (-61965414482 / 1000000000000) (-61965414478 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 60 12 (751710050484729 / 4000000000000)) (orderedInterval (12513301690 / 1000000000000) (12513301692 / 1000000000000), orderedInterval (56808678635 / 1000000000000) (56808678636 / 1000000000000))) = true
  norm_num [besselStateAtRationalPoint, besselIntervalStepZero,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, besselZeroTransition,
    besselInitial, besselGridStateAt, besselGridStateBlock00, besselGridStateBlock01,
    besselGridStateBlock02, besselGridStateBlock03, besselGridStateBlock04,
    besselGridStateBlock05, besselGridStateBlock06, besselGridStateBlock07,
    besselGridStateBlock08, besselGridStateBlock09, besselGridStateBlock10,
    besselGridStateBlock11, besselGridStateBlock12, besselGridStateBlock13,
    besselGridStateBlock14, besselGridState007, besselGridState010, besselGridState016, besselGridState019, besselGridState020, besselGridState025, besselGridState027, besselGridState030, besselGridState035, besselGridState037, besselGridState040, besselGridState041, besselGridState043, besselGridState044, besselGridState045, besselGridState050, besselGridState053, besselGridState054, besselGridState060, besselGridState064, besselGridState068, besselGridState074, besselGridState077, besselGridState079, besselStateSubset, linearInterval, widenInterval,
    rationalErrorInterval, rationalIntervalSubset, orderedInterval, Finset.sum_range_succ,
    IntervalRat.add, IntervalRat.mul, IntervalRat.scale, IntervalRat.singleton]

theorem compactCertificate231_stateChecks5 :
    compactCertificate231.stateChecks 15 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 50 12 (626697470381801 / 4000000000000)) (orderedInterval (23604635205 / 1000000000000) (23604635206 / 1000000000000), orderedInterval (59137565596 / 1000000000000) (59137565597 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 44 12 (553706220909821 / 4000000000000)) (orderedInterval (56357343441 / 1000000000000) (56357343442 / 1000000000000), orderedInterval (37516590123 / 1000000000000) (37516590124 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 64 12 (160485644556279 / 800000000000)) (orderedInterval (18249179043 / 1000000000000) (18249179044 / 1000000000000), orderedInterval (53250310345 / 1000000000000) (53250310346 / 1000000000000))) = true
  norm_num [besselStateAtRationalPoint, besselIntervalStepZero,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, besselZeroTransition,
    besselInitial, besselGridStateAt, besselGridStateBlock00, besselGridStateBlock01,
    besselGridStateBlock02, besselGridStateBlock03, besselGridStateBlock04,
    besselGridStateBlock05, besselGridStateBlock06, besselGridStateBlock07,
    besselGridStateBlock08, besselGridStateBlock09, besselGridStateBlock10,
    besselGridStateBlock11, besselGridStateBlock12, besselGridStateBlock13,
    besselGridStateBlock14, besselGridState007, besselGridState010, besselGridState016, besselGridState019, besselGridState020, besselGridState025, besselGridState027, besselGridState030, besselGridState035, besselGridState037, besselGridState040, besselGridState041, besselGridState043, besselGridState044, besselGridState045, besselGridState050, besselGridState053, besselGridState054, besselGridState060, besselGridState064, besselGridState068, besselGridState074, besselGridState077, besselGridState079, besselStateSubset, linearInterval, widenInterval,
    rationalErrorInterval, rationalIntervalSubset, orderedInterval, Finset.sum_range_succ,
    IntervalRat.add, IntervalRat.mul, IntervalRat.scale, IntervalRat.singleton]

theorem compactCertificate231_stateChecks6 :
    compactCertificate231.stateChecks 18 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 35 12 (443911738739413 / 4000000000000)) (orderedInterval (-73645474160 / 1000000000000) (-73645473307 / 1000000000000), orderedInterval (18016419103 / 1000000000000) (18016419956 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 30 12 (376308897117293 / 4000000000000)) (orderedInterval (47361388204 / 1000000000000) (47361388205 / 1000000000000), orderedInterval (67008402863 / 1000000000000) (67008402864 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 19 12 (235476635233679 / 4000000000000)) (orderedInterval (3932608186 / 1000000000000) (3932608202 / 1000000000000), orderedInterval (-103951977356 / 1000000000000) (-103951977340 / 1000000000000))) = true
  norm_num [besselStateAtRationalPoint, besselIntervalStepZero,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, besselZeroTransition,
    besselInitial, besselGridStateAt, besselGridStateBlock00, besselGridStateBlock01,
    besselGridStateBlock02, besselGridStateBlock03, besselGridStateBlock04,
    besselGridStateBlock05, besselGridStateBlock06, besselGridStateBlock07,
    besselGridStateBlock08, besselGridStateBlock09, besselGridStateBlock10,
    besselGridStateBlock11, besselGridStateBlock12, besselGridStateBlock13,
    besselGridStateBlock14, besselGridState007, besselGridState010, besselGridState016, besselGridState019, besselGridState020, besselGridState025, besselGridState027, besselGridState030, besselGridState035, besselGridState037, besselGridState040, besselGridState041, besselGridState043, besselGridState044, besselGridState045, besselGridState050, besselGridState053, besselGridState054, besselGridState060, besselGridState064, besselGridState068, besselGridState074, besselGridState077, besselGridState079, besselStateSubset, linearInterval, widenInterval,
    rationalErrorInterval, rationalIntervalSubset, orderedInterval, Finset.sum_range_succ,
    IntervalRat.add, IntervalRat.mul, IntervalRat.scale, IntervalRat.singleton]

theorem compactCertificate231_stateChecks7 :
    compactCertificate231.stateChecks 21 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 10 12 (126640117588593 / 4000000000000)) (orderedInterval (121234031158 / 1000000000000) (121234031159 / 1000000000000), orderedInterval (71632776574 / 1000000000000) (71632776575 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 27 12 (343852554264779 / 4000000000000)) (orderedInterval (-80741128944 / 1000000000000) (-80741126084 / 1000000000000), orderedInterval (30243839562 / 1000000000000) (30243842422 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 37 12 (469501265989483 / 4000000000000)) (orderedInterval (-69183018286 / 1000000000000) (-69183015019 / 1000000000000), orderedInterval (25542841197 / 1000000000000) (25542844464 / 1000000000000))) = true
  norm_num [besselStateAtRationalPoint, besselIntervalStepZero,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, besselZeroTransition,
    besselInitial, besselGridStateAt, besselGridStateBlock00, besselGridStateBlock01,
    besselGridStateBlock02, besselGridStateBlock03, besselGridStateBlock04,
    besselGridStateBlock05, besselGridStateBlock06, besselGridStateBlock07,
    besselGridStateBlock08, besselGridStateBlock09, besselGridStateBlock10,
    besselGridStateBlock11, besselGridStateBlock12, besselGridStateBlock13,
    besselGridStateBlock14, besselGridState007, besselGridState010, besselGridState016, besselGridState019, besselGridState020, besselGridState025, besselGridState027, besselGridState030, besselGridState035, besselGridState037, besselGridState040, besselGridState041, besselGridState043, besselGridState044, besselGridState045, besselGridState050, besselGridState053, besselGridState054, besselGridState060, besselGridState064, besselGridState068, besselGridState074, besselGridState077, besselGridState079, besselStateSubset, linearInterval, widenInterval,
    rationalErrorInterval, rationalIntervalSubset, orderedInterval, Finset.sum_range_succ,
    IntervalRat.add, IntervalRat.mul, IntervalRat.scale, IntervalRat.singleton]

theorem compactCertificate231_stateChecks8 :
    compactCertificate231.stateChecks 24 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 16 12 (198523364766321 / 4000000000000)) (orderedInterval (16727208475 / 1000000000000) (16727208476 / 1000000000000), orderedInterval (111849012045 / 1000000000000) (111849012047 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 64 12 (806986456087441 / 4000000000000)) (orderedInterval (55885953713 / 1000000000000) (55885953728 / 1000000000000), orderedInterval (5544099061 / 1000000000000) (5544099076 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 43 12 (539029553634719 / 4000000000000)) (orderedInterval (-30104979738 / 1000000000000) (-30104979737 / 1000000000000), orderedInterval (-61677476349 / 1000000000000) (-61677476348 / 1000000000000))) = true
  norm_num [besselStateAtRationalPoint, besselIntervalStepZero,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, besselZeroTransition,
    besselInitial, besselGridStateAt, besselGridStateBlock00, besselGridStateBlock01,
    besselGridStateBlock02, besselGridStateBlock03, besselGridStateBlock04,
    besselGridStateBlock05, besselGridStateBlock06, besselGridStateBlock07,
    besselGridStateBlock08, besselGridStateBlock09, besselGridStateBlock10,
    besselGridStateBlock11, besselGridStateBlock12, besselGridStateBlock13,
    besselGridStateBlock14, besselGridState007, besselGridState010, besselGridState016, besselGridState019, besselGridState020, besselGridState025, besselGridState027, besselGridState030, besselGridState035, besselGridState037, besselGridState040, besselGridState041, besselGridState043, besselGridState044, besselGridState045, besselGridState050, besselGridState053, besselGridState054, besselGridState060, besselGridState064, besselGridState068, besselGridState074, besselGridState077, besselGridState079, besselStateSubset, linearInterval, widenInterval,
    rationalErrorInterval, rationalIntervalSubset, orderedInterval, Finset.sum_range_succ,
    IntervalRat.add, IntervalRat.mul, IntervalRat.scale, IntervalRat.singleton]

theorem compactCertificate231_states : ∀ j,
    BesselStateValid (compactCertificate231.point j) (compactCertificate231.state j) :=
  compactCertificate231.statesValid_of_checks3 compactCertificate231_stateChecks0
    compactCertificate231_stateChecks1 compactCertificate231_stateChecks2
    compactCertificate231_stateChecks3 compactCertificate231_stateChecks4
    compactCertificate231_stateChecks5 compactCertificate231_stateChecks6
    compactCertificate231_stateChecks7 compactCertificate231_stateChecks8

theorem compactCertificate231_chunkChecks0_0 :
    compactCertificate231.chunkChecks (0 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 0) <| besselDerivativeNearFromState (217 / 2) 0 (IntervalRat.scale (217 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (47656679352 / 1000000000000) (47656704846 / 1000000000000), orderedInterval (-60188924341 / 1000000000000) (-60188898848 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 0) <| besselDerivativeNearFromState (319682435694517 / 4000000000000) 0 (IntervalRat.scale (217 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-73970415229 / 1000000000000) (-73970384402 / 1000000000000), orderedInterval (50402440733 / 1000000000000) (50402471560 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 0) <| besselDerivativeNearFromState (103378731413461 / 800000000000) 0 (IntervalRat.scale (217 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-65483257181 / 1000000000000) (-65483257180 / 1000000000000), orderedInterval (-25013616415 / 1000000000000) (-25013616414 / 1000000000000)))) (orderedInterval (14357546424 / 1000000000000) (14357556825 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 0) <| besselDerivativeNearFromState (93282537436319 / 4000000000000) 0 (IntervalRat.scale (217 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-141804298856 / 1000000000000) (-141804284341 / 1000000000000), orderedInterval (87815936808 / 1000000000000) (87815951322 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 0) <| besselDerivativeNearFromState (250570016828243 / 4000000000000) 0 (IntervalRat.scale (217 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (56425241684 / 1000000000000) (56425241685 / 1000000000000), orderedInterval (83090407494 / 1000000000000) (83090407495 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 0) <| besselDerivativeNearFromState (680346338498631 / 4000000000000) 0 (IntervalRat.scale (217 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (57562858424 / 1000000000000) (57562858425 / 1000000000000), orderedInterval (20553253909 / 1000000000000) (20553253910 / 1000000000000)))) (orderedInterval (-493462909 / 1000000000000) (-493462738 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 0) <| besselDerivativeNearFromState (501140033656703 / 4000000000000) 0 (IntervalRat.scale (217 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (28133055497 / 1000000000000) (28133055498 / 1000000000000), orderedInterval (65385293104 / 1000000000000) (65385293105 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 0) <| besselDerivativeNearFromState (858711989329019 / 4000000000000) 0 (IntervalRat.scale (217 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (52573335327 / 1000000000000) (52573337490 / 1000000000000), orderedInterval (-14317547807 / 1000000000000) (-14317545643 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 0) <| besselDerivativeNearFromState (632523364766321 / 4000000000000) 0 (IntervalRat.scale (217 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (61234655286 / 1000000000000) (61234656875 / 1000000000000), orderedInterval (-16813026552 / 1000000000000) (-16813024963 / 1000000000000)))) (orderedInterval (-141651275 / 1000000000000) (-141651163 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate231_chunkChecks0_1 :
    compactCertificate231.chunkChecks (0 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 0) <| besselDerivativeNearFromState (970453502234783 / 4000000000000) 0 (IntervalRat.scale (217 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-51080366654 / 1000000000000) (-51080366623 / 1000000000000), orderedInterval (-3741807608 / 1000000000000) (-3741807577 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 0) <| besselDerivativeNearFromState (560291590751207 / 4000000000000) 0 (IntervalRat.scale (217 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (33161545083 / 1000000000000) (33161549678 / 1000000000000), orderedInterval (-58814576349 / 1000000000000) (-58814571754 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 0) <| besselDerivativeNearFromState (994247259966163 / 4000000000000) 0 (IntervalRat.scale (217 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-46415899286 / 1000000000000) (-46415899285 / 1000000000000), orderedInterval (-20075266513 / 1000000000000) (-20075266512 / 1000000000000)))) (orderedInterval (4935068421 / 1000000000000) (4935068811 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 0) <| besselDerivativeNearFromState (928954760622847 / 4000000000000) 0 (IntervalRat.scale (217 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (27173713236 / 1000000000000) (27173713237 / 1000000000000), orderedInterval (44694403629 / 1000000000000) (44694403630 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 0) <| besselDerivativeNearFromState (662945950536751 / 4000000000000) 0 (IntervalRat.scale (217 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-1036265500 / 1000000000000) (-1036265496 / 1000000000000), orderedInterval (-61965414482 / 1000000000000) (-61965414478 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 0) <| besselDerivativeNearFromState (751710050484729 / 4000000000000) 0 (IntervalRat.scale (217 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (12513301690 / 1000000000000) (12513301692 / 1000000000000), orderedInterval (56808678635 / 1000000000000) (56808678636 / 1000000000000)))) (orderedInterval (-651886139 / 1000000000000) (-651886125 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 0) <| besselDerivativeNearFromState (626697470381801 / 4000000000000) 0 (IntervalRat.scale (217 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (23604635205 / 1000000000000) (23604635206 / 1000000000000), orderedInterval (59137565596 / 1000000000000) (59137565597 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 0) <| besselDerivativeNearFromState (553706220909821 / 4000000000000) 0 (IntervalRat.scale (217 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (56357343441 / 1000000000000) (56357343442 / 1000000000000), orderedInterval (37516590123 / 1000000000000) (37516590124 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 0) <| besselDerivativeNearFromState (160485644556279 / 800000000000) 0 (IntervalRat.scale (217 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (18249179043 / 1000000000000) (18249179044 / 1000000000000), orderedInterval (53250310345 / 1000000000000) (53250310346 / 1000000000000)))) (orderedInterval (-2485313890 / 1000000000000) (-2485313878 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate231_chunkChecks0_2 :
    compactCertificate231.chunkChecks (0 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 0) <| besselDerivativeNearFromState (443911738739413 / 4000000000000) 0 (IntervalRat.scale (217 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-73645474160 / 1000000000000) (-73645473307 / 1000000000000), orderedInterval (18016419103 / 1000000000000) (18016419956 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 0) <| besselDerivativeNearFromState (376308897117293 / 4000000000000) 0 (IntervalRat.scale (217 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (47361388204 / 1000000000000) (47361388205 / 1000000000000), orderedInterval (67008402863 / 1000000000000) (67008402864 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 0) <| besselDerivativeNearFromState (235476635233679 / 4000000000000) 0 (IntervalRat.scale (217 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (3932608186 / 1000000000000) (3932608202 / 1000000000000), orderedInterval (-103951977356 / 1000000000000) (-103951977340 / 1000000000000)))) (orderedInterval (9222729192 / 1000000000000) (9222729357 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 0) <| besselDerivativeNearFromState (126640117588593 / 4000000000000) 0 (IntervalRat.scale (217 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (121234031158 / 1000000000000) (121234031159 / 1000000000000), orderedInterval (71632776574 / 1000000000000) (71632776575 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 0) <| besselDerivativeNearFromState (343852554264779 / 4000000000000) 0 (IntervalRat.scale (217 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-80741128944 / 1000000000000) (-80741126084 / 1000000000000), orderedInterval (30243839562 / 1000000000000) (30243842422 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 0) <| besselDerivativeNearFromState (469501265989483 / 4000000000000) 0 (IntervalRat.scale (217 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-69183018286 / 1000000000000) (-69183015019 / 1000000000000), orderedInterval (25542841197 / 1000000000000) (25542844464 / 1000000000000)))) (orderedInterval (4895270303 / 1000000000000) (4895270632 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 0) <| besselDerivativeNearFromState (198523364766321 / 4000000000000) 0 (IntervalRat.scale (217 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (16727208475 / 1000000000000) (16727208476 / 1000000000000), orderedInterval (111849012045 / 1000000000000) (111849012047 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 0) <| besselDerivativeNearFromState (806986456087441 / 4000000000000) 0 (IntervalRat.scale (217 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (55885953713 / 1000000000000) (55885953728 / 1000000000000), orderedInterval (5544099061 / 1000000000000) (5544099076 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 0) <| besselDerivativeNearFromState (539029553634719 / 4000000000000) 0 (IntervalRat.scale (217 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-30104979738 / 1000000000000) (-30104979737 / 1000000000000), orderedInterval (-61677476349 / 1000000000000) (-61677476348 / 1000000000000)))) (orderedInterval (1200113934 / 1000000000000) (1200113967 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate231_chunkChecks0 :
    compactCertificate231.chunkChecks (0 : Fin 5) 0 9 = true :=
  compactCertificate231.chunkChecks_nine_of_three (0 : Fin 5) compactCertificate231_chunkChecks0_0
    compactCertificate231_chunkChecks0_1 compactCertificate231_chunkChecks0_2

theorem compactCertificate231_chunkChecks1_0 :
    compactCertificate231.chunkChecks (1 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 1) <| besselDerivativeNearFromState (217 / 2) 1 (IntervalRat.scale (217 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (47656679352 / 1000000000000) (47656704846 / 1000000000000), orderedInterval (-60188924341 / 1000000000000) (-60188898848 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 1) <| besselDerivativeNearFromState (319682435694517 / 4000000000000) 1 (IntervalRat.scale (217 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-73970415229 / 1000000000000) (-73970384402 / 1000000000000), orderedInterval (50402440733 / 1000000000000) (50402471560 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 1) <| besselDerivativeNearFromState (103378731413461 / 800000000000) 1 (IntervalRat.scale (217 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-65483257181 / 1000000000000) (-65483257180 / 1000000000000), orderedInterval (-25013616415 / 1000000000000) (-25013616414 / 1000000000000)))) (orderedInterval (-25259019755 / 1000000000000) (-25259009429 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 1) <| besselDerivativeNearFromState (93282537436319 / 4000000000000) 1 (IntervalRat.scale (217 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-141804298856 / 1000000000000) (-141804284341 / 1000000000000), orderedInterval (87815936808 / 1000000000000) (87815951322 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 1) <| besselDerivativeNearFromState (250570016828243 / 4000000000000) 1 (IntervalRat.scale (217 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (56425241684 / 1000000000000) (56425241685 / 1000000000000), orderedInterval (83090407494 / 1000000000000) (83090407495 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 1) <| besselDerivativeNearFromState (680346338498631 / 4000000000000) 1 (IntervalRat.scale (217 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (57562858424 / 1000000000000) (57562858425 / 1000000000000), orderedInterval (20553253909 / 1000000000000) (20553253910 / 1000000000000)))) (orderedInterval (-743711523 / 1000000000000) (-743711473 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 1) <| besselDerivativeNearFromState (501140033656703 / 4000000000000) 1 (IntervalRat.scale (217 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (28133055497 / 1000000000000) (28133055498 / 1000000000000), orderedInterval (65385293104 / 1000000000000) (65385293105 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 1) <| besselDerivativeNearFromState (858711989329019 / 4000000000000) 1 (IntervalRat.scale (217 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (52573335327 / 1000000000000) (52573337490 / 1000000000000), orderedInterval (-14317547807 / 1000000000000) (-14317545643 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 1) <| besselDerivativeNearFromState (632523364766321 / 4000000000000) 1 (IntervalRat.scale (217 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (61234655286 / 1000000000000) (61234656875 / 1000000000000), orderedInterval (-16813026552 / 1000000000000) (-16813024963 / 1000000000000)))) (orderedInterval (281562349 / 1000000000000) (281562549 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate231_chunkChecks1_1 :
    compactCertificate231.chunkChecks (1 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 1) <| besselDerivativeNearFromState (970453502234783 / 4000000000000) 1 (IntervalRat.scale (217 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-51080366654 / 1000000000000) (-51080366623 / 1000000000000), orderedInterval (-3741807608 / 1000000000000) (-3741807577 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 1) <| besselDerivativeNearFromState (560291590751207 / 4000000000000) 1 (IntervalRat.scale (217 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (33161545083 / 1000000000000) (33161549678 / 1000000000000), orderedInterval (-58814576349 / 1000000000000) (-58814571754 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 1) <| besselDerivativeNearFromState (994247259966163 / 4000000000000) 1 (IntervalRat.scale (217 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-46415899286 / 1000000000000) (-46415899285 / 1000000000000), orderedInterval (-20075266513 / 1000000000000) (-20075266512 / 1000000000000)))) (orderedInterval (-10676820566 / 1000000000000) (-10676820024 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 1) <| besselDerivativeNearFromState (928954760622847 / 4000000000000) 1 (IntervalRat.scale (217 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (27173713236 / 1000000000000) (27173713237 / 1000000000000), orderedInterval (44694403629 / 1000000000000) (44694403630 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 1) <| besselDerivativeNearFromState (662945950536751 / 4000000000000) 1 (IntervalRat.scale (217 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-1036265500 / 1000000000000) (-1036265496 / 1000000000000), orderedInterval (-61965414482 / 1000000000000) (-61965414478 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 1) <| besselDerivativeNearFromState (751710050484729 / 4000000000000) 1 (IntervalRat.scale (217 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (12513301690 / 1000000000000) (12513301692 / 1000000000000), orderedInterval (56808678635 / 1000000000000) (56808678636 / 1000000000000)))) (orderedInterval (-11175734364 / 1000000000000) (-11175734341 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 1) <| besselDerivativeNearFromState (626697470381801 / 4000000000000) 1 (IntervalRat.scale (217 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (23604635205 / 1000000000000) (23604635206 / 1000000000000), orderedInterval (59137565596 / 1000000000000) (59137565597 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 1) <| besselDerivativeNearFromState (553706220909821 / 4000000000000) 1 (IntervalRat.scale (217 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (56357343441 / 1000000000000) (56357343442 / 1000000000000), orderedInterval (37516590123 / 1000000000000) (37516590124 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 1) <| besselDerivativeNearFromState (160485644556279 / 800000000000) 1 (IntervalRat.scale (217 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (18249179043 / 1000000000000) (18249179044 / 1000000000000), orderedInterval (53250310345 / 1000000000000) (53250310346 / 1000000000000)))) (orderedInterval (767830050 / 1000000000000) (767830066 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate231_chunkChecks1_2 :
    compactCertificate231.chunkChecks (1 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 1) <| besselDerivativeNearFromState (443911738739413 / 4000000000000) 1 (IntervalRat.scale (217 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-73645474160 / 1000000000000) (-73645473307 / 1000000000000), orderedInterval (18016419103 / 1000000000000) (18016419956 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 1) <| besselDerivativeNearFromState (376308897117293 / 4000000000000) 1 (IntervalRat.scale (217 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (47361388204 / 1000000000000) (47361388205 / 1000000000000), orderedInterval (67008402863 / 1000000000000) (67008402864 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 1) <| besselDerivativeNearFromState (235476635233679 / 4000000000000) 1 (IntervalRat.scale (217 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (3932608186 / 1000000000000) (3932608202 / 1000000000000), orderedInterval (-103951977356 / 1000000000000) (-103951977340 / 1000000000000)))) (orderedInterval (-8071163019 / 1000000000000) (-8071162853 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 1) <| besselDerivativeNearFromState (126640117588593 / 4000000000000) 1 (IntervalRat.scale (217 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (121234031158 / 1000000000000) (121234031159 / 1000000000000), orderedInterval (71632776574 / 1000000000000) (71632776575 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 1) <| besselDerivativeNearFromState (343852554264779 / 4000000000000) 1 (IntervalRat.scale (217 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-80741128944 / 1000000000000) (-80741126084 / 1000000000000), orderedInterval (30243839562 / 1000000000000) (30243842422 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 1) <| besselDerivativeNearFromState (469501265989483 / 4000000000000) 1 (IntervalRat.scale (217 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-69183018286 / 1000000000000) (-69183015019 / 1000000000000), orderedInterval (25542841197 / 1000000000000) (25542844464 / 1000000000000)))) (orderedInterval (-3047285549 / 1000000000000) (-3047285214 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 1) <| besselDerivativeNearFromState (198523364766321 / 4000000000000) 1 (IntervalRat.scale (217 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (16727208475 / 1000000000000) (16727208476 / 1000000000000), orderedInterval (111849012045 / 1000000000000) (111849012047 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 1) <| besselDerivativeNearFromState (806986456087441 / 4000000000000) 1 (IntervalRat.scale (217 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (55885953713 / 1000000000000) (55885953728 / 1000000000000), orderedInterval (5544099061 / 1000000000000) (5544099076 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 1) <| besselDerivativeNearFromState (539029553634719 / 4000000000000) 1 (IntervalRat.scale (217 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-30104979738 / 1000000000000) (-30104979737 / 1000000000000), orderedInterval (-61677476349 / 1000000000000) (-61677476348 / 1000000000000)))) (orderedInterval (13842148620 / 1000000000000) (13842148666 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate231_chunkChecks1 :
    compactCertificate231.chunkChecks (1 : Fin 5) 0 9 = true :=
  compactCertificate231.chunkChecks_nine_of_three (1 : Fin 5) compactCertificate231_chunkChecks1_0
    compactCertificate231_chunkChecks1_1 compactCertificate231_chunkChecks1_2

theorem compactCertificate231_chunkChecks2_0 :
    compactCertificate231.chunkChecks (2 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 2) <| besselDerivativeNearFromState (217 / 2) 2 (IntervalRat.scale (217 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (47656679352 / 1000000000000) (47656704846 / 1000000000000), orderedInterval (-60188924341 / 1000000000000) (-60188898848 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 2) <| besselDerivativeNearFromState (319682435694517 / 4000000000000) 2 (IntervalRat.scale (217 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-73970415229 / 1000000000000) (-73970384402 / 1000000000000), orderedInterval (50402440733 / 1000000000000) (50402471560 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 2) <| besselDerivativeNearFromState (103378731413461 / 800000000000) 2 (IntervalRat.scale (217 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-65483257181 / 1000000000000) (-65483257180 / 1000000000000), orderedInterval (-25013616415 / 1000000000000) (-25013616414 / 1000000000000)))) (orderedInterval (-12831979998 / 1000000000000) (-12831969631 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 2) <| besselDerivativeNearFromState (93282537436319 / 4000000000000) 2 (IntervalRat.scale (217 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-141804298856 / 1000000000000) (-141804284341 / 1000000000000), orderedInterval (87815936808 / 1000000000000) (87815951322 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 2) <| besselDerivativeNearFromState (250570016828243 / 4000000000000) 2 (IntervalRat.scale (217 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (56425241684 / 1000000000000) (56425241685 / 1000000000000), orderedInterval (83090407494 / 1000000000000) (83090407495 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 2) <| besselDerivativeNearFromState (680346338498631 / 4000000000000) 2 (IntervalRat.scale (217 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (57562858424 / 1000000000000) (57562858425 / 1000000000000), orderedInterval (20553253909 / 1000000000000) (20553253910 / 1000000000000)))) (orderedInterval (9305146081 / 1000000000000) (9305146110 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 2) <| besselDerivativeNearFromState (501140033656703 / 4000000000000) 2 (IntervalRat.scale (217 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (28133055497 / 1000000000000) (28133055498 / 1000000000000), orderedInterval (65385293104 / 1000000000000) (65385293105 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 2) <| besselDerivativeNearFromState (858711989329019 / 4000000000000) 2 (IntervalRat.scale (217 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (52573335327 / 1000000000000) (52573337490 / 1000000000000), orderedInterval (-14317547807 / 1000000000000) (-14317545643 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 2) <| besselDerivativeNearFromState (632523364766321 / 4000000000000) 2 (IntervalRat.scale (217 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (61234655286 / 1000000000000) (61234656875 / 1000000000000), orderedInterval (-16813026552 / 1000000000000) (-16813024963 / 1000000000000)))) (orderedInterval (3202132308 / 1000000000000) (3202132672 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate231_chunkChecks2_1 :
    compactCertificate231.chunkChecks (2 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 2) <| besselDerivativeNearFromState (970453502234783 / 4000000000000) 2 (IntervalRat.scale (217 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-51080366654 / 1000000000000) (-51080366623 / 1000000000000), orderedInterval (-3741807608 / 1000000000000) (-3741807577 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 2) <| besselDerivativeNearFromState (560291590751207 / 4000000000000) 2 (IntervalRat.scale (217 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (33161545083 / 1000000000000) (33161549678 / 1000000000000), orderedInterval (-58814576349 / 1000000000000) (-58814571754 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 2) <| besselDerivativeNearFromState (994247259966163 / 4000000000000) 2 (IntervalRat.scale (217 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-46415899286 / 1000000000000) (-46415899285 / 1000000000000), orderedInterval (-20075266513 / 1000000000000) (-20075266512 / 1000000000000)))) (orderedInterval (-14749332713 / 1000000000000) (-14749331922 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 2) <| besselDerivativeNearFromState (928954760622847 / 4000000000000) 2 (IntervalRat.scale (217 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (27173713236 / 1000000000000) (27173713237 / 1000000000000), orderedInterval (44694403629 / 1000000000000) (44694403630 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 2) <| besselDerivativeNearFromState (662945950536751 / 4000000000000) 2 (IntervalRat.scale (217 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-1036265500 / 1000000000000) (-1036265496 / 1000000000000), orderedInterval (-61965414482 / 1000000000000) (-61965414478 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 2) <| besselDerivativeNearFromState (751710050484729 / 4000000000000) 2 (IntervalRat.scale (217 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (12513301690 / 1000000000000) (12513301692 / 1000000000000), orderedInterval (56808678635 / 1000000000000) (56808678636 / 1000000000000)))) (orderedInterval (2769178101 / 1000000000000) (2769178138 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 2) <| besselDerivativeNearFromState (626697470381801 / 4000000000000) 2 (IntervalRat.scale (217 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (23604635205 / 1000000000000) (23604635206 / 1000000000000), orderedInterval (59137565596 / 1000000000000) (59137565597 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 2) <| besselDerivativeNearFromState (553706220909821 / 4000000000000) 2 (IntervalRat.scale (217 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (56357343441 / 1000000000000) (56357343442 / 1000000000000), orderedInterval (37516590123 / 1000000000000) (37516590124 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 2) <| besselDerivativeNearFromState (160485644556279 / 800000000000) 2 (IntervalRat.scale (217 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (18249179043 / 1000000000000) (18249179044 / 1000000000000), orderedInterval (53250310345 / 1000000000000) (53250310346 / 1000000000000)))) (orderedInterval (3076895500 / 1000000000000) (3076895523 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate231_chunkChecks2_2 :
    compactCertificate231.chunkChecks (2 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 2) <| besselDerivativeNearFromState (443911738739413 / 4000000000000) 2 (IntervalRat.scale (217 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-73645474160 / 1000000000000) (-73645473307 / 1000000000000), orderedInterval (18016419103 / 1000000000000) (18016419956 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 2) <| besselDerivativeNearFromState (376308897117293 / 4000000000000) 2 (IntervalRat.scale (217 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (47361388204 / 1000000000000) (47361388205 / 1000000000000), orderedInterval (67008402863 / 1000000000000) (67008402864 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 2) <| besselDerivativeNearFromState (235476635233679 / 4000000000000) 2 (IntervalRat.scale (217 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (3932608186 / 1000000000000) (3932608202 / 1000000000000), orderedInterval (-103951977356 / 1000000000000) (-103951977340 / 1000000000000)))) (orderedInterval (-10267302929 / 1000000000000) (-10267302760 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 2) <| besselDerivativeNearFromState (126640117588593 / 4000000000000) 2 (IntervalRat.scale (217 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (121234031158 / 1000000000000) (121234031159 / 1000000000000), orderedInterval (71632776574 / 1000000000000) (71632776575 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 2) <| besselDerivativeNearFromState (343852554264779 / 4000000000000) 2 (IntervalRat.scale (217 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-80741128944 / 1000000000000) (-80741126084 / 1000000000000), orderedInterval (30243839562 / 1000000000000) (30243842422 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 2) <| besselDerivativeNearFromState (469501265989483 / 4000000000000) 2 (IntervalRat.scale (217 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-69183018286 / 1000000000000) (-69183015019 / 1000000000000), orderedInterval (25542841197 / 1000000000000) (25542844464 / 1000000000000)))) (orderedInterval (-7136151472 / 1000000000000) (-7136151123 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 2) <| besselDerivativeNearFromState (198523364766321 / 4000000000000) 2 (IntervalRat.scale (217 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (16727208475 / 1000000000000) (16727208476 / 1000000000000), orderedInterval (111849012045 / 1000000000000) (111849012047 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 2) <| besselDerivativeNearFromState (806986456087441 / 4000000000000) 2 (IntervalRat.scale (217 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (55885953713 / 1000000000000) (55885953728 / 1000000000000), orderedInterval (5544099061 / 1000000000000) (5544099076 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 2) <| besselDerivativeNearFromState (539029553634719 / 4000000000000) 2 (IntervalRat.scale (217 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-30104979738 / 1000000000000) (-30104979737 / 1000000000000), orderedInterval (-61677476349 / 1000000000000) (-61677476348 / 1000000000000)))) (orderedInterval (6866694101 / 1000000000000) (6866694169 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate231_chunkChecks2 :
    compactCertificate231.chunkChecks (2 : Fin 5) 0 9 = true :=
  compactCertificate231.chunkChecks_nine_of_three (2 : Fin 5) compactCertificate231_chunkChecks2_0
    compactCertificate231_chunkChecks2_1 compactCertificate231_chunkChecks2_2

theorem compactCertificate231_chunkChecks3_0 :
    compactCertificate231.chunkChecks (3 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 3) <| besselDerivativeNearFromState (217 / 2) 3 (IntervalRat.scale (217 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (47656679352 / 1000000000000) (47656704846 / 1000000000000), orderedInterval (-60188924341 / 1000000000000) (-60188898848 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 3) <| besselDerivativeNearFromState (319682435694517 / 4000000000000) 3 (IntervalRat.scale (217 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-73970415229 / 1000000000000) (-73970384402 / 1000000000000), orderedInterval (50402440733 / 1000000000000) (50402471560 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 3) <| besselDerivativeNearFromState (103378731413461 / 800000000000) 3 (IntervalRat.scale (217 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-65483257181 / 1000000000000) (-65483257180 / 1000000000000), orderedInterval (-25013616415 / 1000000000000) (-25013616414 / 1000000000000)))) (orderedInterval (26264952585 / 1000000000000) (26264962909 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 3) <| besselDerivativeNearFromState (93282537436319 / 4000000000000) 3 (IntervalRat.scale (217 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-141804298856 / 1000000000000) (-141804284341 / 1000000000000), orderedInterval (87815936808 / 1000000000000) (87815951322 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 3) <| besselDerivativeNearFromState (250570016828243 / 4000000000000) 3 (IntervalRat.scale (217 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (56425241684 / 1000000000000) (56425241685 / 1000000000000), orderedInterval (83090407494 / 1000000000000) (83090407495 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 3) <| besselDerivativeNearFromState (680346338498631 / 4000000000000) 3 (IntervalRat.scale (217 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (57562858424 / 1000000000000) (57562858425 / 1000000000000), orderedInterval (20553253909 / 1000000000000) (20553253910 / 1000000000000)))) (orderedInterval (4968482057 / 1000000000000) (4968482090 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 3) <| besselDerivativeNearFromState (501140033656703 / 4000000000000) 3 (IntervalRat.scale (217 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (28133055497 / 1000000000000) (28133055498 / 1000000000000), orderedInterval (65385293104 / 1000000000000) (65385293105 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 3) <| besselDerivativeNearFromState (858711989329019 / 4000000000000) 3 (IntervalRat.scale (217 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (52573335327 / 1000000000000) (52573337490 / 1000000000000), orderedInterval (-14317547807 / 1000000000000) (-14317545643 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 3) <| besselDerivativeNearFromState (632523364766321 / 4000000000000) 3 (IntervalRat.scale (217 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (61234655286 / 1000000000000) (61234656875 / 1000000000000), orderedInterval (-16813026552 / 1000000000000) (-16813024963 / 1000000000000)))) (orderedInterval (-2192266903 / 1000000000000) (-2192266229 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate231_chunkChecks3_1 :
    compactCertificate231.chunkChecks (3 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 3) <| besselDerivativeNearFromState (970453502234783 / 4000000000000) 3 (IntervalRat.scale (217 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-51080366654 / 1000000000000) (-51080366623 / 1000000000000), orderedInterval (-3741807608 / 1000000000000) (-3741807577 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 3) <| besselDerivativeNearFromState (560291590751207 / 4000000000000) 3 (IntervalRat.scale (217 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (33161545083 / 1000000000000) (33161549678 / 1000000000000), orderedInterval (-58814576349 / 1000000000000) (-58814571754 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 3) <| besselDerivativeNearFromState (994247259966163 / 4000000000000) 3 (IntervalRat.scale (217 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-46415899286 / 1000000000000) (-46415899285 / 1000000000000), orderedInterval (-20075266513 / 1000000000000) (-20075266512 / 1000000000000)))) (orderedInterval (36389278588 / 1000000000000) (36389279808 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 3) <| besselDerivativeNearFromState (928954760622847 / 4000000000000) 3 (IntervalRat.scale (217 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (27173713236 / 1000000000000) (27173713237 / 1000000000000), orderedInterval (44694403629 / 1000000000000) (44694403630 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 3) <| besselDerivativeNearFromState (662945950536751 / 4000000000000) 3 (IntervalRat.scale (217 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-1036265500 / 1000000000000) (-1036265496 / 1000000000000), orderedInterval (-61965414482 / 1000000000000) (-61965414478 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 3) <| besselDerivativeNearFromState (751710050484729 / 4000000000000) 3 (IntervalRat.scale (217 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (12513301690 / 1000000000000) (12513301692 / 1000000000000), orderedInterval (56808678635 / 1000000000000) (56808678636 / 1000000000000)))) (orderedInterval (30264973148 / 1000000000000) (30264973209 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 3) <| besselDerivativeNearFromState (626697470381801 / 4000000000000) 3 (IntervalRat.scale (217 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (23604635205 / 1000000000000) (23604635206 / 1000000000000), orderedInterval (59137565596 / 1000000000000) (59137565597 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 3) <| besselDerivativeNearFromState (553706220909821 / 4000000000000) 3 (IntervalRat.scale (217 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (56357343441 / 1000000000000) (56357343442 / 1000000000000), orderedInterval (37516590123 / 1000000000000) (37516590124 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 3) <| besselDerivativeNearFromState (160485644556279 / 800000000000) 3 (IntervalRat.scale (217 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (18249179043 / 1000000000000) (18249179044 / 1000000000000), orderedInterval (53250310345 / 1000000000000) (53250310346 / 1000000000000)))) (orderedInterval (-6243402377 / 1000000000000) (-6243402341 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate231_chunkChecks3_2 :
    compactCertificate231.chunkChecks (3 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 3) <| besselDerivativeNearFromState (443911738739413 / 4000000000000) 3 (IntervalRat.scale (217 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-73645474160 / 1000000000000) (-73645473307 / 1000000000000), orderedInterval (18016419103 / 1000000000000) (18016419956 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 3) <| besselDerivativeNearFromState (376308897117293 / 4000000000000) 3 (IntervalRat.scale (217 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (47361388204 / 1000000000000) (47361388205 / 1000000000000), orderedInterval (67008402863 / 1000000000000) (67008402864 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 3) <| besselDerivativeNearFromState (235476635233679 / 4000000000000) 3 (IntervalRat.scale (217 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (3932608186 / 1000000000000) (3932608202 / 1000000000000), orderedInterval (-103951977356 / 1000000000000) (-103951977340 / 1000000000000)))) (orderedInterval (6189432261 / 1000000000000) (6189432433 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 3) <| besselDerivativeNearFromState (126640117588593 / 4000000000000) 3 (IntervalRat.scale (217 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (121234031158 / 1000000000000) (121234031159 / 1000000000000), orderedInterval (71632776574 / 1000000000000) (71632776575 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 3) <| besselDerivativeNearFromState (343852554264779 / 4000000000000) 3 (IntervalRat.scale (217 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-80741128944 / 1000000000000) (-80741126084 / 1000000000000), orderedInterval (30243839562 / 1000000000000) (30243842422 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 3) <| besselDerivativeNearFromState (469501265989483 / 4000000000000) 3 (IntervalRat.scale (217 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-69183018286 / 1000000000000) (-69183015019 / 1000000000000), orderedInterval (25542841197 / 1000000000000) (25542844464 / 1000000000000)))) (orderedInterval (2917946012 / 1000000000000) (2917946377 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 3) <| besselDerivativeNearFromState (198523364766321 / 4000000000000) 3 (IntervalRat.scale (217 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (16727208475 / 1000000000000) (16727208476 / 1000000000000), orderedInterval (111849012045 / 1000000000000) (111849012047 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 3) <| besselDerivativeNearFromState (806986456087441 / 4000000000000) 3 (IntervalRat.scale (217 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (55885953713 / 1000000000000) (55885953728 / 1000000000000), orderedInterval (5544099061 / 1000000000000) (5544099076 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 3) <| besselDerivativeNearFromState (539029553634719 / 4000000000000) 3 (IntervalRat.scale (217 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-30104979738 / 1000000000000) (-30104979737 / 1000000000000), orderedInterval (-61677476349 / 1000000000000) (-61677476348 / 1000000000000)))) (orderedInterval (-19396543862 / 1000000000000) (-19396543756 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate231_chunkChecks3 :
    compactCertificate231.chunkChecks (3 : Fin 5) 0 9 = true :=
  compactCertificate231.chunkChecks_nine_of_three (3 : Fin 5) compactCertificate231_chunkChecks3_0
    compactCertificate231_chunkChecks3_1 compactCertificate231_chunkChecks3_2

theorem compactCertificate231_chunkChecks4_0 :
    compactCertificate231.chunkChecks (4 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 4) <| besselDerivativeNearFromState (217 / 2) 4 (IntervalRat.scale (217 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (47656679352 / 1000000000000) (47656704846 / 1000000000000), orderedInterval (-60188924341 / 1000000000000) (-60188898848 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 4) <| besselDerivativeNearFromState (319682435694517 / 4000000000000) 4 (IntervalRat.scale (217 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-73970415229 / 1000000000000) (-73970384402 / 1000000000000), orderedInterval (50402440733 / 1000000000000) (50402471560 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 4) <| besselDerivativeNearFromState (103378731413461 / 800000000000) 4 (IntervalRat.scale (217 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-65483257181 / 1000000000000) (-65483257180 / 1000000000000), orderedInterval (-25013616415 / 1000000000000) (-25013616414 / 1000000000000)))) (orderedInterval (10469619161 / 1000000000000) (10469629551 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 4) <| besselDerivativeNearFromState (93282537436319 / 4000000000000) 4 (IntervalRat.scale (217 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-141804298856 / 1000000000000) (-141804284341 / 1000000000000), orderedInterval (87815936808 / 1000000000000) (87815951322 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 4) <| besselDerivativeNearFromState (250570016828243 / 4000000000000) 4 (IntervalRat.scale (217 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (56425241684 / 1000000000000) (56425241685 / 1000000000000), orderedInterval (83090407494 / 1000000000000) (83090407495 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 4) <| besselDerivativeNearFromState (680346338498631 / 4000000000000) 4 (IntervalRat.scale (217 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (57562858424 / 1000000000000) (57562858425 / 1000000000000), orderedInterval (20553253909 / 1000000000000) (20553253910 / 1000000000000)))) (orderedInterval (-24570718725 / 1000000000000) (-24570718676 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 4) <| besselDerivativeNearFromState (501140033656703 / 4000000000000) 4 (IntervalRat.scale (217 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (28133055497 / 1000000000000) (28133055498 / 1000000000000), orderedInterval (65385293104 / 1000000000000) (65385293105 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 4) <| besselDerivativeNearFromState (858711989329019 / 4000000000000) 4 (IntervalRat.scale (217 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (52573335327 / 1000000000000) (52573337490 / 1000000000000), orderedInterval (-14317547807 / 1000000000000) (-14317545643 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 4) <| besselDerivativeNearFromState (632523364766321 / 4000000000000) 4 (IntervalRat.scale (217 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (61234655286 / 1000000000000) (61234656875 / 1000000000000), orderedInterval (-16813026552 / 1000000000000) (-16813024963 / 1000000000000)))) (orderedInterval (-18134598129 / 1000000000000) (-18134596858 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate231_chunkChecks4_1 :
    compactCertificate231.chunkChecks (4 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 4) <| besselDerivativeNearFromState (970453502234783 / 4000000000000) 4 (IntervalRat.scale (217 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-51080366654 / 1000000000000) (-51080366623 / 1000000000000), orderedInterval (-3741807608 / 1000000000000) (-3741807577 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 4) <| besselDerivativeNearFromState (560291590751207 / 4000000000000) 4 (IntervalRat.scale (217 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (33161545083 / 1000000000000) (33161549678 / 1000000000000), orderedInterval (-58814576349 / 1000000000000) (-58814571754 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 4) <| besselDerivativeNearFromState (994247259966163 / 4000000000000) 4 (IntervalRat.scale (217 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-46415899286 / 1000000000000) (-46415899285 / 1000000000000), orderedInterval (-20075266513 / 1000000000000) (-20075266512 / 1000000000000)))) (orderedInterval (51322170635 / 1000000000000) (51322172668 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 4) <| besselDerivativeNearFromState (928954760622847 / 4000000000000) 4 (IntervalRat.scale (217 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (27173713236 / 1000000000000) (27173713237 / 1000000000000), orderedInterval (44694403629 / 1000000000000) (44694403630 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 4) <| besselDerivativeNearFromState (662945950536751 / 4000000000000) 4 (IntervalRat.scale (217 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-1036265500 / 1000000000000) (-1036265496 / 1000000000000), orderedInterval (-61965414482 / 1000000000000) (-61965414478 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 4) <| besselDerivativeNearFromState (751710050484729 / 4000000000000) 4 (IntervalRat.scale (217 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (12513301690 / 1000000000000) (12513301692 / 1000000000000), orderedInterval (56808678635 / 1000000000000) (56808678636 / 1000000000000)))) (orderedInterval (-11958284653 / 1000000000000) (-11958284547 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 4) <| besselDerivativeNearFromState (626697470381801 / 4000000000000) 4 (IntervalRat.scale (217 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (23604635205 / 1000000000000) (23604635206 / 1000000000000), orderedInterval (59137565596 / 1000000000000) (59137565597 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 4) <| besselDerivativeNearFromState (553706220909821 / 4000000000000) 4 (IntervalRat.scale (217 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (56357343441 / 1000000000000) (56357343442 / 1000000000000), orderedInterval (37516590123 / 1000000000000) (37516590124 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 4) <| besselDerivativeNearFromState (160485644556279 / 800000000000) 4 (IntervalRat.scale (217 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (18249179043 / 1000000000000) (18249179044 / 1000000000000), orderedInterval (53250310345 / 1000000000000) (53250310346 / 1000000000000)))) (orderedInterval (-1784146586 / 1000000000000) (-1784146530 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate231_chunkChecks4_2 :
    compactCertificate231.chunkChecks (4 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 4) <| besselDerivativeNearFromState (443911738739413 / 4000000000000) 4 (IntervalRat.scale (217 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-73645474160 / 1000000000000) (-73645473307 / 1000000000000), orderedInterval (18016419103 / 1000000000000) (18016419956 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 4) <| besselDerivativeNearFromState (376308897117293 / 4000000000000) 4 (IntervalRat.scale (217 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (47361388204 / 1000000000000) (47361388205 / 1000000000000), orderedInterval (67008402863 / 1000000000000) (67008402864 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 4) <| besselDerivativeNearFromState (235476635233679 / 4000000000000) 4 (IntervalRat.scale (217 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (3932608186 / 1000000000000) (3932608202 / 1000000000000), orderedInterval (-103951977356 / 1000000000000) (-103951977340 / 1000000000000)))) (orderedInterval (11269451527 / 1000000000000) (11269451703 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 4) <| besselDerivativeNearFromState (126640117588593 / 4000000000000) 4 (IntervalRat.scale (217 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (121234031158 / 1000000000000) (121234031159 / 1000000000000), orderedInterval (71632776574 / 1000000000000) (71632776575 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 4) <| besselDerivativeNearFromState (343852554264779 / 4000000000000) 4 (IntervalRat.scale (217 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-80741128944 / 1000000000000) (-80741126084 / 1000000000000), orderedInterval (30243839562 / 1000000000000) (30243842422 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 4) <| besselDerivativeNearFromState (469501265989483 / 4000000000000) 4 (IntervalRat.scale (217 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-69183018286 / 1000000000000) (-69183015019 / 1000000000000), orderedInterval (25542841197 / 1000000000000) (25542844464 / 1000000000000)))) (orderedInterval (7912824287 / 1000000000000) (7912824675 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 4) <| besselDerivativeNearFromState (198523364766321 / 4000000000000) 4 (IntervalRat.scale (217 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (16727208475 / 1000000000000) (16727208476 / 1000000000000), orderedInterval (111849012045 / 1000000000000) (111849012047 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 4) <| besselDerivativeNearFromState (806986456087441 / 4000000000000) 4 (IntervalRat.scale (217 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (55885953713 / 1000000000000) (55885953728 / 1000000000000), orderedInterval (5544099061 / 1000000000000) (5544099076 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 4) <| besselDerivativeNearFromState (539029553634719 / 4000000000000) 4 (IntervalRat.scale (217 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-30104979738 / 1000000000000) (-30104979737 / 1000000000000), orderedInterval (-61677476349 / 1000000000000) (-61677476348 / 1000000000000)))) (orderedInterval (-40577136016 / 1000000000000) (-40577135845 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate231_chunkChecks4 :
    compactCertificate231.chunkChecks (4 : Fin 5) 0 9 = true :=
  compactCertificate231.chunkChecks_nine_of_three (4 : Fin 5) compactCertificate231_chunkChecks4_0
    compactCertificate231_chunkChecks4_1 compactCertificate231_chunkChecks4_2

theorem compactCertificate231_chunks :
    ∀ r : Fin 5, ∀ b, compactCertificate231.chunkCheck r b = true :=
  compactCertificate231.chunkChecks_all (by
    intro r
    fin_cases r
    · exact compactCertificate231_chunkChecks0
    · exact compactCertificate231_chunkChecks1
    · exact compactCertificate231_chunkChecks2
    · exact compactCertificate231_chunkChecks3
    · exact compactCertificate231_chunkChecks4)

theorem compactCertificate231_coefficient0 :
    compactCertificate231.coefficientCheck (0 : Fin 5) = true := by
  norm_num [CompactCertificate.coefficientCheck, intervalFinSumHull,
    compactCertificate231, rationalIntervalSubset, orderedInterval, Fin.sum_univ_succ]

theorem compactCertificate231_coefficient1 :
    compactCertificate231.coefficientCheck (1 : Fin 5) = true := by
  norm_num [CompactCertificate.coefficientCheck, intervalFinSumHull,
    compactCertificate231, rationalIntervalSubset, orderedInterval, Fin.sum_univ_succ]

theorem compactCertificate231_coefficient2 :
    compactCertificate231.coefficientCheck (2 : Fin 5) = true := by
  norm_num [CompactCertificate.coefficientCheck, intervalFinSumHull,
    compactCertificate231, rationalIntervalSubset, orderedInterval, Fin.sum_univ_succ]

theorem compactCertificate231_coefficient3 :
    compactCertificate231.coefficientCheck (3 : Fin 5) = true := by
  norm_num [CompactCertificate.coefficientCheck, intervalFinSumHull,
    compactCertificate231, rationalIntervalSubset, orderedInterval, Fin.sum_univ_succ]

theorem compactCertificate231_coefficient4 :
    compactCertificate231.coefficientCheck (4 : Fin 5) = true := by
  norm_num [CompactCertificate.coefficientCheck, intervalFinSumHull,
    compactCertificate231, rationalIntervalSubset, orderedInterval, Fin.sum_univ_succ]

theorem compactCertificate231_coefficients : ∀ r : Fin 5,
    compactCertificate231.coefficientCheck r = true := by
  intro r
  fin_cases r
  · exact compactCertificate231_coefficient0
  · exact compactCertificate231_coefficient1
  · exact compactCertificate231_coefficient2
  · exact compactCertificate231_coefficient3
  · exact compactCertificate231_coefficient4

theorem compactCertificate231_lower : (1 : ℚ) ≤ compactCertificate231.output.lo := by
  norm_num [CompactCertificate.output, CompactCertificate.interval,
    CompactCertificate.coefficientTargetNat, compactCertificate231, dualConstant,
    intervalTaylorSum, intervalPow, intervalSub, intervalMaxAbs, widenInterval,
    rationalErrorInterval, orderedInterval, IntervalRat.add, IntervalRat.mul, IntervalRat.scale,
    IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4]

theorem compactCertificate231_proves {t : ℝ} (ht : t ∈ compactCertificate231.interval) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t :=
  compactCertificate231.proves compactCertificate231_states compactCertificate231_chunks
    compactCertificate231_coefficients compactCertificate231_lower ht

end Erdos232
