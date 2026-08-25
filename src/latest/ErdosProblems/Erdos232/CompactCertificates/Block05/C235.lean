/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, OpenAI Codex
-/
import ErdosProblems.Erdos232.CompactBase

open LeanCert.Core
namespace Erdos232

def compactCertificate235 : CompactCertificate where
  left := 112
  right := 113
  center := 225 / 2
  grid := fun i =>
    match i.val with
    | 0 => 36
    | 1 => 26
    | 2 => 43
    | 3 => 8
    | 4 => 21
    | 5 => 56
    | 6 => 41
    | 7 => 71
    | 8 => 52
    | 9 => 80
    | 10 => 46
    | 11 => 82
    | 12 => 77
    | 13 => 55
    | 14 => 62
    | 15 => 52
    | 16 => 46
    | 17 => 66
    | 18 => 37
    | 19 => 31
    | 20 => 19
    | 21 => 10
    | 22 => 28
    | 23 => 39
    | 24 => 16
    | 25 => 67
    | _ => 44
  point := fun i =>
    match i.val with
    | 0 => 225 / 2
    | 1 => 13258718531109 / 160000000000
    | 2 => 4287597155397 / 32000000000
    | 3 => 3868860999663 / 160000000000
    | 4 => 10392304845411 / 160000000000
    | 5 => 28217129246487 / 160000000000
    | 6 => 20784609690831 / 160000000000
    | 7 => 35614782967563 / 160000000000
    | 8 => 26233687939617 / 160000000000
    | 9 => 40249223594991 / 160000000000
    | 10 => 23237900077239 / 160000000000
    | 11 => 41236061473251 / 160000000000
    | 12 => 38528077629519 / 160000000000
    | 13 => 27495454169727 / 160000000000
    | 14 => 31176914536233 / 160000000000
    | 15 => 25992060983577 / 160000000000
    | 16 => 22964774139117 / 160000000000
    | 17 => 6656086640583 / 32000000000
    | 18 => 18411085938501 / 160000000000
    | 19 => 15607281447261 / 160000000000
    | 20 => 9766312060383 / 160000000000
    | 21 => 5252355107361 / 160000000000
    | 22 => 14261165845083 / 160000000000
    | 23 => 19472402736891 / 160000000000
    | 24 => 8233687939617 / 160000000000
    | 25 => 33469484353857 / 160000000000
    | _ => 22356064436463 / 160000000000
  state := fun i =>
    match i.val with
    | 0 => (orderedInterval (13981635826 / 1000000000000) (13981635828 / 1000000000000), orderedInterval (73852732621 / 1000000000000) (73852732623 / 1000000000000))
    | 1 => (orderedInterval (80774910372 / 1000000000000) (80774914962 / 1000000000000), orderedInterval (-34513010138 / 1000000000000) (-34513005548 / 1000000000000))
    | 2 => (orderedInterval (21460904255 / 1000000000000) (21460904743 / 1000000000000), orderedInterval (-65584255822 / 1000000000000) (-65584255333 / 1000000000000))
    | 3 => (orderedInterval (-27788419242 / 1000000000000) (-27788419098 / 1000000000000), orderedInterval (160452547646 / 1000000000000) (160452547790 / 1000000000000))
    | 4 => (orderedInterval (23346723629 / 1000000000000) (23346723905 / 1000000000000), orderedInterval (-96390892300 / 1000000000000) (-96390892024 / 1000000000000))
    | 5 => (orderedInterval (56267555039 / 1000000000000) (56267555040 / 1000000000000), orderedInterval (20906695711 / 1000000000000) (20906695712 / 1000000000000))
    | 6 => (orderedInterval (-66621776093 / 1000000000000) (-66621773784 / 1000000000000), orderedInterval (21755513894 / 1000000000000) (21755516203 / 1000000000000))
    | 7 => (orderedInterval (-17033361669 / 1000000000000) (-17033361668 / 1000000000000), orderedInterval (-50655872360 / 1000000000000) (-50655872359 / 1000000000000))
    | 8 => (orderedInterval (61208734234 / 1000000000000) (61208734237 / 1000000000000), orderedInterval (11485360524 / 1000000000000) (11485360527 / 1000000000000))
    | 9 => (orderedInterval (42737696475 / 1000000000000) (42737696476 / 1000000000000), orderedInterval (26451790038 / 1000000000000) (26451790039 / 1000000000000))
    | 10 => (orderedInterval (66076584440 / 1000000000000) (66076584458 / 1000000000000), orderedInterval (3917365262 / 1000000000000) (3917365280 / 1000000000000))
    | 11 => (orderedInterval (38922488488 / 1000000000000) (38922488489 / 1000000000000), orderedInterval (30830581412 / 1000000000000) (30830581413 / 1000000000000))
    | 12 => (orderedInterval (16040924079 / 1000000000000) (16040924325 / 1000000000000), orderedInterval (-48884692638 / 1000000000000) (-48884692391 / 1000000000000))
    | 13 => (orderedInterval (9476736476 / 1000000000000) (9476736518 / 1000000000000), orderedInterval (-60150682965 / 1000000000000) (-60150682923 / 1000000000000))
    | 14 => (orderedInterval (43381715273 / 1000000000000) (43381715274 / 1000000000000), orderedInterval (37106412031 / 1000000000000) (37106412032 / 1000000000000))
    | 15 => (orderedInterval (-7979104075 / 1000000000000) (-7979104046 / 1000000000000), orderedInterval (62114884514 / 1000000000000) (62114884543 / 1000000000000))
    | 16 => (orderedInterval (-13159135913 / 1000000000000) (-13159135818 / 1000000000000), orderedInterval (65332243358 / 1000000000000) (65332243454 / 1000000000000))
    | 17 => (orderedInterval (54867436697 / 1000000000000) (54867436708 / 1000000000000), orderedInterval (6952457125 / 1000000000000) (6952457136 / 1000000000000))
    | 18 => (orderedInterval (27956914248 / 1000000000000) (27956915506 / 1000000000000), orderedInterval (-69048533845 / 1000000000000) (-69048532586 / 1000000000000))
    | 19 => (orderedInterval (-65251087122 / 1000000000000) (-65251087121 / 1000000000000), orderedInterval (-47295962930 / 1000000000000) (-47295962929 / 1000000000000))
    | 20 => (orderedInterval (-86430271910 / 1000000000000) (-86430250874 / 1000000000000), orderedInterval (55107405086 / 1000000000000) (55107426122 / 1000000000000))
    | 21 => (orderedInterval (113164004948 / 1000000000000) (113164037693 / 1000000000000), orderedInterval (-82878834226 / 1000000000000) (-82878801481 / 1000000000000))
    | 22 => (orderedInterval (78455452603 / 1000000000000) (78455456527 / 1000000000000), orderedInterval (-31857848439 / 1000000000000) (-31857844515 / 1000000000000))
    | 23 => (orderedInterval (2547141542 / 1000000000000) (2547141552 / 1000000000000), orderedInterval (-72291208938 / 1000000000000) (-72291208929 / 1000000000000))
    | 24 => (orderedInterval (102126412840 / 1000000000000) (102126417126 / 1000000000000), orderedInterval (-45046930125 / 1000000000000) (-45046925839 / 1000000000000))
    | 25 => (orderedInterval (27297563281 / 1000000000000) (27297566563 / 1000000000000), orderedInterval (-48004707103 / 1000000000000) (-48004703821 / 1000000000000))
    | _ => (orderedInterval (51231554395 / 1000000000000) (51231663261 / 1000000000000), orderedInterval (-44132648271 / 1000000000000) (-44132539405 / 1000000000000))
  chunkTarget := fun r b =>
    match r.val with
    | 0 =>
      match b.val with
      | 0 => orderedInterval (7553846770 / 1000000000000) (7553846851 / 1000000000000)
      | 1 => orderedInterval (-2846126007 / 1000000000000) (-2846125981 / 1000000000000)
      | 2 => orderedInterval (2004671362 / 1000000000000) (2004671370 / 1000000000000)
      | 3 => orderedInterval (2834819561 / 1000000000000) (2834819608 / 1000000000000)
      | 4 => orderedInterval (387022701 / 1000000000000) (387022724 / 1000000000000)
      | 5 => orderedInterval (2065736654 / 1000000000000) (2065736672 / 1000000000000)
      | 6 => orderedInterval (-3590651770 / 1000000000000) (-3590650855 / 1000000000000)
      | 7 => orderedInterval (-4064705369 / 1000000000000) (-4064704660 / 1000000000000)
      | _ => orderedInterval (-11218837978 / 1000000000000) (-11218817227 / 1000000000000)
    | 1 =>
      match b.val with
      | 0 => orderedInterval (24452122332 / 1000000000000) (24452122408 / 1000000000000)
      | 1 => orderedInterval (-4735959375 / 1000000000000) (-4735959353 / 1000000000000)
      | 2 => orderedInterval (3495972509 / 1000000000000) (3495972521 / 1000000000000)
      | 3 => orderedInterval (-94776033 / 1000000000000) (-94775937 / 1000000000000)
      | 4 => orderedInterval (-7124851865 / 1000000000000) (-7124851827 / 1000000000000)
      | 5 => orderedInterval (-3405087810 / 1000000000000) (-3405087786 / 1000000000000)
      | 6 => orderedInterval (14586980218 / 1000000000000) (14586980822 / 1000000000000)
      | 7 => orderedInterval (7012701505 / 1000000000000) (7012701766 / 1000000000000)
      | _ => orderedInterval (17426092144 / 1000000000000) (17426118066 / 1000000000000)
    | 2 =>
      match b.val with
      | 0 => orderedInterval (-7953921273 / 1000000000000) (-7953921197 / 1000000000000)
      | 1 => orderedInterval (9573833697 / 1000000000000) (9573833723 / 1000000000000)
      | 2 => orderedInterval (-5230009682 / 1000000000000) (-5230009661 / 1000000000000)
      | 3 => orderedInterval (772611442 / 1000000000000) (772611645 / 1000000000000)
      | 4 => orderedInterval (-42314817 / 1000000000000) (-42314751 / 1000000000000)
      | 5 => orderedInterval (-5805725001 / 1000000000000) (-5805724967 / 1000000000000)
      | 6 => orderedInterval (2598675473 / 1000000000000) (2598675916 / 1000000000000)
      | 7 => orderedInterval (1461318543 / 1000000000000) (1461318666 / 1000000000000)
      | _ => orderedInterval (22226753633 / 1000000000000) (22226786366 / 1000000000000)
    | 3 =>
      match b.val with
      | 0 => orderedInterval (-22569692753 / 1000000000000) (-22569692673 / 1000000000000)
      | 1 => orderedInterval (6334609598 / 1000000000000) (6334609633 / 1000000000000)
      | 2 => orderedInterval (-12915004640 / 1000000000000) (-12915004603 / 1000000000000)
      | 3 => orderedInterval (-775885480 / 1000000000000) (-775885039 / 1000000000000)
      | 4 => orderedInterval (12594497827 / 1000000000000) (12594497947 / 1000000000000)
      | 5 => orderedInterval (4530693405 / 1000000000000) (4530693456 / 1000000000000)
      | 6 => orderedInterval (-13867703255 / 1000000000000) (-13867702901 / 1000000000000)
      | 7 => orderedInterval (-7424068286 / 1000000000000) (-7424068212 / 1000000000000)
      | _ => orderedInterval (-41156169019 / 1000000000000) (-41156127780 / 1000000000000)
    | _ =>
      match b.val with
      | 0 => orderedInterval (8697915403 / 1000000000000) (8697915489 / 1000000000000)
      | 1 => orderedInterval (-24172532941 / 1000000000000) (-24172532889 / 1000000000000)
      | 2 => orderedInterval (14955398802 / 1000000000000) (14955398869 / 1000000000000)
      | 3 => orderedInterval (-23836493162 / 1000000000000) (-23836492185 / 1000000000000)
      | 4 => orderedInterval (-3399256895 / 1000000000000) (-3399256672 / 1000000000000)
      | 5 => orderedInterval (17930341992 / 1000000000000) (17930342069 / 1000000000000)
      | 6 => orderedInterval (-2802290765 / 1000000000000) (-2802290455 / 1000000000000)
      | 7 => orderedInterval (-851749881 / 1000000000000) (-851749826 / 1000000000000)
      | _ => orderedInterval (-48674878374 / 1000000000000) (-48674825695 / 1000000000000)
  coefficientTarget := fun i =>
    match i.val with
    | 0 => orderedInterval (-6874224076 / 1000000000000) (-6874201498 / 1000000000000)
    | 1 => orderedInterval (51613193625 / 1000000000000) (51613220680 / 1000000000000)
    | 2 => orderedInterval (17601222015 / 1000000000000) (17601255740 / 1000000000000)
    | 3 => orderedInterval (-75248722603 / 1000000000000) (-75248680172 / 1000000000000)
    | _ => orderedInterval (-62153545821 / 1000000000000) (-62153491295 / 1000000000000)

theorem compactCertificate235_stateChecks0 :
    compactCertificate235.stateChecks 0 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 36 12 (225 / 2)) (orderedInterval (13981635826 / 1000000000000) (13981635828 / 1000000000000), orderedInterval (73852732621 / 1000000000000) (73852732623 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 26 12 (13258718531109 / 160000000000)) (orderedInterval (80774910372 / 1000000000000) (80774914962 / 1000000000000), orderedInterval (-34513010138 / 1000000000000) (-34513005548 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 43 12 (4287597155397 / 32000000000)) (orderedInterval (21460904255 / 1000000000000) (21460904743 / 1000000000000), orderedInterval (-65584255822 / 1000000000000) (-65584255333 / 1000000000000))) = true
  norm_num [besselStateAtRationalPoint, besselIntervalStepZero,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, besselZeroTransition,
    besselInitial, besselGridStateAt, besselGridStateBlock00, besselGridStateBlock01,
    besselGridStateBlock02, besselGridStateBlock03, besselGridStateBlock04,
    besselGridStateBlock05, besselGridStateBlock06, besselGridStateBlock07,
    besselGridStateBlock08, besselGridStateBlock09, besselGridStateBlock10,
    besselGridStateBlock11, besselGridStateBlock12, besselGridStateBlock13,
    besselGridStateBlock14, besselGridState008, besselGridState010, besselGridState016, besselGridState019, besselGridState021, besselGridState026, besselGridState028, besselGridState031, besselGridState036, besselGridState037, besselGridState039, besselGridState041, besselGridState043, besselGridState044, besselGridState046, besselGridState052, besselGridState055, besselGridState056, besselGridState062, besselGridState066, besselGridState067, besselGridState071, besselGridState077, besselGridState080, besselGridState082, besselStateSubset, linearInterval, widenInterval,
    rationalErrorInterval, rationalIntervalSubset, orderedInterval, Finset.sum_range_succ,
    IntervalRat.add, IntervalRat.mul, IntervalRat.scale, IntervalRat.singleton]

theorem compactCertificate235_stateChecks1 :
    compactCertificate235.stateChecks 3 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 8 12 (3868860999663 / 160000000000)) (orderedInterval (-27788419242 / 1000000000000) (-27788419098 / 1000000000000), orderedInterval (160452547646 / 1000000000000) (160452547790 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 21 12 (10392304845411 / 160000000000)) (orderedInterval (23346723629 / 1000000000000) (23346723905 / 1000000000000), orderedInterval (-96390892300 / 1000000000000) (-96390892024 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 56 12 (28217129246487 / 160000000000)) (orderedInterval (56267555039 / 1000000000000) (56267555040 / 1000000000000), orderedInterval (20906695711 / 1000000000000) (20906695712 / 1000000000000))) = true
  norm_num [besselStateAtRationalPoint, besselIntervalStepZero,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, besselZeroTransition,
    besselInitial, besselGridStateAt, besselGridStateBlock00, besselGridStateBlock01,
    besselGridStateBlock02, besselGridStateBlock03, besselGridStateBlock04,
    besselGridStateBlock05, besselGridStateBlock06, besselGridStateBlock07,
    besselGridStateBlock08, besselGridStateBlock09, besselGridStateBlock10,
    besselGridStateBlock11, besselGridStateBlock12, besselGridStateBlock13,
    besselGridStateBlock14, besselGridState008, besselGridState010, besselGridState016, besselGridState019, besselGridState021, besselGridState026, besselGridState028, besselGridState031, besselGridState036, besselGridState037, besselGridState039, besselGridState041, besselGridState043, besselGridState044, besselGridState046, besselGridState052, besselGridState055, besselGridState056, besselGridState062, besselGridState066, besselGridState067, besselGridState071, besselGridState077, besselGridState080, besselGridState082, besselStateSubset, linearInterval, widenInterval,
    rationalErrorInterval, rationalIntervalSubset, orderedInterval, Finset.sum_range_succ,
    IntervalRat.add, IntervalRat.mul, IntervalRat.scale, IntervalRat.singleton]

theorem compactCertificate235_stateChecks2 :
    compactCertificate235.stateChecks 6 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 41 12 (20784609690831 / 160000000000)) (orderedInterval (-66621776093 / 1000000000000) (-66621773784 / 1000000000000), orderedInterval (21755513894 / 1000000000000) (21755516203 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 71 12 (35614782967563 / 160000000000)) (orderedInterval (-17033361669 / 1000000000000) (-17033361668 / 1000000000000), orderedInterval (-50655872360 / 1000000000000) (-50655872359 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 52 12 (26233687939617 / 160000000000)) (orderedInterval (61208734234 / 1000000000000) (61208734237 / 1000000000000), orderedInterval (11485360524 / 1000000000000) (11485360527 / 1000000000000))) = true
  norm_num [besselStateAtRationalPoint, besselIntervalStepZero,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, besselZeroTransition,
    besselInitial, besselGridStateAt, besselGridStateBlock00, besselGridStateBlock01,
    besselGridStateBlock02, besselGridStateBlock03, besselGridStateBlock04,
    besselGridStateBlock05, besselGridStateBlock06, besselGridStateBlock07,
    besselGridStateBlock08, besselGridStateBlock09, besselGridStateBlock10,
    besselGridStateBlock11, besselGridStateBlock12, besselGridStateBlock13,
    besselGridStateBlock14, besselGridState008, besselGridState010, besselGridState016, besselGridState019, besselGridState021, besselGridState026, besselGridState028, besselGridState031, besselGridState036, besselGridState037, besselGridState039, besselGridState041, besselGridState043, besselGridState044, besselGridState046, besselGridState052, besselGridState055, besselGridState056, besselGridState062, besselGridState066, besselGridState067, besselGridState071, besselGridState077, besselGridState080, besselGridState082, besselStateSubset, linearInterval, widenInterval,
    rationalErrorInterval, rationalIntervalSubset, orderedInterval, Finset.sum_range_succ,
    IntervalRat.add, IntervalRat.mul, IntervalRat.scale, IntervalRat.singleton]

theorem compactCertificate235_stateChecks3 :
    compactCertificate235.stateChecks 9 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 80 12 (40249223594991 / 160000000000)) (orderedInterval (42737696475 / 1000000000000) (42737696476 / 1000000000000), orderedInterval (26451790038 / 1000000000000) (26451790039 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 46 12 (23237900077239 / 160000000000)) (orderedInterval (66076584440 / 1000000000000) (66076584458 / 1000000000000), orderedInterval (3917365262 / 1000000000000) (3917365280 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 82 12 (41236061473251 / 160000000000)) (orderedInterval (38922488488 / 1000000000000) (38922488489 / 1000000000000), orderedInterval (30830581412 / 1000000000000) (30830581413 / 1000000000000))) = true
  norm_num [besselStateAtRationalPoint, besselIntervalStepZero,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, besselZeroTransition,
    besselInitial, besselGridStateAt, besselGridStateBlock00, besselGridStateBlock01,
    besselGridStateBlock02, besselGridStateBlock03, besselGridStateBlock04,
    besselGridStateBlock05, besselGridStateBlock06, besselGridStateBlock07,
    besselGridStateBlock08, besselGridStateBlock09, besselGridStateBlock10,
    besselGridStateBlock11, besselGridStateBlock12, besselGridStateBlock13,
    besselGridStateBlock14, besselGridState008, besselGridState010, besselGridState016, besselGridState019, besselGridState021, besselGridState026, besselGridState028, besselGridState031, besselGridState036, besselGridState037, besselGridState039, besselGridState041, besselGridState043, besselGridState044, besselGridState046, besselGridState052, besselGridState055, besselGridState056, besselGridState062, besselGridState066, besselGridState067, besselGridState071, besselGridState077, besselGridState080, besselGridState082, besselStateSubset, linearInterval, widenInterval,
    rationalErrorInterval, rationalIntervalSubset, orderedInterval, Finset.sum_range_succ,
    IntervalRat.add, IntervalRat.mul, IntervalRat.scale, IntervalRat.singleton]

theorem compactCertificate235_stateChecks4 :
    compactCertificate235.stateChecks 12 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 77 12 (38528077629519 / 160000000000)) (orderedInterval (16040924079 / 1000000000000) (16040924325 / 1000000000000), orderedInterval (-48884692638 / 1000000000000) (-48884692391 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 55 12 (27495454169727 / 160000000000)) (orderedInterval (9476736476 / 1000000000000) (9476736518 / 1000000000000), orderedInterval (-60150682965 / 1000000000000) (-60150682923 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 62 12 (31176914536233 / 160000000000)) (orderedInterval (43381715273 / 1000000000000) (43381715274 / 1000000000000), orderedInterval (37106412031 / 1000000000000) (37106412032 / 1000000000000))) = true
  norm_num [besselStateAtRationalPoint, besselIntervalStepZero,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, besselZeroTransition,
    besselInitial, besselGridStateAt, besselGridStateBlock00, besselGridStateBlock01,
    besselGridStateBlock02, besselGridStateBlock03, besselGridStateBlock04,
    besselGridStateBlock05, besselGridStateBlock06, besselGridStateBlock07,
    besselGridStateBlock08, besselGridStateBlock09, besselGridStateBlock10,
    besselGridStateBlock11, besselGridStateBlock12, besselGridStateBlock13,
    besselGridStateBlock14, besselGridState008, besselGridState010, besselGridState016, besselGridState019, besselGridState021, besselGridState026, besselGridState028, besselGridState031, besselGridState036, besselGridState037, besselGridState039, besselGridState041, besselGridState043, besselGridState044, besselGridState046, besselGridState052, besselGridState055, besselGridState056, besselGridState062, besselGridState066, besselGridState067, besselGridState071, besselGridState077, besselGridState080, besselGridState082, besselStateSubset, linearInterval, widenInterval,
    rationalErrorInterval, rationalIntervalSubset, orderedInterval, Finset.sum_range_succ,
    IntervalRat.add, IntervalRat.mul, IntervalRat.scale, IntervalRat.singleton]

theorem compactCertificate235_stateChecks5 :
    compactCertificate235.stateChecks 15 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 52 12 (25992060983577 / 160000000000)) (orderedInterval (-7979104075 / 1000000000000) (-7979104046 / 1000000000000), orderedInterval (62114884514 / 1000000000000) (62114884543 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 46 12 (22964774139117 / 160000000000)) (orderedInterval (-13159135913 / 1000000000000) (-13159135818 / 1000000000000), orderedInterval (65332243358 / 1000000000000) (65332243454 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 66 12 (6656086640583 / 32000000000)) (orderedInterval (54867436697 / 1000000000000) (54867436708 / 1000000000000), orderedInterval (6952457125 / 1000000000000) (6952457136 / 1000000000000))) = true
  norm_num [besselStateAtRationalPoint, besselIntervalStepZero,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, besselZeroTransition,
    besselInitial, besselGridStateAt, besselGridStateBlock00, besselGridStateBlock01,
    besselGridStateBlock02, besselGridStateBlock03, besselGridStateBlock04,
    besselGridStateBlock05, besselGridStateBlock06, besselGridStateBlock07,
    besselGridStateBlock08, besselGridStateBlock09, besselGridStateBlock10,
    besselGridStateBlock11, besselGridStateBlock12, besselGridStateBlock13,
    besselGridStateBlock14, besselGridState008, besselGridState010, besselGridState016, besselGridState019, besselGridState021, besselGridState026, besselGridState028, besselGridState031, besselGridState036, besselGridState037, besselGridState039, besselGridState041, besselGridState043, besselGridState044, besselGridState046, besselGridState052, besselGridState055, besselGridState056, besselGridState062, besselGridState066, besselGridState067, besselGridState071, besselGridState077, besselGridState080, besselGridState082, besselStateSubset, linearInterval, widenInterval,
    rationalErrorInterval, rationalIntervalSubset, orderedInterval, Finset.sum_range_succ,
    IntervalRat.add, IntervalRat.mul, IntervalRat.scale, IntervalRat.singleton]

theorem compactCertificate235_stateChecks6 :
    compactCertificate235.stateChecks 18 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 37 12 (18411085938501 / 160000000000)) (orderedInterval (27956914248 / 1000000000000) (27956915506 / 1000000000000), orderedInterval (-69048533845 / 1000000000000) (-69048532586 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 31 12 (15607281447261 / 160000000000)) (orderedInterval (-65251087122 / 1000000000000) (-65251087121 / 1000000000000), orderedInterval (-47295962930 / 1000000000000) (-47295962929 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 19 12 (9766312060383 / 160000000000)) (orderedInterval (-86430271910 / 1000000000000) (-86430250874 / 1000000000000), orderedInterval (55107405086 / 1000000000000) (55107426122 / 1000000000000))) = true
  norm_num [besselStateAtRationalPoint, besselIntervalStepZero,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, besselZeroTransition,
    besselInitial, besselGridStateAt, besselGridStateBlock00, besselGridStateBlock01,
    besselGridStateBlock02, besselGridStateBlock03, besselGridStateBlock04,
    besselGridStateBlock05, besselGridStateBlock06, besselGridStateBlock07,
    besselGridStateBlock08, besselGridStateBlock09, besselGridStateBlock10,
    besselGridStateBlock11, besselGridStateBlock12, besselGridStateBlock13,
    besselGridStateBlock14, besselGridState008, besselGridState010, besselGridState016, besselGridState019, besselGridState021, besselGridState026, besselGridState028, besselGridState031, besselGridState036, besselGridState037, besselGridState039, besselGridState041, besselGridState043, besselGridState044, besselGridState046, besselGridState052, besselGridState055, besselGridState056, besselGridState062, besselGridState066, besselGridState067, besselGridState071, besselGridState077, besselGridState080, besselGridState082, besselStateSubset, linearInterval, widenInterval,
    rationalErrorInterval, rationalIntervalSubset, orderedInterval, Finset.sum_range_succ,
    IntervalRat.add, IntervalRat.mul, IntervalRat.scale, IntervalRat.singleton]

theorem compactCertificate235_stateChecks7 :
    compactCertificate235.stateChecks 21 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 10 12 (5252355107361 / 160000000000)) (orderedInterval (113164004948 / 1000000000000) (113164037693 / 1000000000000), orderedInterval (-82878834226 / 1000000000000) (-82878801481 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 28 12 (14261165845083 / 160000000000)) (orderedInterval (78455452603 / 1000000000000) (78455456527 / 1000000000000), orderedInterval (-31857848439 / 1000000000000) (-31857844515 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 39 12 (19472402736891 / 160000000000)) (orderedInterval (2547141542 / 1000000000000) (2547141552 / 1000000000000), orderedInterval (-72291208938 / 1000000000000) (-72291208929 / 1000000000000))) = true
  norm_num [besselStateAtRationalPoint, besselIntervalStepZero,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, besselZeroTransition,
    besselInitial, besselGridStateAt, besselGridStateBlock00, besselGridStateBlock01,
    besselGridStateBlock02, besselGridStateBlock03, besselGridStateBlock04,
    besselGridStateBlock05, besselGridStateBlock06, besselGridStateBlock07,
    besselGridStateBlock08, besselGridStateBlock09, besselGridStateBlock10,
    besselGridStateBlock11, besselGridStateBlock12, besselGridStateBlock13,
    besselGridStateBlock14, besselGridState008, besselGridState010, besselGridState016, besselGridState019, besselGridState021, besselGridState026, besselGridState028, besselGridState031, besselGridState036, besselGridState037, besselGridState039, besselGridState041, besselGridState043, besselGridState044, besselGridState046, besselGridState052, besselGridState055, besselGridState056, besselGridState062, besselGridState066, besselGridState067, besselGridState071, besselGridState077, besselGridState080, besselGridState082, besselStateSubset, linearInterval, widenInterval,
    rationalErrorInterval, rationalIntervalSubset, orderedInterval, Finset.sum_range_succ,
    IntervalRat.add, IntervalRat.mul, IntervalRat.scale, IntervalRat.singleton]

theorem compactCertificate235_stateChecks8 :
    compactCertificate235.stateChecks 24 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 16 12 (8233687939617 / 160000000000)) (orderedInterval (102126412840 / 1000000000000) (102126417126 / 1000000000000), orderedInterval (-45046930125 / 1000000000000) (-45046925839 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 67 12 (33469484353857 / 160000000000)) (orderedInterval (27297563281 / 1000000000000) (27297566563 / 1000000000000), orderedInterval (-48004707103 / 1000000000000) (-48004703821 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 44 12 (22356064436463 / 160000000000)) (orderedInterval (51231554395 / 1000000000000) (51231663261 / 1000000000000), orderedInterval (-44132648271 / 1000000000000) (-44132539405 / 1000000000000))) = true
  norm_num [besselStateAtRationalPoint, besselIntervalStepZero,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, besselZeroTransition,
    besselInitial, besselGridStateAt, besselGridStateBlock00, besselGridStateBlock01,
    besselGridStateBlock02, besselGridStateBlock03, besselGridStateBlock04,
    besselGridStateBlock05, besselGridStateBlock06, besselGridStateBlock07,
    besselGridStateBlock08, besselGridStateBlock09, besselGridStateBlock10,
    besselGridStateBlock11, besselGridStateBlock12, besselGridStateBlock13,
    besselGridStateBlock14, besselGridState008, besselGridState010, besselGridState016, besselGridState019, besselGridState021, besselGridState026, besselGridState028, besselGridState031, besselGridState036, besselGridState037, besselGridState039, besselGridState041, besselGridState043, besselGridState044, besselGridState046, besselGridState052, besselGridState055, besselGridState056, besselGridState062, besselGridState066, besselGridState067, besselGridState071, besselGridState077, besselGridState080, besselGridState082, besselStateSubset, linearInterval, widenInterval,
    rationalErrorInterval, rationalIntervalSubset, orderedInterval, Finset.sum_range_succ,
    IntervalRat.add, IntervalRat.mul, IntervalRat.scale, IntervalRat.singleton]

theorem compactCertificate235_states : ∀ j,
    BesselStateValid (compactCertificate235.point j) (compactCertificate235.state j) :=
  compactCertificate235.statesValid_of_checks3 compactCertificate235_stateChecks0
    compactCertificate235_stateChecks1 compactCertificate235_stateChecks2
    compactCertificate235_stateChecks3 compactCertificate235_stateChecks4
    compactCertificate235_stateChecks5 compactCertificate235_stateChecks6
    compactCertificate235_stateChecks7 compactCertificate235_stateChecks8

theorem compactCertificate235_chunkChecks0_0 :
    compactCertificate235.chunkChecks (0 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 0) <| besselDerivativeNearFromState (225 / 2) 0 (IntervalRat.scale (225 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (13981635826 / 1000000000000) (13981635828 / 1000000000000), orderedInterval (73852732621 / 1000000000000) (73852732623 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 0) <| besselDerivativeNearFromState (13258718531109 / 160000000000) 0 (IntervalRat.scale (225 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (80774910372 / 1000000000000) (80774914962 / 1000000000000), orderedInterval (-34513010138 / 1000000000000) (-34513005548 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 0) <| besselDerivativeNearFromState (4287597155397 / 32000000000) 0 (IntervalRat.scale (225 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (21460904255 / 1000000000000) (21460904743 / 1000000000000), orderedInterval (-65584255822 / 1000000000000) (-65584255333 / 1000000000000)))) (orderedInterval (7553846770 / 1000000000000) (7553846851 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 0) <| besselDerivativeNearFromState (3868860999663 / 160000000000) 0 (IntervalRat.scale (225 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-27788419242 / 1000000000000) (-27788419098 / 1000000000000), orderedInterval (160452547646 / 1000000000000) (160452547790 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 0) <| besselDerivativeNearFromState (10392304845411 / 160000000000) 0 (IntervalRat.scale (225 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (23346723629 / 1000000000000) (23346723905 / 1000000000000), orderedInterval (-96390892300 / 1000000000000) (-96390892024 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 0) <| besselDerivativeNearFromState (28217129246487 / 160000000000) 0 (IntervalRat.scale (225 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (56267555039 / 1000000000000) (56267555040 / 1000000000000), orderedInterval (20906695711 / 1000000000000) (20906695712 / 1000000000000)))) (orderedInterval (-2846126007 / 1000000000000) (-2846125981 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 0) <| besselDerivativeNearFromState (20784609690831 / 160000000000) 0 (IntervalRat.scale (225 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-66621776093 / 1000000000000) (-66621773784 / 1000000000000), orderedInterval (21755513894 / 1000000000000) (21755516203 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 0) <| besselDerivativeNearFromState (35614782967563 / 160000000000) 0 (IntervalRat.scale (225 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-17033361669 / 1000000000000) (-17033361668 / 1000000000000), orderedInterval (-50655872360 / 1000000000000) (-50655872359 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 0) <| besselDerivativeNearFromState (26233687939617 / 160000000000) 0 (IntervalRat.scale (225 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (61208734234 / 1000000000000) (61208734237 / 1000000000000), orderedInterval (11485360524 / 1000000000000) (11485360527 / 1000000000000)))) (orderedInterval (2004671362 / 1000000000000) (2004671370 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate235_chunkChecks0_1 :
    compactCertificate235.chunkChecks (0 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 0) <| besselDerivativeNearFromState (40249223594991 / 160000000000) 0 (IntervalRat.scale (225 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (42737696475 / 1000000000000) (42737696476 / 1000000000000), orderedInterval (26451790038 / 1000000000000) (26451790039 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 0) <| besselDerivativeNearFromState (23237900077239 / 160000000000) 0 (IntervalRat.scale (225 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (66076584440 / 1000000000000) (66076584458 / 1000000000000), orderedInterval (3917365262 / 1000000000000) (3917365280 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 0) <| besselDerivativeNearFromState (41236061473251 / 160000000000) 0 (IntervalRat.scale (225 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (38922488488 / 1000000000000) (38922488489 / 1000000000000), orderedInterval (30830581412 / 1000000000000) (30830581413 / 1000000000000)))) (orderedInterval (2834819561 / 1000000000000) (2834819608 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 0) <| besselDerivativeNearFromState (38528077629519 / 160000000000) 0 (IntervalRat.scale (225 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (16040924079 / 1000000000000) (16040924325 / 1000000000000), orderedInterval (-48884692638 / 1000000000000) (-48884692391 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 0) <| besselDerivativeNearFromState (27495454169727 / 160000000000) 0 (IntervalRat.scale (225 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (9476736476 / 1000000000000) (9476736518 / 1000000000000), orderedInterval (-60150682965 / 1000000000000) (-60150682923 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 0) <| besselDerivativeNearFromState (31176914536233 / 160000000000) 0 (IntervalRat.scale (225 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (43381715273 / 1000000000000) (43381715274 / 1000000000000), orderedInterval (37106412031 / 1000000000000) (37106412032 / 1000000000000)))) (orderedInterval (387022701 / 1000000000000) (387022724 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 0) <| besselDerivativeNearFromState (25992060983577 / 160000000000) 0 (IntervalRat.scale (225 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-7979104075 / 1000000000000) (-7979104046 / 1000000000000), orderedInterval (62114884514 / 1000000000000) (62114884543 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 0) <| besselDerivativeNearFromState (22964774139117 / 160000000000) 0 (IntervalRat.scale (225 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-13159135913 / 1000000000000) (-13159135818 / 1000000000000), orderedInterval (65332243358 / 1000000000000) (65332243454 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 0) <| besselDerivativeNearFromState (6656086640583 / 32000000000) 0 (IntervalRat.scale (225 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (54867436697 / 1000000000000) (54867436708 / 1000000000000), orderedInterval (6952457125 / 1000000000000) (6952457136 / 1000000000000)))) (orderedInterval (2065736654 / 1000000000000) (2065736672 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate235_chunkChecks0_2 :
    compactCertificate235.chunkChecks (0 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 0) <| besselDerivativeNearFromState (18411085938501 / 160000000000) 0 (IntervalRat.scale (225 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (27956914248 / 1000000000000) (27956915506 / 1000000000000), orderedInterval (-69048533845 / 1000000000000) (-69048532586 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 0) <| besselDerivativeNearFromState (15607281447261 / 160000000000) 0 (IntervalRat.scale (225 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-65251087122 / 1000000000000) (-65251087121 / 1000000000000), orderedInterval (-47295962930 / 1000000000000) (-47295962929 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 0) <| besselDerivativeNearFromState (9766312060383 / 160000000000) 0 (IntervalRat.scale (225 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-86430271910 / 1000000000000) (-86430250874 / 1000000000000), orderedInterval (55107405086 / 1000000000000) (55107426122 / 1000000000000)))) (orderedInterval (-3590651770 / 1000000000000) (-3590650855 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 0) <| besselDerivativeNearFromState (5252355107361 / 160000000000) 0 (IntervalRat.scale (225 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (113164004948 / 1000000000000) (113164037693 / 1000000000000), orderedInterval (-82878834226 / 1000000000000) (-82878801481 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 0) <| besselDerivativeNearFromState (14261165845083 / 160000000000) 0 (IntervalRat.scale (225 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (78455452603 / 1000000000000) (78455456527 / 1000000000000), orderedInterval (-31857848439 / 1000000000000) (-31857844515 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 0) <| besselDerivativeNearFromState (19472402736891 / 160000000000) 0 (IntervalRat.scale (225 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (2547141542 / 1000000000000) (2547141552 / 1000000000000), orderedInterval (-72291208938 / 1000000000000) (-72291208929 / 1000000000000)))) (orderedInterval (-4064705369 / 1000000000000) (-4064704660 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 0) <| besselDerivativeNearFromState (8233687939617 / 160000000000) 0 (IntervalRat.scale (225 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (102126412840 / 1000000000000) (102126417126 / 1000000000000), orderedInterval (-45046930125 / 1000000000000) (-45046925839 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 0) <| besselDerivativeNearFromState (33469484353857 / 160000000000) 0 (IntervalRat.scale (225 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (27297563281 / 1000000000000) (27297566563 / 1000000000000), orderedInterval (-48004707103 / 1000000000000) (-48004703821 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 0) <| besselDerivativeNearFromState (22356064436463 / 160000000000) 0 (IntervalRat.scale (225 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (51231554395 / 1000000000000) (51231663261 / 1000000000000), orderedInterval (-44132648271 / 1000000000000) (-44132539405 / 1000000000000)))) (orderedInterval (-11218837978 / 1000000000000) (-11218817227 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate235_chunkChecks0 :
    compactCertificate235.chunkChecks (0 : Fin 5) 0 9 = true :=
  compactCertificate235.chunkChecks_nine_of_three (0 : Fin 5) compactCertificate235_chunkChecks0_0
    compactCertificate235_chunkChecks0_1 compactCertificate235_chunkChecks0_2

theorem compactCertificate235_chunkChecks1_0 :
    compactCertificate235.chunkChecks (1 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 1) <| besselDerivativeNearFromState (225 / 2) 1 (IntervalRat.scale (225 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (13981635826 / 1000000000000) (13981635828 / 1000000000000), orderedInterval (73852732621 / 1000000000000) (73852732623 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 1) <| besselDerivativeNearFromState (13258718531109 / 160000000000) 1 (IntervalRat.scale (225 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (80774910372 / 1000000000000) (80774914962 / 1000000000000), orderedInterval (-34513010138 / 1000000000000) (-34513005548 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 1) <| besselDerivativeNearFromState (4287597155397 / 32000000000) 1 (IntervalRat.scale (225 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (21460904255 / 1000000000000) (21460904743 / 1000000000000), orderedInterval (-65584255822 / 1000000000000) (-65584255333 / 1000000000000)))) (orderedInterval (24452122332 / 1000000000000) (24452122408 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 1) <| besselDerivativeNearFromState (3868860999663 / 160000000000) 1 (IntervalRat.scale (225 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-27788419242 / 1000000000000) (-27788419098 / 1000000000000), orderedInterval (160452547646 / 1000000000000) (160452547790 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 1) <| besselDerivativeNearFromState (10392304845411 / 160000000000) 1 (IntervalRat.scale (225 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (23346723629 / 1000000000000) (23346723905 / 1000000000000), orderedInterval (-96390892300 / 1000000000000) (-96390892024 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 1) <| besselDerivativeNearFromState (28217129246487 / 160000000000) 1 (IntervalRat.scale (225 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (56267555039 / 1000000000000) (56267555040 / 1000000000000), orderedInterval (20906695711 / 1000000000000) (20906695712 / 1000000000000)))) (orderedInterval (-4735959375 / 1000000000000) (-4735959353 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 1) <| besselDerivativeNearFromState (20784609690831 / 160000000000) 1 (IntervalRat.scale (225 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-66621776093 / 1000000000000) (-66621773784 / 1000000000000), orderedInterval (21755513894 / 1000000000000) (21755516203 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 1) <| besselDerivativeNearFromState (35614782967563 / 160000000000) 1 (IntervalRat.scale (225 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-17033361669 / 1000000000000) (-17033361668 / 1000000000000), orderedInterval (-50655872360 / 1000000000000) (-50655872359 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 1) <| besselDerivativeNearFromState (26233687939617 / 160000000000) 1 (IntervalRat.scale (225 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (61208734234 / 1000000000000) (61208734237 / 1000000000000), orderedInterval (11485360524 / 1000000000000) (11485360527 / 1000000000000)))) (orderedInterval (3495972509 / 1000000000000) (3495972521 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate235_chunkChecks1_1 :
    compactCertificate235.chunkChecks (1 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 1) <| besselDerivativeNearFromState (40249223594991 / 160000000000) 1 (IntervalRat.scale (225 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (42737696475 / 1000000000000) (42737696476 / 1000000000000), orderedInterval (26451790038 / 1000000000000) (26451790039 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 1) <| besselDerivativeNearFromState (23237900077239 / 160000000000) 1 (IntervalRat.scale (225 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (66076584440 / 1000000000000) (66076584458 / 1000000000000), orderedInterval (3917365262 / 1000000000000) (3917365280 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 1) <| besselDerivativeNearFromState (41236061473251 / 160000000000) 1 (IntervalRat.scale (225 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (38922488488 / 1000000000000) (38922488489 / 1000000000000), orderedInterval (30830581412 / 1000000000000) (30830581413 / 1000000000000)))) (orderedInterval (-94776033 / 1000000000000) (-94775937 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 1) <| besselDerivativeNearFromState (38528077629519 / 160000000000) 1 (IntervalRat.scale (225 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (16040924079 / 1000000000000) (16040924325 / 1000000000000), orderedInterval (-48884692638 / 1000000000000) (-48884692391 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 1) <| besselDerivativeNearFromState (27495454169727 / 160000000000) 1 (IntervalRat.scale (225 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (9476736476 / 1000000000000) (9476736518 / 1000000000000), orderedInterval (-60150682965 / 1000000000000) (-60150682923 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 1) <| besselDerivativeNearFromState (31176914536233 / 160000000000) 1 (IntervalRat.scale (225 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (43381715273 / 1000000000000) (43381715274 / 1000000000000), orderedInterval (37106412031 / 1000000000000) (37106412032 / 1000000000000)))) (orderedInterval (-7124851865 / 1000000000000) (-7124851827 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 1) <| besselDerivativeNearFromState (25992060983577 / 160000000000) 1 (IntervalRat.scale (225 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-7979104075 / 1000000000000) (-7979104046 / 1000000000000), orderedInterval (62114884514 / 1000000000000) (62114884543 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 1) <| besselDerivativeNearFromState (22964774139117 / 160000000000) 1 (IntervalRat.scale (225 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-13159135913 / 1000000000000) (-13159135818 / 1000000000000), orderedInterval (65332243358 / 1000000000000) (65332243454 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 1) <| besselDerivativeNearFromState (6656086640583 / 32000000000) 1 (IntervalRat.scale (225 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (54867436697 / 1000000000000) (54867436708 / 1000000000000), orderedInterval (6952457125 / 1000000000000) (6952457136 / 1000000000000)))) (orderedInterval (-3405087810 / 1000000000000) (-3405087786 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate235_chunkChecks1_2 :
    compactCertificate235.chunkChecks (1 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 1) <| besselDerivativeNearFromState (18411085938501 / 160000000000) 1 (IntervalRat.scale (225 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (27956914248 / 1000000000000) (27956915506 / 1000000000000), orderedInterval (-69048533845 / 1000000000000) (-69048532586 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 1) <| besselDerivativeNearFromState (15607281447261 / 160000000000) 1 (IntervalRat.scale (225 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-65251087122 / 1000000000000) (-65251087121 / 1000000000000), orderedInterval (-47295962930 / 1000000000000) (-47295962929 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 1) <| besselDerivativeNearFromState (9766312060383 / 160000000000) 1 (IntervalRat.scale (225 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-86430271910 / 1000000000000) (-86430250874 / 1000000000000), orderedInterval (55107405086 / 1000000000000) (55107426122 / 1000000000000)))) (orderedInterval (14586980218 / 1000000000000) (14586980822 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 1) <| besselDerivativeNearFromState (5252355107361 / 160000000000) 1 (IntervalRat.scale (225 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (113164004948 / 1000000000000) (113164037693 / 1000000000000), orderedInterval (-82878834226 / 1000000000000) (-82878801481 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 1) <| besselDerivativeNearFromState (14261165845083 / 160000000000) 1 (IntervalRat.scale (225 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (78455452603 / 1000000000000) (78455456527 / 1000000000000), orderedInterval (-31857848439 / 1000000000000) (-31857844515 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 1) <| besselDerivativeNearFromState (19472402736891 / 160000000000) 1 (IntervalRat.scale (225 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (2547141542 / 1000000000000) (2547141552 / 1000000000000), orderedInterval (-72291208938 / 1000000000000) (-72291208929 / 1000000000000)))) (orderedInterval (7012701505 / 1000000000000) (7012701766 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 1) <| besselDerivativeNearFromState (8233687939617 / 160000000000) 1 (IntervalRat.scale (225 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (102126412840 / 1000000000000) (102126417126 / 1000000000000), orderedInterval (-45046930125 / 1000000000000) (-45046925839 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 1) <| besselDerivativeNearFromState (33469484353857 / 160000000000) 1 (IntervalRat.scale (225 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (27297563281 / 1000000000000) (27297566563 / 1000000000000), orderedInterval (-48004707103 / 1000000000000) (-48004703821 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 1) <| besselDerivativeNearFromState (22356064436463 / 160000000000) 1 (IntervalRat.scale (225 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (51231554395 / 1000000000000) (51231663261 / 1000000000000), orderedInterval (-44132648271 / 1000000000000) (-44132539405 / 1000000000000)))) (orderedInterval (17426092144 / 1000000000000) (17426118066 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate235_chunkChecks1 :
    compactCertificate235.chunkChecks (1 : Fin 5) 0 9 = true :=
  compactCertificate235.chunkChecks_nine_of_three (1 : Fin 5) compactCertificate235_chunkChecks1_0
    compactCertificate235_chunkChecks1_1 compactCertificate235_chunkChecks1_2

theorem compactCertificate235_chunkChecks2_0 :
    compactCertificate235.chunkChecks (2 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 2) <| besselDerivativeNearFromState (225 / 2) 2 (IntervalRat.scale (225 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (13981635826 / 1000000000000) (13981635828 / 1000000000000), orderedInterval (73852732621 / 1000000000000) (73852732623 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 2) <| besselDerivativeNearFromState (13258718531109 / 160000000000) 2 (IntervalRat.scale (225 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (80774910372 / 1000000000000) (80774914962 / 1000000000000), orderedInterval (-34513010138 / 1000000000000) (-34513005548 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 2) <| besselDerivativeNearFromState (4287597155397 / 32000000000) 2 (IntervalRat.scale (225 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (21460904255 / 1000000000000) (21460904743 / 1000000000000), orderedInterval (-65584255822 / 1000000000000) (-65584255333 / 1000000000000)))) (orderedInterval (-7953921273 / 1000000000000) (-7953921197 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 2) <| besselDerivativeNearFromState (3868860999663 / 160000000000) 2 (IntervalRat.scale (225 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-27788419242 / 1000000000000) (-27788419098 / 1000000000000), orderedInterval (160452547646 / 1000000000000) (160452547790 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 2) <| besselDerivativeNearFromState (10392304845411 / 160000000000) 2 (IntervalRat.scale (225 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (23346723629 / 1000000000000) (23346723905 / 1000000000000), orderedInterval (-96390892300 / 1000000000000) (-96390892024 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 2) <| besselDerivativeNearFromState (28217129246487 / 160000000000) 2 (IntervalRat.scale (225 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (56267555039 / 1000000000000) (56267555040 / 1000000000000), orderedInterval (20906695711 / 1000000000000) (20906695712 / 1000000000000)))) (orderedInterval (9573833697 / 1000000000000) (9573833723 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 2) <| besselDerivativeNearFromState (20784609690831 / 160000000000) 2 (IntervalRat.scale (225 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-66621776093 / 1000000000000) (-66621773784 / 1000000000000), orderedInterval (21755513894 / 1000000000000) (21755516203 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 2) <| besselDerivativeNearFromState (35614782967563 / 160000000000) 2 (IntervalRat.scale (225 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-17033361669 / 1000000000000) (-17033361668 / 1000000000000), orderedInterval (-50655872360 / 1000000000000) (-50655872359 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 2) <| besselDerivativeNearFromState (26233687939617 / 160000000000) 2 (IntervalRat.scale (225 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (61208734234 / 1000000000000) (61208734237 / 1000000000000), orderedInterval (11485360524 / 1000000000000) (11485360527 / 1000000000000)))) (orderedInterval (-5230009682 / 1000000000000) (-5230009661 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate235_chunkChecks2_1 :
    compactCertificate235.chunkChecks (2 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 2) <| besselDerivativeNearFromState (40249223594991 / 160000000000) 2 (IntervalRat.scale (225 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (42737696475 / 1000000000000) (42737696476 / 1000000000000), orderedInterval (26451790038 / 1000000000000) (26451790039 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 2) <| besselDerivativeNearFromState (23237900077239 / 160000000000) 2 (IntervalRat.scale (225 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (66076584440 / 1000000000000) (66076584458 / 1000000000000), orderedInterval (3917365262 / 1000000000000) (3917365280 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 2) <| besselDerivativeNearFromState (41236061473251 / 160000000000) 2 (IntervalRat.scale (225 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (38922488488 / 1000000000000) (38922488489 / 1000000000000), orderedInterval (30830581412 / 1000000000000) (30830581413 / 1000000000000)))) (orderedInterval (772611442 / 1000000000000) (772611645 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 2) <| besselDerivativeNearFromState (38528077629519 / 160000000000) 2 (IntervalRat.scale (225 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (16040924079 / 1000000000000) (16040924325 / 1000000000000), orderedInterval (-48884692638 / 1000000000000) (-48884692391 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 2) <| besselDerivativeNearFromState (27495454169727 / 160000000000) 2 (IntervalRat.scale (225 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (9476736476 / 1000000000000) (9476736518 / 1000000000000), orderedInterval (-60150682965 / 1000000000000) (-60150682923 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 2) <| besselDerivativeNearFromState (31176914536233 / 160000000000) 2 (IntervalRat.scale (225 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (43381715273 / 1000000000000) (43381715274 / 1000000000000), orderedInterval (37106412031 / 1000000000000) (37106412032 / 1000000000000)))) (orderedInterval (-42314817 / 1000000000000) (-42314751 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 2) <| besselDerivativeNearFromState (25992060983577 / 160000000000) 2 (IntervalRat.scale (225 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-7979104075 / 1000000000000) (-7979104046 / 1000000000000), orderedInterval (62114884514 / 1000000000000) (62114884543 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 2) <| besselDerivativeNearFromState (22964774139117 / 160000000000) 2 (IntervalRat.scale (225 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-13159135913 / 1000000000000) (-13159135818 / 1000000000000), orderedInterval (65332243358 / 1000000000000) (65332243454 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 2) <| besselDerivativeNearFromState (6656086640583 / 32000000000) 2 (IntervalRat.scale (225 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (54867436697 / 1000000000000) (54867436708 / 1000000000000), orderedInterval (6952457125 / 1000000000000) (6952457136 / 1000000000000)))) (orderedInterval (-5805725001 / 1000000000000) (-5805724967 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate235_chunkChecks2_2 :
    compactCertificate235.chunkChecks (2 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 2) <| besselDerivativeNearFromState (18411085938501 / 160000000000) 2 (IntervalRat.scale (225 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (27956914248 / 1000000000000) (27956915506 / 1000000000000), orderedInterval (-69048533845 / 1000000000000) (-69048532586 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 2) <| besselDerivativeNearFromState (15607281447261 / 160000000000) 2 (IntervalRat.scale (225 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-65251087122 / 1000000000000) (-65251087121 / 1000000000000), orderedInterval (-47295962930 / 1000000000000) (-47295962929 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 2) <| besselDerivativeNearFromState (9766312060383 / 160000000000) 2 (IntervalRat.scale (225 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-86430271910 / 1000000000000) (-86430250874 / 1000000000000), orderedInterval (55107405086 / 1000000000000) (55107426122 / 1000000000000)))) (orderedInterval (2598675473 / 1000000000000) (2598675916 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 2) <| besselDerivativeNearFromState (5252355107361 / 160000000000) 2 (IntervalRat.scale (225 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (113164004948 / 1000000000000) (113164037693 / 1000000000000), orderedInterval (-82878834226 / 1000000000000) (-82878801481 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 2) <| besselDerivativeNearFromState (14261165845083 / 160000000000) 2 (IntervalRat.scale (225 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (78455452603 / 1000000000000) (78455456527 / 1000000000000), orderedInterval (-31857848439 / 1000000000000) (-31857844515 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 2) <| besselDerivativeNearFromState (19472402736891 / 160000000000) 2 (IntervalRat.scale (225 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (2547141542 / 1000000000000) (2547141552 / 1000000000000), orderedInterval (-72291208938 / 1000000000000) (-72291208929 / 1000000000000)))) (orderedInterval (1461318543 / 1000000000000) (1461318666 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 2) <| besselDerivativeNearFromState (8233687939617 / 160000000000) 2 (IntervalRat.scale (225 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (102126412840 / 1000000000000) (102126417126 / 1000000000000), orderedInterval (-45046930125 / 1000000000000) (-45046925839 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 2) <| besselDerivativeNearFromState (33469484353857 / 160000000000) 2 (IntervalRat.scale (225 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (27297563281 / 1000000000000) (27297566563 / 1000000000000), orderedInterval (-48004707103 / 1000000000000) (-48004703821 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 2) <| besselDerivativeNearFromState (22356064436463 / 160000000000) 2 (IntervalRat.scale (225 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (51231554395 / 1000000000000) (51231663261 / 1000000000000), orderedInterval (-44132648271 / 1000000000000) (-44132539405 / 1000000000000)))) (orderedInterval (22226753633 / 1000000000000) (22226786366 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate235_chunkChecks2 :
    compactCertificate235.chunkChecks (2 : Fin 5) 0 9 = true :=
  compactCertificate235.chunkChecks_nine_of_three (2 : Fin 5) compactCertificate235_chunkChecks2_0
    compactCertificate235_chunkChecks2_1 compactCertificate235_chunkChecks2_2

theorem compactCertificate235_chunkChecks3_0 :
    compactCertificate235.chunkChecks (3 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 3) <| besselDerivativeNearFromState (225 / 2) 3 (IntervalRat.scale (225 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (13981635826 / 1000000000000) (13981635828 / 1000000000000), orderedInterval (73852732621 / 1000000000000) (73852732623 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 3) <| besselDerivativeNearFromState (13258718531109 / 160000000000) 3 (IntervalRat.scale (225 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (80774910372 / 1000000000000) (80774914962 / 1000000000000), orderedInterval (-34513010138 / 1000000000000) (-34513005548 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 3) <| besselDerivativeNearFromState (4287597155397 / 32000000000) 3 (IntervalRat.scale (225 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (21460904255 / 1000000000000) (21460904743 / 1000000000000), orderedInterval (-65584255822 / 1000000000000) (-65584255333 / 1000000000000)))) (orderedInterval (-22569692753 / 1000000000000) (-22569692673 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 3) <| besselDerivativeNearFromState (3868860999663 / 160000000000) 3 (IntervalRat.scale (225 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-27788419242 / 1000000000000) (-27788419098 / 1000000000000), orderedInterval (160452547646 / 1000000000000) (160452547790 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 3) <| besselDerivativeNearFromState (10392304845411 / 160000000000) 3 (IntervalRat.scale (225 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (23346723629 / 1000000000000) (23346723905 / 1000000000000), orderedInterval (-96390892300 / 1000000000000) (-96390892024 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 3) <| besselDerivativeNearFromState (28217129246487 / 160000000000) 3 (IntervalRat.scale (225 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (56267555039 / 1000000000000) (56267555040 / 1000000000000), orderedInterval (20906695711 / 1000000000000) (20906695712 / 1000000000000)))) (orderedInterval (6334609598 / 1000000000000) (6334609633 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 3) <| besselDerivativeNearFromState (20784609690831 / 160000000000) 3 (IntervalRat.scale (225 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-66621776093 / 1000000000000) (-66621773784 / 1000000000000), orderedInterval (21755513894 / 1000000000000) (21755516203 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 3) <| besselDerivativeNearFromState (35614782967563 / 160000000000) 3 (IntervalRat.scale (225 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-17033361669 / 1000000000000) (-17033361668 / 1000000000000), orderedInterval (-50655872360 / 1000000000000) (-50655872359 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 3) <| besselDerivativeNearFromState (26233687939617 / 160000000000) 3 (IntervalRat.scale (225 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (61208734234 / 1000000000000) (61208734237 / 1000000000000), orderedInterval (11485360524 / 1000000000000) (11485360527 / 1000000000000)))) (orderedInterval (-12915004640 / 1000000000000) (-12915004603 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate235_chunkChecks3_1 :
    compactCertificate235.chunkChecks (3 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 3) <| besselDerivativeNearFromState (40249223594991 / 160000000000) 3 (IntervalRat.scale (225 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (42737696475 / 1000000000000) (42737696476 / 1000000000000), orderedInterval (26451790038 / 1000000000000) (26451790039 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 3) <| besselDerivativeNearFromState (23237900077239 / 160000000000) 3 (IntervalRat.scale (225 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (66076584440 / 1000000000000) (66076584458 / 1000000000000), orderedInterval (3917365262 / 1000000000000) (3917365280 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 3) <| besselDerivativeNearFromState (41236061473251 / 160000000000) 3 (IntervalRat.scale (225 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (38922488488 / 1000000000000) (38922488489 / 1000000000000), orderedInterval (30830581412 / 1000000000000) (30830581413 / 1000000000000)))) (orderedInterval (-775885480 / 1000000000000) (-775885039 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 3) <| besselDerivativeNearFromState (38528077629519 / 160000000000) 3 (IntervalRat.scale (225 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (16040924079 / 1000000000000) (16040924325 / 1000000000000), orderedInterval (-48884692638 / 1000000000000) (-48884692391 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 3) <| besselDerivativeNearFromState (27495454169727 / 160000000000) 3 (IntervalRat.scale (225 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (9476736476 / 1000000000000) (9476736518 / 1000000000000), orderedInterval (-60150682965 / 1000000000000) (-60150682923 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 3) <| besselDerivativeNearFromState (31176914536233 / 160000000000) 3 (IntervalRat.scale (225 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (43381715273 / 1000000000000) (43381715274 / 1000000000000), orderedInterval (37106412031 / 1000000000000) (37106412032 / 1000000000000)))) (orderedInterval (12594497827 / 1000000000000) (12594497947 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 3) <| besselDerivativeNearFromState (25992060983577 / 160000000000) 3 (IntervalRat.scale (225 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-7979104075 / 1000000000000) (-7979104046 / 1000000000000), orderedInterval (62114884514 / 1000000000000) (62114884543 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 3) <| besselDerivativeNearFromState (22964774139117 / 160000000000) 3 (IntervalRat.scale (225 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-13159135913 / 1000000000000) (-13159135818 / 1000000000000), orderedInterval (65332243358 / 1000000000000) (65332243454 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 3) <| besselDerivativeNearFromState (6656086640583 / 32000000000) 3 (IntervalRat.scale (225 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (54867436697 / 1000000000000) (54867436708 / 1000000000000), orderedInterval (6952457125 / 1000000000000) (6952457136 / 1000000000000)))) (orderedInterval (4530693405 / 1000000000000) (4530693456 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate235_chunkChecks3_2 :
    compactCertificate235.chunkChecks (3 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 3) <| besselDerivativeNearFromState (18411085938501 / 160000000000) 3 (IntervalRat.scale (225 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (27956914248 / 1000000000000) (27956915506 / 1000000000000), orderedInterval (-69048533845 / 1000000000000) (-69048532586 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 3) <| besselDerivativeNearFromState (15607281447261 / 160000000000) 3 (IntervalRat.scale (225 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-65251087122 / 1000000000000) (-65251087121 / 1000000000000), orderedInterval (-47295962930 / 1000000000000) (-47295962929 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 3) <| besselDerivativeNearFromState (9766312060383 / 160000000000) 3 (IntervalRat.scale (225 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-86430271910 / 1000000000000) (-86430250874 / 1000000000000), orderedInterval (55107405086 / 1000000000000) (55107426122 / 1000000000000)))) (orderedInterval (-13867703255 / 1000000000000) (-13867702901 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 3) <| besselDerivativeNearFromState (5252355107361 / 160000000000) 3 (IntervalRat.scale (225 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (113164004948 / 1000000000000) (113164037693 / 1000000000000), orderedInterval (-82878834226 / 1000000000000) (-82878801481 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 3) <| besselDerivativeNearFromState (14261165845083 / 160000000000) 3 (IntervalRat.scale (225 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (78455452603 / 1000000000000) (78455456527 / 1000000000000), orderedInterval (-31857848439 / 1000000000000) (-31857844515 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 3) <| besselDerivativeNearFromState (19472402736891 / 160000000000) 3 (IntervalRat.scale (225 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (2547141542 / 1000000000000) (2547141552 / 1000000000000), orderedInterval (-72291208938 / 1000000000000) (-72291208929 / 1000000000000)))) (orderedInterval (-7424068286 / 1000000000000) (-7424068212 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 3) <| besselDerivativeNearFromState (8233687939617 / 160000000000) 3 (IntervalRat.scale (225 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (102126412840 / 1000000000000) (102126417126 / 1000000000000), orderedInterval (-45046930125 / 1000000000000) (-45046925839 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 3) <| besselDerivativeNearFromState (33469484353857 / 160000000000) 3 (IntervalRat.scale (225 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (27297563281 / 1000000000000) (27297566563 / 1000000000000), orderedInterval (-48004707103 / 1000000000000) (-48004703821 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 3) <| besselDerivativeNearFromState (22356064436463 / 160000000000) 3 (IntervalRat.scale (225 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (51231554395 / 1000000000000) (51231663261 / 1000000000000), orderedInterval (-44132648271 / 1000000000000) (-44132539405 / 1000000000000)))) (orderedInterval (-41156169019 / 1000000000000) (-41156127780 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate235_chunkChecks3 :
    compactCertificate235.chunkChecks (3 : Fin 5) 0 9 = true :=
  compactCertificate235.chunkChecks_nine_of_three (3 : Fin 5) compactCertificate235_chunkChecks3_0
    compactCertificate235_chunkChecks3_1 compactCertificate235_chunkChecks3_2

theorem compactCertificate235_chunkChecks4_0 :
    compactCertificate235.chunkChecks (4 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 4) <| besselDerivativeNearFromState (225 / 2) 4 (IntervalRat.scale (225 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (13981635826 / 1000000000000) (13981635828 / 1000000000000), orderedInterval (73852732621 / 1000000000000) (73852732623 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 4) <| besselDerivativeNearFromState (13258718531109 / 160000000000) 4 (IntervalRat.scale (225 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (80774910372 / 1000000000000) (80774914962 / 1000000000000), orderedInterval (-34513010138 / 1000000000000) (-34513005548 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 4) <| besselDerivativeNearFromState (4287597155397 / 32000000000) 4 (IntervalRat.scale (225 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (21460904255 / 1000000000000) (21460904743 / 1000000000000), orderedInterval (-65584255822 / 1000000000000) (-65584255333 / 1000000000000)))) (orderedInterval (8697915403 / 1000000000000) (8697915489 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 4) <| besselDerivativeNearFromState (3868860999663 / 160000000000) 4 (IntervalRat.scale (225 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-27788419242 / 1000000000000) (-27788419098 / 1000000000000), orderedInterval (160452547646 / 1000000000000) (160452547790 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 4) <| besselDerivativeNearFromState (10392304845411 / 160000000000) 4 (IntervalRat.scale (225 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (23346723629 / 1000000000000) (23346723905 / 1000000000000), orderedInterval (-96390892300 / 1000000000000) (-96390892024 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 4) <| besselDerivativeNearFromState (28217129246487 / 160000000000) 4 (IntervalRat.scale (225 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (56267555039 / 1000000000000) (56267555040 / 1000000000000), orderedInterval (20906695711 / 1000000000000) (20906695712 / 1000000000000)))) (orderedInterval (-24172532941 / 1000000000000) (-24172532889 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 4) <| besselDerivativeNearFromState (20784609690831 / 160000000000) 4 (IntervalRat.scale (225 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-66621776093 / 1000000000000) (-66621773784 / 1000000000000), orderedInterval (21755513894 / 1000000000000) (21755516203 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 4) <| besselDerivativeNearFromState (35614782967563 / 160000000000) 4 (IntervalRat.scale (225 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-17033361669 / 1000000000000) (-17033361668 / 1000000000000), orderedInterval (-50655872360 / 1000000000000) (-50655872359 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 4) <| besselDerivativeNearFromState (26233687939617 / 160000000000) 4 (IntervalRat.scale (225 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (61208734234 / 1000000000000) (61208734237 / 1000000000000), orderedInterval (11485360524 / 1000000000000) (11485360527 / 1000000000000)))) (orderedInterval (14955398802 / 1000000000000) (14955398869 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate235_chunkChecks4_1 :
    compactCertificate235.chunkChecks (4 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 4) <| besselDerivativeNearFromState (40249223594991 / 160000000000) 4 (IntervalRat.scale (225 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (42737696475 / 1000000000000) (42737696476 / 1000000000000), orderedInterval (26451790038 / 1000000000000) (26451790039 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 4) <| besselDerivativeNearFromState (23237900077239 / 160000000000) 4 (IntervalRat.scale (225 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (66076584440 / 1000000000000) (66076584458 / 1000000000000), orderedInterval (3917365262 / 1000000000000) (3917365280 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 4) <| besselDerivativeNearFromState (41236061473251 / 160000000000) 4 (IntervalRat.scale (225 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (38922488488 / 1000000000000) (38922488489 / 1000000000000), orderedInterval (30830581412 / 1000000000000) (30830581413 / 1000000000000)))) (orderedInterval (-23836493162 / 1000000000000) (-23836492185 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 4) <| besselDerivativeNearFromState (38528077629519 / 160000000000) 4 (IntervalRat.scale (225 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (16040924079 / 1000000000000) (16040924325 / 1000000000000), orderedInterval (-48884692638 / 1000000000000) (-48884692391 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 4) <| besselDerivativeNearFromState (27495454169727 / 160000000000) 4 (IntervalRat.scale (225 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (9476736476 / 1000000000000) (9476736518 / 1000000000000), orderedInterval (-60150682965 / 1000000000000) (-60150682923 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 4) <| besselDerivativeNearFromState (31176914536233 / 160000000000) 4 (IntervalRat.scale (225 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (43381715273 / 1000000000000) (43381715274 / 1000000000000), orderedInterval (37106412031 / 1000000000000) (37106412032 / 1000000000000)))) (orderedInterval (-3399256895 / 1000000000000) (-3399256672 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 4) <| besselDerivativeNearFromState (25992060983577 / 160000000000) 4 (IntervalRat.scale (225 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-7979104075 / 1000000000000) (-7979104046 / 1000000000000), orderedInterval (62114884514 / 1000000000000) (62114884543 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 4) <| besselDerivativeNearFromState (22964774139117 / 160000000000) 4 (IntervalRat.scale (225 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-13159135913 / 1000000000000) (-13159135818 / 1000000000000), orderedInterval (65332243358 / 1000000000000) (65332243454 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 4) <| besselDerivativeNearFromState (6656086640583 / 32000000000) 4 (IntervalRat.scale (225 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (54867436697 / 1000000000000) (54867436708 / 1000000000000), orderedInterval (6952457125 / 1000000000000) (6952457136 / 1000000000000)))) (orderedInterval (17930341992 / 1000000000000) (17930342069 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate235_chunkChecks4_2 :
    compactCertificate235.chunkChecks (4 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 4) <| besselDerivativeNearFromState (18411085938501 / 160000000000) 4 (IntervalRat.scale (225 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (27956914248 / 1000000000000) (27956915506 / 1000000000000), orderedInterval (-69048533845 / 1000000000000) (-69048532586 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 4) <| besselDerivativeNearFromState (15607281447261 / 160000000000) 4 (IntervalRat.scale (225 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-65251087122 / 1000000000000) (-65251087121 / 1000000000000), orderedInterval (-47295962930 / 1000000000000) (-47295962929 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 4) <| besselDerivativeNearFromState (9766312060383 / 160000000000) 4 (IntervalRat.scale (225 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-86430271910 / 1000000000000) (-86430250874 / 1000000000000), orderedInterval (55107405086 / 1000000000000) (55107426122 / 1000000000000)))) (orderedInterval (-2802290765 / 1000000000000) (-2802290455 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 4) <| besselDerivativeNearFromState (5252355107361 / 160000000000) 4 (IntervalRat.scale (225 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (113164004948 / 1000000000000) (113164037693 / 1000000000000), orderedInterval (-82878834226 / 1000000000000) (-82878801481 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 4) <| besselDerivativeNearFromState (14261165845083 / 160000000000) 4 (IntervalRat.scale (225 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (78455452603 / 1000000000000) (78455456527 / 1000000000000), orderedInterval (-31857848439 / 1000000000000) (-31857844515 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 4) <| besselDerivativeNearFromState (19472402736891 / 160000000000) 4 (IntervalRat.scale (225 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (2547141542 / 1000000000000) (2547141552 / 1000000000000), orderedInterval (-72291208938 / 1000000000000) (-72291208929 / 1000000000000)))) (orderedInterval (-851749881 / 1000000000000) (-851749826 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 4) <| besselDerivativeNearFromState (8233687939617 / 160000000000) 4 (IntervalRat.scale (225 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (102126412840 / 1000000000000) (102126417126 / 1000000000000), orderedInterval (-45046930125 / 1000000000000) (-45046925839 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 4) <| besselDerivativeNearFromState (33469484353857 / 160000000000) 4 (IntervalRat.scale (225 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (27297563281 / 1000000000000) (27297566563 / 1000000000000), orderedInterval (-48004707103 / 1000000000000) (-48004703821 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 4) <| besselDerivativeNearFromState (22356064436463 / 160000000000) 4 (IntervalRat.scale (225 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (51231554395 / 1000000000000) (51231663261 / 1000000000000), orderedInterval (-44132648271 / 1000000000000) (-44132539405 / 1000000000000)))) (orderedInterval (-48674878374 / 1000000000000) (-48674825695 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate235_chunkChecks4 :
    compactCertificate235.chunkChecks (4 : Fin 5) 0 9 = true :=
  compactCertificate235.chunkChecks_nine_of_three (4 : Fin 5) compactCertificate235_chunkChecks4_0
    compactCertificate235_chunkChecks4_1 compactCertificate235_chunkChecks4_2

theorem compactCertificate235_chunks :
    ∀ r : Fin 5, ∀ b, compactCertificate235.chunkCheck r b = true :=
  compactCertificate235.chunkChecks_all (by
    intro r
    fin_cases r
    · exact compactCertificate235_chunkChecks0
    · exact compactCertificate235_chunkChecks1
    · exact compactCertificate235_chunkChecks2
    · exact compactCertificate235_chunkChecks3
    · exact compactCertificate235_chunkChecks4)

theorem compactCertificate235_coefficient0 :
    compactCertificate235.coefficientCheck (0 : Fin 5) = true := by
  norm_num [CompactCertificate.coefficientCheck, intervalFinSumHull,
    compactCertificate235, rationalIntervalSubset, orderedInterval, Fin.sum_univ_succ]

theorem compactCertificate235_coefficient1 :
    compactCertificate235.coefficientCheck (1 : Fin 5) = true := by
  norm_num [CompactCertificate.coefficientCheck, intervalFinSumHull,
    compactCertificate235, rationalIntervalSubset, orderedInterval, Fin.sum_univ_succ]

theorem compactCertificate235_coefficient2 :
    compactCertificate235.coefficientCheck (2 : Fin 5) = true := by
  norm_num [CompactCertificate.coefficientCheck, intervalFinSumHull,
    compactCertificate235, rationalIntervalSubset, orderedInterval, Fin.sum_univ_succ]

theorem compactCertificate235_coefficient3 :
    compactCertificate235.coefficientCheck (3 : Fin 5) = true := by
  norm_num [CompactCertificate.coefficientCheck, intervalFinSumHull,
    compactCertificate235, rationalIntervalSubset, orderedInterval, Fin.sum_univ_succ]

theorem compactCertificate235_coefficient4 :
    compactCertificate235.coefficientCheck (4 : Fin 5) = true := by
  norm_num [CompactCertificate.coefficientCheck, intervalFinSumHull,
    compactCertificate235, rationalIntervalSubset, orderedInterval, Fin.sum_univ_succ]

theorem compactCertificate235_coefficients : ∀ r : Fin 5,
    compactCertificate235.coefficientCheck r = true := by
  intro r
  fin_cases r
  · exact compactCertificate235_coefficient0
  · exact compactCertificate235_coefficient1
  · exact compactCertificate235_coefficient2
  · exact compactCertificate235_coefficient3
  · exact compactCertificate235_coefficient4

theorem compactCertificate235_lower : (1 : ℚ) ≤ compactCertificate235.output.lo := by
  norm_num [CompactCertificate.output, CompactCertificate.interval,
    CompactCertificate.coefficientTargetNat, compactCertificate235, dualConstant,
    intervalTaylorSum, intervalPow, intervalSub, intervalMaxAbs, widenInterval,
    rationalErrorInterval, orderedInterval, IntervalRat.add, IntervalRat.mul, IntervalRat.scale,
    IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4]

theorem compactCertificate235_proves {t : ℝ} (ht : t ∈ compactCertificate235.interval) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t :=
  compactCertificate235.proves compactCertificate235_states compactCertificate235_chunks
    compactCertificate235_coefficients compactCertificate235_lower ht

end Erdos232
