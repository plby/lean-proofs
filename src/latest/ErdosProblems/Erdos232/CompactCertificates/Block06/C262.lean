/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, OpenAI Codex
-/
import ErdosProblems.Erdos232.CompactBase

open LeanCert.Core
namespace Erdos232

def compactCertificate262 : CompactCertificate where
  left := 136
  right := 137
  center := 273 / 2
  grid := fun i =>
    match i.val with
    | 0 => 43
    | 1 => 32
    | 2 => 52
    | 3 => 9
    | 4 => 25
    | 5 => 68
    | 6 => 50
    | 7 => 86
    | 8 => 63
    | 9 => 97
    | 10 => 56
    | 11 => 100
    | 12 => 93
    | 13 => 66
    | 14 => 75
    | 15 => 63
    | 16 => 55
    | 17 => 80
    | 18 => 44
    | 19 => 38
    | 20 => 24
    | 21 => 13
    | 22 => 34
    | 23 => 47
    | 24 => 20
    | 25 => 81
    | _ => 54
  point := fun i =>
    match i.val with
    | 0 => 273 / 2
    | 1 => 402181128776973 / 4000000000000
    | 2 => 130057113713709 / 800000000000
    | 3 => 117355450323111 / 4000000000000
    | 4 => 315233246977467 / 4000000000000
    | 5 => 855919587143439 / 4000000000000
    | 6 => 630466493955207 / 4000000000000
    | 7 => 1080315083349411 / 4000000000000
    | 8 => 795755200835049 / 4000000000000
    | 9 => 1220893115714727 / 4000000000000
    | 10 => 704882969009583 / 4000000000000
    | 11 => 1250827198021947 / 4000000000000
    | 12 => 1168685021428743 / 4000000000000
    | 13 => 834028776481719 / 4000000000000
    | 14 => 945699740932401 / 4000000000000
    | 15 => 788425849835169 / 4000000000000
    | 16 => 696598148886549 / 4000000000000
    | 17 => 201901294764351 / 800000000000
    | 18 => 558469606801197 / 4000000000000
    | 19 => 473420870566917 / 4000000000000
    | 20 => 296244799164951 / 4000000000000
    | 21 => 159321438256617 / 4000000000000
    | 22 => 432588697300851 / 4000000000000
    | 23 => 590662883019027 / 4000000000000
    | 24 => 249755200835049 / 4000000000000
    | 25 => 1015241025400329 / 4000000000000
    | _ => 678133954572711 / 4000000000000
  state := fun i =>
    match i.val with
    | 0 => (orderedInterval (-55374557701 / 1000000000000) (-55374505201 / 1000000000000), orderedInterval (40171949893 / 1000000000000) (40172002394 / 1000000000000))
    | 1 => (orderedInterval (56996206758 / 1000000000000) (56996206759 / 1000000000000), orderedInterval (55242264751 / 1000000000000) (55242264752 / 1000000000000))
    | 2 => (orderedInterval (-425307185 / 1000000000000) (-425307180 / 1000000000000), orderedInterval (62577480471 / 1000000000000) (62577480475 / 1000000000000))
    | 3 => (orderedInterval (-141765172486 / 1000000000000) (-141765171623 / 1000000000000), orderedInterval (42400432437 / 1000000000000) (42400433299 / 1000000000000))
    | 4 => (orderedInterval (-78064584714 / 1000000000000) (-78064584713 / 1000000000000), orderedInterval (-44045921302 / 1000000000000) (-44045921301 / 1000000000000))
    | 5 => (orderedInterval (49479107057 / 1000000000000) (49479107058 / 1000000000000), orderedInterval (22839796695 / 1000000000000) (22839796696 / 1000000000000))
    | 6 => (orderedInterval (61590113633 / 1000000000000) (61590113634 / 1000000000000), orderedInterval (15478791671 / 1000000000000) (15478791672 / 1000000000000))
    | 7 => (orderedInterval (30781943217 / 1000000000000) (30781943218 / 1000000000000), orderedInterval (37488133871 / 1000000000000) (37488133872 / 1000000000000))
    | 8 => (orderedInterval (-55047891550 / 1000000000000) (-55047890167 / 1000000000000), orderedInterval (13169052517 / 1000000000000) (13169053900 / 1000000000000))
    | 9 => (orderedInterval (-43670287340 / 1000000000000) (-43670287338 / 1000000000000), orderedInterval (-13294640425 / 1000000000000) (-13294640423 / 1000000000000))
    | 10 => (orderedInterval (52903261642 / 1000000000000) (52903261643 / 1000000000000), orderedInterval (28378192535 / 1000000000000) (28378192536 / 1000000000000))
    | 11 => (orderedInterval (-27929365745 / 1000000000000) (-27929356658 / 1000000000000), orderedInterval (35481743699 / 1000000000000) (35481752786 / 1000000000000))
    | 12 => (orderedInterval (-33096348301 / 1000000000000) (-33096348300 / 1000000000000), orderedInterval (-32860811197 / 1000000000000) (-32860811196 / 1000000000000))
    | 13 => (orderedInterval (51394148289 / 1000000000000) (51394155268 / 1000000000000), orderedInterval (-20417620142 / 1000000000000) (-20417613163 / 1000000000000))
    | 14 => (orderedInterval (-51881181538 / 1000000000000) (-51881181421 / 1000000000000), orderedInterval (1124613339 / 1000000000000) (1124613457 / 1000000000000))
    | 15 => (orderedInterval (1654171538 / 1000000000000) (1654171543 / 1000000000000), orderedInterval (-56811775539 / 1000000000000) (-56811775534 / 1000000000000))
    | 16 => (orderedInterval (-50711582333 / 1000000000000) (-50711542270 / 1000000000000), orderedInterval (33068575317 / 1000000000000) (33068615380 / 1000000000000))
    | 17 => (orderedInterval (48493352018 / 1000000000000) (48493354680 / 1000000000000), orderedInterval (-13168542132 / 1000000000000) (-13168539470 / 1000000000000))
    | 18 => (orderedInterval (55691958343 / 1000000000000) (55692001326 / 1000000000000), orderedInterval (-38385034754 / 1000000000000) (-38384991772 / 1000000000000))
    | 19 => (orderedInterval (-17501713519 / 1000000000000) (-17501713317 / 1000000000000), orderedInterval (71296286187 / 1000000000000) (71296286390 / 1000000000000))
    | 20 => (orderedInterval (-48721427738 / 1000000000000) (-48721418125 / 1000000000000), orderedInterval (79209648961 / 1000000000000) (79209658574 / 1000000000000))
    | 21 => (orderedInterval (28585034268 / 1000000000000) (28585034550 / 1000000000000), orderedInterval (-123514390805 / 1000000000000) (-123514390524 / 1000000000000))
    | 22 => (orderedInterval (65550064182 / 1000000000000) (65550086801 / 1000000000000), orderedInterval (-40174912199 / 1000000000000) (-40174889580 / 1000000000000))
    | 23 => (orderedInterval (-46891281115 / 1000000000000) (-46891281114 / 1000000000000), orderedInterval (-45802402978 / 1000000000000) (-45802402977 / 1000000000000))
    | 24 => (orderedInterval (38420902566 / 1000000000000) (38420902567 / 1000000000000), orderedInterval (93073112356 / 1000000000000) (93073112357 / 1000000000000))
    | 25 => (orderedInterval (-6301501911 / 1000000000000) (-6301501910 / 1000000000000), orderedInterval (-49672056274 / 1000000000000) (-49672056273 / 1000000000000))
    | _ => (orderedInterval (38156372339 / 1000000000000) (38156372340 / 1000000000000), orderedInterval (47837669509 / 1000000000000) (47837669510 / 1000000000000))
  chunkTarget := fun r b =>
    match r.val with
    | 0 =>
      match b.val with
      | 0 => orderedInterval (-21442399617 / 1000000000000) (-21442378797 / 1000000000000)
      | 1 => orderedInterval (-4829674654 / 1000000000000) (-4829674628 / 1000000000000)
      | 2 => orderedInterval (-2279837221 / 1000000000000) (-2279837179 / 1000000000000)
      | 3 => orderedInterval (7709055204 / 1000000000000) (7709056551 / 1000000000000)
      | 4 => orderedInterval (5720017833 / 1000000000000) (5720018511 / 1000000000000)
      | 5 => orderedInterval (4162776230 / 1000000000000) (4162778605 / 1000000000000)
      | 6 => orderedInterval (-9500273189 / 1000000000000) (-9500265957 / 1000000000000)
      | 7 => orderedInterval (1578743008 / 1000000000000) (1578743544 / 1000000000000)
      | _ => orderedInterval (-6414580388 / 1000000000000) (-6414580350 / 1000000000000)
    | 1 =>
      match b.val with
      | 0 => orderedInterval (20675407204 / 1000000000000) (20675428025 / 1000000000000)
      | 1 => orderedInterval (-3572664405 / 1000000000000) (-3572664384 / 1000000000000)
      | 2 => orderedInterval (-1823967162 / 1000000000000) (-1823967099 / 1000000000000)
      | 3 => orderedInterval (19551810390 / 1000000000000) (19551813463 / 1000000000000)
      | 4 => orderedInterval (-1689326979 / 1000000000000) (-1689325943 / 1000000000000)
      | 5 => orderedInterval (-3985093261 / 1000000000000) (-3985090190 / 1000000000000)
      | 6 => orderedInterval (4177816221 / 1000000000000) (4177823462 / 1000000000000)
      | 7 => orderedInterval (5185011516 / 1000000000000) (5185011939 / 1000000000000)
      | _ => orderedInterval (-3372745916 / 1000000000000) (-3372745862 / 1000000000000)
    | 2 =>
      match b.val with
      | 0 => orderedInterval (21544291482 / 1000000000000) (21544312457 / 1000000000000)
      | 1 => orderedInterval (9549091981 / 1000000000000) (9549092008 / 1000000000000)
      | 2 => orderedInterval (6556166878 / 1000000000000) (6556166974 / 1000000000000)
      | 3 => orderedInterval (-24637480340 / 1000000000000) (-24637473296 / 1000000000000)
      | 4 => orderedInterval (-14852638614 / 1000000000000) (-14852637020 / 1000000000000)
      | 5 => orderedInterval (-8978821916 / 1000000000000) (-8978817900 / 1000000000000)
      | 6 => orderedInterval (9007688509 / 1000000000000) (9007695884 / 1000000000000)
      | 7 => orderedInterval (-3265217707 / 1000000000000) (-3265217366 / 1000000000000)
      | _ => orderedInterval (9246253835 / 1000000000000) (9246253914 / 1000000000000)
    | 3 =>
      match b.val with
      | 0 => orderedInterval (-22488926727 / 1000000000000) (-22488905751 / 1000000000000)
      | 1 => orderedInterval (6498804033 / 1000000000000) (6498804072 / 1000000000000)
      | 2 => orderedInterval (7923090770 / 1000000000000) (7923090918 / 1000000000000)
      | 3 => orderedInterval (-91397252431 / 1000000000000) (-91397236319 / 1000000000000)
      | 4 => orderedInterval (1202308433 / 1000000000000) (1202310875 / 1000000000000)
      | 5 => orderedInterval (8101850074 / 1000000000000) (8101855339 / 1000000000000)
      | 6 => orderedInterval (-4414753467 / 1000000000000) (-4414745972 / 1000000000000)
      | 7 => orderedInterval (-4929801719 / 1000000000000) (-4929801446 / 1000000000000)
      | _ => orderedInterval (-8919555686 / 1000000000000) (-8919555564 / 1000000000000)
    | _ =>
      match b.val with
      | 0 => orderedInterval (-21511750514 / 1000000000000) (-21511729386 / 1000000000000)
      | 1 => orderedInterval (-21649830702 / 1000000000000) (-21649830641 / 1000000000000)
      | 2 => orderedInterval (-20669366974 / 1000000000000) (-20669366741 / 1000000000000)
      | 3 => orderedInterval (96861430746 / 1000000000000) (96861467732 / 1000000000000)
      | 4 => orderedInterval (41345945196 / 1000000000000) (41345948958 / 1000000000000)
      | 5 => orderedInterval (22162346209 / 1000000000000) (22162353225 / 1000000000000)
      | 6 => orderedInterval (-9258878391 / 1000000000000) (-9258870698 / 1000000000000)
      | 7 => orderedInterval (4404115320 / 1000000000000) (4404115542 / 1000000000000)
      | _ => orderedInterval (-10762343235 / 1000000000000) (-10762343039 / 1000000000000)
  coefficientTarget := fun i =>
    match i.val with
    | 0 => orderedInterval (-25296172794 / 1000000000000) (-25296139700 / 1000000000000)
    | 1 => orderedInterval (35146247608 / 1000000000000) (35146283411 / 1000000000000)
    | 2 => orderedInterval (4169334108 / 1000000000000) (4169375655 / 1000000000000)
    | 3 => orderedInterval (-108424236720 / 1000000000000) (-108424183848 / 1000000000000)
    | _ => orderedInterval (80921667655 / 1000000000000) (80921744952 / 1000000000000)

theorem compactCertificate262_stateChecks0 :
    compactCertificate262.stateChecks 0 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 43 12 (273 / 2)) (orderedInterval (-55374557701 / 1000000000000) (-55374505201 / 1000000000000), orderedInterval (40171949893 / 1000000000000) (40172002394 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 32 12 (402181128776973 / 4000000000000)) (orderedInterval (56996206758 / 1000000000000) (56996206759 / 1000000000000), orderedInterval (55242264751 / 1000000000000) (55242264752 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 52 12 (130057113713709 / 800000000000)) (orderedInterval (-425307185 / 1000000000000) (-425307180 / 1000000000000), orderedInterval (62577480471 / 1000000000000) (62577480475 / 1000000000000))) = true
  norm_num [besselStateAtRationalPoint, besselIntervalStepZero,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, besselZeroTransition,
    besselInitial, besselGridStateAt, besselGridStateBlock00, besselGridStateBlock01,
    besselGridStateBlock02, besselGridStateBlock03, besselGridStateBlock04,
    besselGridStateBlock05, besselGridStateBlock06, besselGridStateBlock07,
    besselGridStateBlock08, besselGridStateBlock09, besselGridStateBlock10,
    besselGridStateBlock11, besselGridStateBlock12, besselGridStateBlock13,
    besselGridStateBlock14, besselGridState009, besselGridState013, besselGridState020, besselGridState024, besselGridState025, besselGridState032, besselGridState034, besselGridState038, besselGridState043, besselGridState044, besselGridState047, besselGridState050, besselGridState052, besselGridState054, besselGridState055, besselGridState056, besselGridState063, besselGridState066, besselGridState068, besselGridState075, besselGridState080, besselGridState081, besselGridState086, besselGridState093, besselGridState097, besselGridState100, besselStateSubset, linearInterval, widenInterval,
    rationalErrorInterval, rationalIntervalSubset, orderedInterval, Finset.sum_range_succ,
    IntervalRat.add, IntervalRat.mul, IntervalRat.scale, IntervalRat.singleton]

theorem compactCertificate262_stateChecks1 :
    compactCertificate262.stateChecks 3 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 9 12 (117355450323111 / 4000000000000)) (orderedInterval (-141765172486 / 1000000000000) (-141765171623 / 1000000000000), orderedInterval (42400432437 / 1000000000000) (42400433299 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 25 12 (315233246977467 / 4000000000000)) (orderedInterval (-78064584714 / 1000000000000) (-78064584713 / 1000000000000), orderedInterval (-44045921302 / 1000000000000) (-44045921301 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 68 12 (855919587143439 / 4000000000000)) (orderedInterval (49479107057 / 1000000000000) (49479107058 / 1000000000000), orderedInterval (22839796695 / 1000000000000) (22839796696 / 1000000000000))) = true
  norm_num [besselStateAtRationalPoint, besselIntervalStepZero,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, besselZeroTransition,
    besselInitial, besselGridStateAt, besselGridStateBlock00, besselGridStateBlock01,
    besselGridStateBlock02, besselGridStateBlock03, besselGridStateBlock04,
    besselGridStateBlock05, besselGridStateBlock06, besselGridStateBlock07,
    besselGridStateBlock08, besselGridStateBlock09, besselGridStateBlock10,
    besselGridStateBlock11, besselGridStateBlock12, besselGridStateBlock13,
    besselGridStateBlock14, besselGridState009, besselGridState013, besselGridState020, besselGridState024, besselGridState025, besselGridState032, besselGridState034, besselGridState038, besselGridState043, besselGridState044, besselGridState047, besselGridState050, besselGridState052, besselGridState054, besselGridState055, besselGridState056, besselGridState063, besselGridState066, besselGridState068, besselGridState075, besselGridState080, besselGridState081, besselGridState086, besselGridState093, besselGridState097, besselGridState100, besselStateSubset, linearInterval, widenInterval,
    rationalErrorInterval, rationalIntervalSubset, orderedInterval, Finset.sum_range_succ,
    IntervalRat.add, IntervalRat.mul, IntervalRat.scale, IntervalRat.singleton]

theorem compactCertificate262_stateChecks2 :
    compactCertificate262.stateChecks 6 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 50 12 (630466493955207 / 4000000000000)) (orderedInterval (61590113633 / 1000000000000) (61590113634 / 1000000000000), orderedInterval (15478791671 / 1000000000000) (15478791672 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 86 12 (1080315083349411 / 4000000000000)) (orderedInterval (30781943217 / 1000000000000) (30781943218 / 1000000000000), orderedInterval (37488133871 / 1000000000000) (37488133872 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 63 12 (795755200835049 / 4000000000000)) (orderedInterval (-55047891550 / 1000000000000) (-55047890167 / 1000000000000), orderedInterval (13169052517 / 1000000000000) (13169053900 / 1000000000000))) = true
  norm_num [besselStateAtRationalPoint, besselIntervalStepZero,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, besselZeroTransition,
    besselInitial, besselGridStateAt, besselGridStateBlock00, besselGridStateBlock01,
    besselGridStateBlock02, besselGridStateBlock03, besselGridStateBlock04,
    besselGridStateBlock05, besselGridStateBlock06, besselGridStateBlock07,
    besselGridStateBlock08, besselGridStateBlock09, besselGridStateBlock10,
    besselGridStateBlock11, besselGridStateBlock12, besselGridStateBlock13,
    besselGridStateBlock14, besselGridState009, besselGridState013, besselGridState020, besselGridState024, besselGridState025, besselGridState032, besselGridState034, besselGridState038, besselGridState043, besselGridState044, besselGridState047, besselGridState050, besselGridState052, besselGridState054, besselGridState055, besselGridState056, besselGridState063, besselGridState066, besselGridState068, besselGridState075, besselGridState080, besselGridState081, besselGridState086, besselGridState093, besselGridState097, besselGridState100, besselStateSubset, linearInterval, widenInterval,
    rationalErrorInterval, rationalIntervalSubset, orderedInterval, Finset.sum_range_succ,
    IntervalRat.add, IntervalRat.mul, IntervalRat.scale, IntervalRat.singleton]

theorem compactCertificate262_stateChecks3 :
    compactCertificate262.stateChecks 9 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 97 12 (1220893115714727 / 4000000000000)) (orderedInterval (-43670287340 / 1000000000000) (-43670287338 / 1000000000000), orderedInterval (-13294640425 / 1000000000000) (-13294640423 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 56 12 (704882969009583 / 4000000000000)) (orderedInterval (52903261642 / 1000000000000) (52903261643 / 1000000000000), orderedInterval (28378192535 / 1000000000000) (28378192536 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 100 12 (1250827198021947 / 4000000000000)) (orderedInterval (-27929365745 / 1000000000000) (-27929356658 / 1000000000000), orderedInterval (35481743699 / 1000000000000) (35481752786 / 1000000000000))) = true
  norm_num [besselStateAtRationalPoint, besselIntervalStepZero,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, besselZeroTransition,
    besselInitial, besselGridStateAt, besselGridStateBlock00, besselGridStateBlock01,
    besselGridStateBlock02, besselGridStateBlock03, besselGridStateBlock04,
    besselGridStateBlock05, besselGridStateBlock06, besselGridStateBlock07,
    besselGridStateBlock08, besselGridStateBlock09, besselGridStateBlock10,
    besselGridStateBlock11, besselGridStateBlock12, besselGridStateBlock13,
    besselGridStateBlock14, besselGridState009, besselGridState013, besselGridState020, besselGridState024, besselGridState025, besselGridState032, besselGridState034, besselGridState038, besselGridState043, besselGridState044, besselGridState047, besselGridState050, besselGridState052, besselGridState054, besselGridState055, besselGridState056, besselGridState063, besselGridState066, besselGridState068, besselGridState075, besselGridState080, besselGridState081, besselGridState086, besselGridState093, besselGridState097, besselGridState100, besselStateSubset, linearInterval, widenInterval,
    rationalErrorInterval, rationalIntervalSubset, orderedInterval, Finset.sum_range_succ,
    IntervalRat.add, IntervalRat.mul, IntervalRat.scale, IntervalRat.singleton]

theorem compactCertificate262_stateChecks4 :
    compactCertificate262.stateChecks 12 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 93 12 (1168685021428743 / 4000000000000)) (orderedInterval (-33096348301 / 1000000000000) (-33096348300 / 1000000000000), orderedInterval (-32860811197 / 1000000000000) (-32860811196 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 66 12 (834028776481719 / 4000000000000)) (orderedInterval (51394148289 / 1000000000000) (51394155268 / 1000000000000), orderedInterval (-20417620142 / 1000000000000) (-20417613163 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 75 12 (945699740932401 / 4000000000000)) (orderedInterval (-51881181538 / 1000000000000) (-51881181421 / 1000000000000), orderedInterval (1124613339 / 1000000000000) (1124613457 / 1000000000000))) = true
  norm_num [besselStateAtRationalPoint, besselIntervalStepZero,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, besselZeroTransition,
    besselInitial, besselGridStateAt, besselGridStateBlock00, besselGridStateBlock01,
    besselGridStateBlock02, besselGridStateBlock03, besselGridStateBlock04,
    besselGridStateBlock05, besselGridStateBlock06, besselGridStateBlock07,
    besselGridStateBlock08, besselGridStateBlock09, besselGridStateBlock10,
    besselGridStateBlock11, besselGridStateBlock12, besselGridStateBlock13,
    besselGridStateBlock14, besselGridState009, besselGridState013, besselGridState020, besselGridState024, besselGridState025, besselGridState032, besselGridState034, besselGridState038, besselGridState043, besselGridState044, besselGridState047, besselGridState050, besselGridState052, besselGridState054, besselGridState055, besselGridState056, besselGridState063, besselGridState066, besselGridState068, besselGridState075, besselGridState080, besselGridState081, besselGridState086, besselGridState093, besselGridState097, besselGridState100, besselStateSubset, linearInterval, widenInterval,
    rationalErrorInterval, rationalIntervalSubset, orderedInterval, Finset.sum_range_succ,
    IntervalRat.add, IntervalRat.mul, IntervalRat.scale, IntervalRat.singleton]

theorem compactCertificate262_stateChecks5 :
    compactCertificate262.stateChecks 15 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 63 12 (788425849835169 / 4000000000000)) (orderedInterval (1654171538 / 1000000000000) (1654171543 / 1000000000000), orderedInterval (-56811775539 / 1000000000000) (-56811775534 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 55 12 (696598148886549 / 4000000000000)) (orderedInterval (-50711582333 / 1000000000000) (-50711542270 / 1000000000000), orderedInterval (33068575317 / 1000000000000) (33068615380 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 80 12 (201901294764351 / 800000000000)) (orderedInterval (48493352018 / 1000000000000) (48493354680 / 1000000000000), orderedInterval (-13168542132 / 1000000000000) (-13168539470 / 1000000000000))) = true
  norm_num [besselStateAtRationalPoint, besselIntervalStepZero,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, besselZeroTransition,
    besselInitial, besselGridStateAt, besselGridStateBlock00, besselGridStateBlock01,
    besselGridStateBlock02, besselGridStateBlock03, besselGridStateBlock04,
    besselGridStateBlock05, besselGridStateBlock06, besselGridStateBlock07,
    besselGridStateBlock08, besselGridStateBlock09, besselGridStateBlock10,
    besselGridStateBlock11, besselGridStateBlock12, besselGridStateBlock13,
    besselGridStateBlock14, besselGridState009, besselGridState013, besselGridState020, besselGridState024, besselGridState025, besselGridState032, besselGridState034, besselGridState038, besselGridState043, besselGridState044, besselGridState047, besselGridState050, besselGridState052, besselGridState054, besselGridState055, besselGridState056, besselGridState063, besselGridState066, besselGridState068, besselGridState075, besselGridState080, besselGridState081, besselGridState086, besselGridState093, besselGridState097, besselGridState100, besselStateSubset, linearInterval, widenInterval,
    rationalErrorInterval, rationalIntervalSubset, orderedInterval, Finset.sum_range_succ,
    IntervalRat.add, IntervalRat.mul, IntervalRat.scale, IntervalRat.singleton]

theorem compactCertificate262_stateChecks6 :
    compactCertificate262.stateChecks 18 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 44 12 (558469606801197 / 4000000000000)) (orderedInterval (55691958343 / 1000000000000) (55692001326 / 1000000000000), orderedInterval (-38385034754 / 1000000000000) (-38384991772 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 38 12 (473420870566917 / 4000000000000)) (orderedInterval (-17501713519 / 1000000000000) (-17501713317 / 1000000000000), orderedInterval (71296286187 / 1000000000000) (71296286390 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 24 12 (296244799164951 / 4000000000000)) (orderedInterval (-48721427738 / 1000000000000) (-48721418125 / 1000000000000), orderedInterval (79209648961 / 1000000000000) (79209658574 / 1000000000000))) = true
  norm_num [besselStateAtRationalPoint, besselIntervalStepZero,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, besselZeroTransition,
    besselInitial, besselGridStateAt, besselGridStateBlock00, besselGridStateBlock01,
    besselGridStateBlock02, besselGridStateBlock03, besselGridStateBlock04,
    besselGridStateBlock05, besselGridStateBlock06, besselGridStateBlock07,
    besselGridStateBlock08, besselGridStateBlock09, besselGridStateBlock10,
    besselGridStateBlock11, besselGridStateBlock12, besselGridStateBlock13,
    besselGridStateBlock14, besselGridState009, besselGridState013, besselGridState020, besselGridState024, besselGridState025, besselGridState032, besselGridState034, besselGridState038, besselGridState043, besselGridState044, besselGridState047, besselGridState050, besselGridState052, besselGridState054, besselGridState055, besselGridState056, besselGridState063, besselGridState066, besselGridState068, besselGridState075, besselGridState080, besselGridState081, besselGridState086, besselGridState093, besselGridState097, besselGridState100, besselStateSubset, linearInterval, widenInterval,
    rationalErrorInterval, rationalIntervalSubset, orderedInterval, Finset.sum_range_succ,
    IntervalRat.add, IntervalRat.mul, IntervalRat.scale, IntervalRat.singleton]

theorem compactCertificate262_stateChecks7 :
    compactCertificate262.stateChecks 21 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 13 12 (159321438256617 / 4000000000000)) (orderedInterval (28585034268 / 1000000000000) (28585034550 / 1000000000000), orderedInterval (-123514390805 / 1000000000000) (-123514390524 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 34 12 (432588697300851 / 4000000000000)) (orderedInterval (65550064182 / 1000000000000) (65550086801 / 1000000000000), orderedInterval (-40174912199 / 1000000000000) (-40174889580 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 47 12 (590662883019027 / 4000000000000)) (orderedInterval (-46891281115 / 1000000000000) (-46891281114 / 1000000000000), orderedInterval (-45802402978 / 1000000000000) (-45802402977 / 1000000000000))) = true
  norm_num [besselStateAtRationalPoint, besselIntervalStepZero,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, besselZeroTransition,
    besselInitial, besselGridStateAt, besselGridStateBlock00, besselGridStateBlock01,
    besselGridStateBlock02, besselGridStateBlock03, besselGridStateBlock04,
    besselGridStateBlock05, besselGridStateBlock06, besselGridStateBlock07,
    besselGridStateBlock08, besselGridStateBlock09, besselGridStateBlock10,
    besselGridStateBlock11, besselGridStateBlock12, besselGridStateBlock13,
    besselGridStateBlock14, besselGridState009, besselGridState013, besselGridState020, besselGridState024, besselGridState025, besselGridState032, besselGridState034, besselGridState038, besselGridState043, besselGridState044, besselGridState047, besselGridState050, besselGridState052, besselGridState054, besselGridState055, besselGridState056, besselGridState063, besselGridState066, besselGridState068, besselGridState075, besselGridState080, besselGridState081, besselGridState086, besselGridState093, besselGridState097, besselGridState100, besselStateSubset, linearInterval, widenInterval,
    rationalErrorInterval, rationalIntervalSubset, orderedInterval, Finset.sum_range_succ,
    IntervalRat.add, IntervalRat.mul, IntervalRat.scale, IntervalRat.singleton]

theorem compactCertificate262_stateChecks8 :
    compactCertificate262.stateChecks 24 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 20 12 (249755200835049 / 4000000000000)) (orderedInterval (38420902566 / 1000000000000) (38420902567 / 1000000000000), orderedInterval (93073112356 / 1000000000000) (93073112357 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 81 12 (1015241025400329 / 4000000000000)) (orderedInterval (-6301501911 / 1000000000000) (-6301501910 / 1000000000000), orderedInterval (-49672056274 / 1000000000000) (-49672056273 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 54 12 (678133954572711 / 4000000000000)) (orderedInterval (38156372339 / 1000000000000) (38156372340 / 1000000000000), orderedInterval (47837669509 / 1000000000000) (47837669510 / 1000000000000))) = true
  norm_num [besselStateAtRationalPoint, besselIntervalStepZero,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, besselZeroTransition,
    besselInitial, besselGridStateAt, besselGridStateBlock00, besselGridStateBlock01,
    besselGridStateBlock02, besselGridStateBlock03, besselGridStateBlock04,
    besselGridStateBlock05, besselGridStateBlock06, besselGridStateBlock07,
    besselGridStateBlock08, besselGridStateBlock09, besselGridStateBlock10,
    besselGridStateBlock11, besselGridStateBlock12, besselGridStateBlock13,
    besselGridStateBlock14, besselGridState009, besselGridState013, besselGridState020, besselGridState024, besselGridState025, besselGridState032, besselGridState034, besselGridState038, besselGridState043, besselGridState044, besselGridState047, besselGridState050, besselGridState052, besselGridState054, besselGridState055, besselGridState056, besselGridState063, besselGridState066, besselGridState068, besselGridState075, besselGridState080, besselGridState081, besselGridState086, besselGridState093, besselGridState097, besselGridState100, besselStateSubset, linearInterval, widenInterval,
    rationalErrorInterval, rationalIntervalSubset, orderedInterval, Finset.sum_range_succ,
    IntervalRat.add, IntervalRat.mul, IntervalRat.scale, IntervalRat.singleton]

theorem compactCertificate262_states : ∀ j,
    BesselStateValid (compactCertificate262.point j) (compactCertificate262.state j) :=
  compactCertificate262.statesValid_of_checks3 compactCertificate262_stateChecks0
    compactCertificate262_stateChecks1 compactCertificate262_stateChecks2
    compactCertificate262_stateChecks3 compactCertificate262_stateChecks4
    compactCertificate262_stateChecks5 compactCertificate262_stateChecks6
    compactCertificate262_stateChecks7 compactCertificate262_stateChecks8

theorem compactCertificate262_chunkChecks0_0 :
    compactCertificate262.chunkChecks (0 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 0) <| besselDerivativeNearFromState (273 / 2) 0 (IntervalRat.scale (273 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-55374557701 / 1000000000000) (-55374505201 / 1000000000000), orderedInterval (40171949893 / 1000000000000) (40172002394 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 0) <| besselDerivativeNearFromState (402181128776973 / 4000000000000) 0 (IntervalRat.scale (273 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (56996206758 / 1000000000000) (56996206759 / 1000000000000), orderedInterval (55242264751 / 1000000000000) (55242264752 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 0) <| besselDerivativeNearFromState (130057113713709 / 800000000000) 0 (IntervalRat.scale (273 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-425307185 / 1000000000000) (-425307180 / 1000000000000), orderedInterval (62577480471 / 1000000000000) (62577480475 / 1000000000000)))) (orderedInterval (-21442399617 / 1000000000000) (-21442378797 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 0) <| besselDerivativeNearFromState (117355450323111 / 4000000000000) 0 (IntervalRat.scale (273 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-141765172486 / 1000000000000) (-141765171623 / 1000000000000), orderedInterval (42400432437 / 1000000000000) (42400433299 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 0) <| besselDerivativeNearFromState (315233246977467 / 4000000000000) 0 (IntervalRat.scale (273 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-78064584714 / 1000000000000) (-78064584713 / 1000000000000), orderedInterval (-44045921302 / 1000000000000) (-44045921301 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 0) <| besselDerivativeNearFromState (855919587143439 / 4000000000000) 0 (IntervalRat.scale (273 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (49479107057 / 1000000000000) (49479107058 / 1000000000000), orderedInterval (22839796695 / 1000000000000) (22839796696 / 1000000000000)))) (orderedInterval (-4829674654 / 1000000000000) (-4829674628 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 0) <| besselDerivativeNearFromState (630466493955207 / 4000000000000) 0 (IntervalRat.scale (273 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (61590113633 / 1000000000000) (61590113634 / 1000000000000), orderedInterval (15478791671 / 1000000000000) (15478791672 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 0) <| besselDerivativeNearFromState (1080315083349411 / 4000000000000) 0 (IntervalRat.scale (273 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (30781943217 / 1000000000000) (30781943218 / 1000000000000), orderedInterval (37488133871 / 1000000000000) (37488133872 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 0) <| besselDerivativeNearFromState (795755200835049 / 4000000000000) 0 (IntervalRat.scale (273 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-55047891550 / 1000000000000) (-55047890167 / 1000000000000), orderedInterval (13169052517 / 1000000000000) (13169053900 / 1000000000000)))) (orderedInterval (-2279837221 / 1000000000000) (-2279837179 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate262_chunkChecks0_1 :
    compactCertificate262.chunkChecks (0 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 0) <| besselDerivativeNearFromState (1220893115714727 / 4000000000000) 0 (IntervalRat.scale (273 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-43670287340 / 1000000000000) (-43670287338 / 1000000000000), orderedInterval (-13294640425 / 1000000000000) (-13294640423 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 0) <| besselDerivativeNearFromState (704882969009583 / 4000000000000) 0 (IntervalRat.scale (273 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (52903261642 / 1000000000000) (52903261643 / 1000000000000), orderedInterval (28378192535 / 1000000000000) (28378192536 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 0) <| besselDerivativeNearFromState (1250827198021947 / 4000000000000) 0 (IntervalRat.scale (273 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-27929365745 / 1000000000000) (-27929356658 / 1000000000000), orderedInterval (35481743699 / 1000000000000) (35481752786 / 1000000000000)))) (orderedInterval (7709055204 / 1000000000000) (7709056551 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 0) <| besselDerivativeNearFromState (1168685021428743 / 4000000000000) 0 (IntervalRat.scale (273 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-33096348301 / 1000000000000) (-33096348300 / 1000000000000), orderedInterval (-32860811197 / 1000000000000) (-32860811196 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 0) <| besselDerivativeNearFromState (834028776481719 / 4000000000000) 0 (IntervalRat.scale (273 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (51394148289 / 1000000000000) (51394155268 / 1000000000000), orderedInterval (-20417620142 / 1000000000000) (-20417613163 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 0) <| besselDerivativeNearFromState (945699740932401 / 4000000000000) 0 (IntervalRat.scale (273 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-51881181538 / 1000000000000) (-51881181421 / 1000000000000), orderedInterval (1124613339 / 1000000000000) (1124613457 / 1000000000000)))) (orderedInterval (5720017833 / 1000000000000) (5720018511 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 0) <| besselDerivativeNearFromState (788425849835169 / 4000000000000) 0 (IntervalRat.scale (273 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (1654171538 / 1000000000000) (1654171543 / 1000000000000), orderedInterval (-56811775539 / 1000000000000) (-56811775534 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 0) <| besselDerivativeNearFromState (696598148886549 / 4000000000000) 0 (IntervalRat.scale (273 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-50711582333 / 1000000000000) (-50711542270 / 1000000000000), orderedInterval (33068575317 / 1000000000000) (33068615380 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 0) <| besselDerivativeNearFromState (201901294764351 / 800000000000) 0 (IntervalRat.scale (273 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (48493352018 / 1000000000000) (48493354680 / 1000000000000), orderedInterval (-13168542132 / 1000000000000) (-13168539470 / 1000000000000)))) (orderedInterval (4162776230 / 1000000000000) (4162778605 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate262_chunkChecks0_2 :
    compactCertificate262.chunkChecks (0 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 0) <| besselDerivativeNearFromState (558469606801197 / 4000000000000) 0 (IntervalRat.scale (273 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (55691958343 / 1000000000000) (55692001326 / 1000000000000), orderedInterval (-38385034754 / 1000000000000) (-38384991772 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 0) <| besselDerivativeNearFromState (473420870566917 / 4000000000000) 0 (IntervalRat.scale (273 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-17501713519 / 1000000000000) (-17501713317 / 1000000000000), orderedInterval (71296286187 / 1000000000000) (71296286390 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 0) <| besselDerivativeNearFromState (296244799164951 / 4000000000000) 0 (IntervalRat.scale (273 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-48721427738 / 1000000000000) (-48721418125 / 1000000000000), orderedInterval (79209648961 / 1000000000000) (79209658574 / 1000000000000)))) (orderedInterval (-9500273189 / 1000000000000) (-9500265957 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 0) <| besselDerivativeNearFromState (159321438256617 / 4000000000000) 0 (IntervalRat.scale (273 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (28585034268 / 1000000000000) (28585034550 / 1000000000000), orderedInterval (-123514390805 / 1000000000000) (-123514390524 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 0) <| besselDerivativeNearFromState (432588697300851 / 4000000000000) 0 (IntervalRat.scale (273 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (65550064182 / 1000000000000) (65550086801 / 1000000000000), orderedInterval (-40174912199 / 1000000000000) (-40174889580 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 0) <| besselDerivativeNearFromState (590662883019027 / 4000000000000) 0 (IntervalRat.scale (273 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-46891281115 / 1000000000000) (-46891281114 / 1000000000000), orderedInterval (-45802402978 / 1000000000000) (-45802402977 / 1000000000000)))) (orderedInterval (1578743008 / 1000000000000) (1578743544 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 0) <| besselDerivativeNearFromState (249755200835049 / 4000000000000) 0 (IntervalRat.scale (273 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (38420902566 / 1000000000000) (38420902567 / 1000000000000), orderedInterval (93073112356 / 1000000000000) (93073112357 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 0) <| besselDerivativeNearFromState (1015241025400329 / 4000000000000) 0 (IntervalRat.scale (273 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-6301501911 / 1000000000000) (-6301501910 / 1000000000000), orderedInterval (-49672056274 / 1000000000000) (-49672056273 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 0) <| besselDerivativeNearFromState (678133954572711 / 4000000000000) 0 (IntervalRat.scale (273 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (38156372339 / 1000000000000) (38156372340 / 1000000000000), orderedInterval (47837669509 / 1000000000000) (47837669510 / 1000000000000)))) (orderedInterval (-6414580388 / 1000000000000) (-6414580350 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate262_chunkChecks0 :
    compactCertificate262.chunkChecks (0 : Fin 5) 0 9 = true :=
  compactCertificate262.chunkChecks_nine_of_three (0 : Fin 5) compactCertificate262_chunkChecks0_0
    compactCertificate262_chunkChecks0_1 compactCertificate262_chunkChecks0_2

theorem compactCertificate262_chunkChecks1_0 :
    compactCertificate262.chunkChecks (1 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 1) <| besselDerivativeNearFromState (273 / 2) 1 (IntervalRat.scale (273 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-55374557701 / 1000000000000) (-55374505201 / 1000000000000), orderedInterval (40171949893 / 1000000000000) (40172002394 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 1) <| besselDerivativeNearFromState (402181128776973 / 4000000000000) 1 (IntervalRat.scale (273 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (56996206758 / 1000000000000) (56996206759 / 1000000000000), orderedInterval (55242264751 / 1000000000000) (55242264752 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 1) <| besselDerivativeNearFromState (130057113713709 / 800000000000) 1 (IntervalRat.scale (273 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-425307185 / 1000000000000) (-425307180 / 1000000000000), orderedInterval (62577480471 / 1000000000000) (62577480475 / 1000000000000)))) (orderedInterval (20675407204 / 1000000000000) (20675428025 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 1) <| besselDerivativeNearFromState (117355450323111 / 4000000000000) 1 (IntervalRat.scale (273 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-141765172486 / 1000000000000) (-141765171623 / 1000000000000), orderedInterval (42400432437 / 1000000000000) (42400433299 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 1) <| besselDerivativeNearFromState (315233246977467 / 4000000000000) 1 (IntervalRat.scale (273 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-78064584714 / 1000000000000) (-78064584713 / 1000000000000), orderedInterval (-44045921302 / 1000000000000) (-44045921301 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 1) <| besselDerivativeNearFromState (855919587143439 / 4000000000000) 1 (IntervalRat.scale (273 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (49479107057 / 1000000000000) (49479107058 / 1000000000000), orderedInterval (22839796695 / 1000000000000) (22839796696 / 1000000000000)))) (orderedInterval (-3572664405 / 1000000000000) (-3572664384 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 1) <| besselDerivativeNearFromState (630466493955207 / 4000000000000) 1 (IntervalRat.scale (273 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (61590113633 / 1000000000000) (61590113634 / 1000000000000), orderedInterval (15478791671 / 1000000000000) (15478791672 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 1) <| besselDerivativeNearFromState (1080315083349411 / 4000000000000) 1 (IntervalRat.scale (273 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (30781943217 / 1000000000000) (30781943218 / 1000000000000), orderedInterval (37488133871 / 1000000000000) (37488133872 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 1) <| besselDerivativeNearFromState (795755200835049 / 4000000000000) 1 (IntervalRat.scale (273 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-55047891550 / 1000000000000) (-55047890167 / 1000000000000), orderedInterval (13169052517 / 1000000000000) (13169053900 / 1000000000000)))) (orderedInterval (-1823967162 / 1000000000000) (-1823967099 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate262_chunkChecks1_1 :
    compactCertificate262.chunkChecks (1 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 1) <| besselDerivativeNearFromState (1220893115714727 / 4000000000000) 1 (IntervalRat.scale (273 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-43670287340 / 1000000000000) (-43670287338 / 1000000000000), orderedInterval (-13294640425 / 1000000000000) (-13294640423 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 1) <| besselDerivativeNearFromState (704882969009583 / 4000000000000) 1 (IntervalRat.scale (273 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (52903261642 / 1000000000000) (52903261643 / 1000000000000), orderedInterval (28378192535 / 1000000000000) (28378192536 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 1) <| besselDerivativeNearFromState (1250827198021947 / 4000000000000) 1 (IntervalRat.scale (273 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-27929365745 / 1000000000000) (-27929356658 / 1000000000000), orderedInterval (35481743699 / 1000000000000) (35481752786 / 1000000000000)))) (orderedInterval (19551810390 / 1000000000000) (19551813463 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 1) <| besselDerivativeNearFromState (1168685021428743 / 4000000000000) 1 (IntervalRat.scale (273 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-33096348301 / 1000000000000) (-33096348300 / 1000000000000), orderedInterval (-32860811197 / 1000000000000) (-32860811196 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 1) <| besselDerivativeNearFromState (834028776481719 / 4000000000000) 1 (IntervalRat.scale (273 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (51394148289 / 1000000000000) (51394155268 / 1000000000000), orderedInterval (-20417620142 / 1000000000000) (-20417613163 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 1) <| besselDerivativeNearFromState (945699740932401 / 4000000000000) 1 (IntervalRat.scale (273 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-51881181538 / 1000000000000) (-51881181421 / 1000000000000), orderedInterval (1124613339 / 1000000000000) (1124613457 / 1000000000000)))) (orderedInterval (-1689326979 / 1000000000000) (-1689325943 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 1) <| besselDerivativeNearFromState (788425849835169 / 4000000000000) 1 (IntervalRat.scale (273 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (1654171538 / 1000000000000) (1654171543 / 1000000000000), orderedInterval (-56811775539 / 1000000000000) (-56811775534 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 1) <| besselDerivativeNearFromState (696598148886549 / 4000000000000) 1 (IntervalRat.scale (273 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-50711582333 / 1000000000000) (-50711542270 / 1000000000000), orderedInterval (33068575317 / 1000000000000) (33068615380 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 1) <| besselDerivativeNearFromState (201901294764351 / 800000000000) 1 (IntervalRat.scale (273 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (48493352018 / 1000000000000) (48493354680 / 1000000000000), orderedInterval (-13168542132 / 1000000000000) (-13168539470 / 1000000000000)))) (orderedInterval (-3985093261 / 1000000000000) (-3985090190 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate262_chunkChecks1_2 :
    compactCertificate262.chunkChecks (1 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 1) <| besselDerivativeNearFromState (558469606801197 / 4000000000000) 1 (IntervalRat.scale (273 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (55691958343 / 1000000000000) (55692001326 / 1000000000000), orderedInterval (-38385034754 / 1000000000000) (-38384991772 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 1) <| besselDerivativeNearFromState (473420870566917 / 4000000000000) 1 (IntervalRat.scale (273 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-17501713519 / 1000000000000) (-17501713317 / 1000000000000), orderedInterval (71296286187 / 1000000000000) (71296286390 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 1) <| besselDerivativeNearFromState (296244799164951 / 4000000000000) 1 (IntervalRat.scale (273 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-48721427738 / 1000000000000) (-48721418125 / 1000000000000), orderedInterval (79209648961 / 1000000000000) (79209658574 / 1000000000000)))) (orderedInterval (4177816221 / 1000000000000) (4177823462 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 1) <| besselDerivativeNearFromState (159321438256617 / 4000000000000) 1 (IntervalRat.scale (273 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (28585034268 / 1000000000000) (28585034550 / 1000000000000), orderedInterval (-123514390805 / 1000000000000) (-123514390524 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 1) <| besselDerivativeNearFromState (432588697300851 / 4000000000000) 1 (IntervalRat.scale (273 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (65550064182 / 1000000000000) (65550086801 / 1000000000000), orderedInterval (-40174912199 / 1000000000000) (-40174889580 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 1) <| besselDerivativeNearFromState (590662883019027 / 4000000000000) 1 (IntervalRat.scale (273 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-46891281115 / 1000000000000) (-46891281114 / 1000000000000), orderedInterval (-45802402978 / 1000000000000) (-45802402977 / 1000000000000)))) (orderedInterval (5185011516 / 1000000000000) (5185011939 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 1) <| besselDerivativeNearFromState (249755200835049 / 4000000000000) 1 (IntervalRat.scale (273 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (38420902566 / 1000000000000) (38420902567 / 1000000000000), orderedInterval (93073112356 / 1000000000000) (93073112357 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 1) <| besselDerivativeNearFromState (1015241025400329 / 4000000000000) 1 (IntervalRat.scale (273 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-6301501911 / 1000000000000) (-6301501910 / 1000000000000), orderedInterval (-49672056274 / 1000000000000) (-49672056273 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 1) <| besselDerivativeNearFromState (678133954572711 / 4000000000000) 1 (IntervalRat.scale (273 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (38156372339 / 1000000000000) (38156372340 / 1000000000000), orderedInterval (47837669509 / 1000000000000) (47837669510 / 1000000000000)))) (orderedInterval (-3372745916 / 1000000000000) (-3372745862 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate262_chunkChecks1 :
    compactCertificate262.chunkChecks (1 : Fin 5) 0 9 = true :=
  compactCertificate262.chunkChecks_nine_of_three (1 : Fin 5) compactCertificate262_chunkChecks1_0
    compactCertificate262_chunkChecks1_1 compactCertificate262_chunkChecks1_2

theorem compactCertificate262_chunkChecks2_0 :
    compactCertificate262.chunkChecks (2 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 2) <| besselDerivativeNearFromState (273 / 2) 2 (IntervalRat.scale (273 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-55374557701 / 1000000000000) (-55374505201 / 1000000000000), orderedInterval (40171949893 / 1000000000000) (40172002394 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 2) <| besselDerivativeNearFromState (402181128776973 / 4000000000000) 2 (IntervalRat.scale (273 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (56996206758 / 1000000000000) (56996206759 / 1000000000000), orderedInterval (55242264751 / 1000000000000) (55242264752 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 2) <| besselDerivativeNearFromState (130057113713709 / 800000000000) 2 (IntervalRat.scale (273 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-425307185 / 1000000000000) (-425307180 / 1000000000000), orderedInterval (62577480471 / 1000000000000) (62577480475 / 1000000000000)))) (orderedInterval (21544291482 / 1000000000000) (21544312457 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 2) <| besselDerivativeNearFromState (117355450323111 / 4000000000000) 2 (IntervalRat.scale (273 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-141765172486 / 1000000000000) (-141765171623 / 1000000000000), orderedInterval (42400432437 / 1000000000000) (42400433299 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 2) <| besselDerivativeNearFromState (315233246977467 / 4000000000000) 2 (IntervalRat.scale (273 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-78064584714 / 1000000000000) (-78064584713 / 1000000000000), orderedInterval (-44045921302 / 1000000000000) (-44045921301 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 2) <| besselDerivativeNearFromState (855919587143439 / 4000000000000) 2 (IntervalRat.scale (273 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (49479107057 / 1000000000000) (49479107058 / 1000000000000), orderedInterval (22839796695 / 1000000000000) (22839796696 / 1000000000000)))) (orderedInterval (9549091981 / 1000000000000) (9549092008 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 2) <| besselDerivativeNearFromState (630466493955207 / 4000000000000) 2 (IntervalRat.scale (273 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (61590113633 / 1000000000000) (61590113634 / 1000000000000), orderedInterval (15478791671 / 1000000000000) (15478791672 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 2) <| besselDerivativeNearFromState (1080315083349411 / 4000000000000) 2 (IntervalRat.scale (273 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (30781943217 / 1000000000000) (30781943218 / 1000000000000), orderedInterval (37488133871 / 1000000000000) (37488133872 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 2) <| besselDerivativeNearFromState (795755200835049 / 4000000000000) 2 (IntervalRat.scale (273 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-55047891550 / 1000000000000) (-55047890167 / 1000000000000), orderedInterval (13169052517 / 1000000000000) (13169053900 / 1000000000000)))) (orderedInterval (6556166878 / 1000000000000) (6556166974 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate262_chunkChecks2_1 :
    compactCertificate262.chunkChecks (2 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 2) <| besselDerivativeNearFromState (1220893115714727 / 4000000000000) 2 (IntervalRat.scale (273 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-43670287340 / 1000000000000) (-43670287338 / 1000000000000), orderedInterval (-13294640425 / 1000000000000) (-13294640423 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 2) <| besselDerivativeNearFromState (704882969009583 / 4000000000000) 2 (IntervalRat.scale (273 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (52903261642 / 1000000000000) (52903261643 / 1000000000000), orderedInterval (28378192535 / 1000000000000) (28378192536 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 2) <| besselDerivativeNearFromState (1250827198021947 / 4000000000000) 2 (IntervalRat.scale (273 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-27929365745 / 1000000000000) (-27929356658 / 1000000000000), orderedInterval (35481743699 / 1000000000000) (35481752786 / 1000000000000)))) (orderedInterval (-24637480340 / 1000000000000) (-24637473296 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 2) <| besselDerivativeNearFromState (1168685021428743 / 4000000000000) 2 (IntervalRat.scale (273 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-33096348301 / 1000000000000) (-33096348300 / 1000000000000), orderedInterval (-32860811197 / 1000000000000) (-32860811196 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 2) <| besselDerivativeNearFromState (834028776481719 / 4000000000000) 2 (IntervalRat.scale (273 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (51394148289 / 1000000000000) (51394155268 / 1000000000000), orderedInterval (-20417620142 / 1000000000000) (-20417613163 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 2) <| besselDerivativeNearFromState (945699740932401 / 4000000000000) 2 (IntervalRat.scale (273 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-51881181538 / 1000000000000) (-51881181421 / 1000000000000), orderedInterval (1124613339 / 1000000000000) (1124613457 / 1000000000000)))) (orderedInterval (-14852638614 / 1000000000000) (-14852637020 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 2) <| besselDerivativeNearFromState (788425849835169 / 4000000000000) 2 (IntervalRat.scale (273 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (1654171538 / 1000000000000) (1654171543 / 1000000000000), orderedInterval (-56811775539 / 1000000000000) (-56811775534 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 2) <| besselDerivativeNearFromState (696598148886549 / 4000000000000) 2 (IntervalRat.scale (273 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-50711582333 / 1000000000000) (-50711542270 / 1000000000000), orderedInterval (33068575317 / 1000000000000) (33068615380 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 2) <| besselDerivativeNearFromState (201901294764351 / 800000000000) 2 (IntervalRat.scale (273 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (48493352018 / 1000000000000) (48493354680 / 1000000000000), orderedInterval (-13168542132 / 1000000000000) (-13168539470 / 1000000000000)))) (orderedInterval (-8978821916 / 1000000000000) (-8978817900 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate262_chunkChecks2_2 :
    compactCertificate262.chunkChecks (2 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 2) <| besselDerivativeNearFromState (558469606801197 / 4000000000000) 2 (IntervalRat.scale (273 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (55691958343 / 1000000000000) (55692001326 / 1000000000000), orderedInterval (-38385034754 / 1000000000000) (-38384991772 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 2) <| besselDerivativeNearFromState (473420870566917 / 4000000000000) 2 (IntervalRat.scale (273 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-17501713519 / 1000000000000) (-17501713317 / 1000000000000), orderedInterval (71296286187 / 1000000000000) (71296286390 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 2) <| besselDerivativeNearFromState (296244799164951 / 4000000000000) 2 (IntervalRat.scale (273 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-48721427738 / 1000000000000) (-48721418125 / 1000000000000), orderedInterval (79209648961 / 1000000000000) (79209658574 / 1000000000000)))) (orderedInterval (9007688509 / 1000000000000) (9007695884 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 2) <| besselDerivativeNearFromState (159321438256617 / 4000000000000) 2 (IntervalRat.scale (273 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (28585034268 / 1000000000000) (28585034550 / 1000000000000), orderedInterval (-123514390805 / 1000000000000) (-123514390524 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 2) <| besselDerivativeNearFromState (432588697300851 / 4000000000000) 2 (IntervalRat.scale (273 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (65550064182 / 1000000000000) (65550086801 / 1000000000000), orderedInterval (-40174912199 / 1000000000000) (-40174889580 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 2) <| besselDerivativeNearFromState (590662883019027 / 4000000000000) 2 (IntervalRat.scale (273 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-46891281115 / 1000000000000) (-46891281114 / 1000000000000), orderedInterval (-45802402978 / 1000000000000) (-45802402977 / 1000000000000)))) (orderedInterval (-3265217707 / 1000000000000) (-3265217366 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 2) <| besselDerivativeNearFromState (249755200835049 / 4000000000000) 2 (IntervalRat.scale (273 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (38420902566 / 1000000000000) (38420902567 / 1000000000000), orderedInterval (93073112356 / 1000000000000) (93073112357 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 2) <| besselDerivativeNearFromState (1015241025400329 / 4000000000000) 2 (IntervalRat.scale (273 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-6301501911 / 1000000000000) (-6301501910 / 1000000000000), orderedInterval (-49672056274 / 1000000000000) (-49672056273 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 2) <| besselDerivativeNearFromState (678133954572711 / 4000000000000) 2 (IntervalRat.scale (273 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (38156372339 / 1000000000000) (38156372340 / 1000000000000), orderedInterval (47837669509 / 1000000000000) (47837669510 / 1000000000000)))) (orderedInterval (9246253835 / 1000000000000) (9246253914 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate262_chunkChecks2 :
    compactCertificate262.chunkChecks (2 : Fin 5) 0 9 = true :=
  compactCertificate262.chunkChecks_nine_of_three (2 : Fin 5) compactCertificate262_chunkChecks2_0
    compactCertificate262_chunkChecks2_1 compactCertificate262_chunkChecks2_2

theorem compactCertificate262_chunkChecks3_0 :
    compactCertificate262.chunkChecks (3 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 3) <| besselDerivativeNearFromState (273 / 2) 3 (IntervalRat.scale (273 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-55374557701 / 1000000000000) (-55374505201 / 1000000000000), orderedInterval (40171949893 / 1000000000000) (40172002394 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 3) <| besselDerivativeNearFromState (402181128776973 / 4000000000000) 3 (IntervalRat.scale (273 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (56996206758 / 1000000000000) (56996206759 / 1000000000000), orderedInterval (55242264751 / 1000000000000) (55242264752 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 3) <| besselDerivativeNearFromState (130057113713709 / 800000000000) 3 (IntervalRat.scale (273 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-425307185 / 1000000000000) (-425307180 / 1000000000000), orderedInterval (62577480471 / 1000000000000) (62577480475 / 1000000000000)))) (orderedInterval (-22488926727 / 1000000000000) (-22488905751 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 3) <| besselDerivativeNearFromState (117355450323111 / 4000000000000) 3 (IntervalRat.scale (273 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-141765172486 / 1000000000000) (-141765171623 / 1000000000000), orderedInterval (42400432437 / 1000000000000) (42400433299 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 3) <| besselDerivativeNearFromState (315233246977467 / 4000000000000) 3 (IntervalRat.scale (273 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-78064584714 / 1000000000000) (-78064584713 / 1000000000000), orderedInterval (-44045921302 / 1000000000000) (-44045921301 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 3) <| besselDerivativeNearFromState (855919587143439 / 4000000000000) 3 (IntervalRat.scale (273 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (49479107057 / 1000000000000) (49479107058 / 1000000000000), orderedInterval (22839796695 / 1000000000000) (22839796696 / 1000000000000)))) (orderedInterval (6498804033 / 1000000000000) (6498804072 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 3) <| besselDerivativeNearFromState (630466493955207 / 4000000000000) 3 (IntervalRat.scale (273 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (61590113633 / 1000000000000) (61590113634 / 1000000000000), orderedInterval (15478791671 / 1000000000000) (15478791672 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 3) <| besselDerivativeNearFromState (1080315083349411 / 4000000000000) 3 (IntervalRat.scale (273 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (30781943217 / 1000000000000) (30781943218 / 1000000000000), orderedInterval (37488133871 / 1000000000000) (37488133872 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 3) <| besselDerivativeNearFromState (795755200835049 / 4000000000000) 3 (IntervalRat.scale (273 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-55047891550 / 1000000000000) (-55047890167 / 1000000000000), orderedInterval (13169052517 / 1000000000000) (13169053900 / 1000000000000)))) (orderedInterval (7923090770 / 1000000000000) (7923090918 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate262_chunkChecks3_1 :
    compactCertificate262.chunkChecks (3 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 3) <| besselDerivativeNearFromState (1220893115714727 / 4000000000000) 3 (IntervalRat.scale (273 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-43670287340 / 1000000000000) (-43670287338 / 1000000000000), orderedInterval (-13294640425 / 1000000000000) (-13294640423 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 3) <| besselDerivativeNearFromState (704882969009583 / 4000000000000) 3 (IntervalRat.scale (273 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (52903261642 / 1000000000000) (52903261643 / 1000000000000), orderedInterval (28378192535 / 1000000000000) (28378192536 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 3) <| besselDerivativeNearFromState (1250827198021947 / 4000000000000) 3 (IntervalRat.scale (273 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-27929365745 / 1000000000000) (-27929356658 / 1000000000000), orderedInterval (35481743699 / 1000000000000) (35481752786 / 1000000000000)))) (orderedInterval (-91397252431 / 1000000000000) (-91397236319 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 3) <| besselDerivativeNearFromState (1168685021428743 / 4000000000000) 3 (IntervalRat.scale (273 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-33096348301 / 1000000000000) (-33096348300 / 1000000000000), orderedInterval (-32860811197 / 1000000000000) (-32860811196 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 3) <| besselDerivativeNearFromState (834028776481719 / 4000000000000) 3 (IntervalRat.scale (273 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (51394148289 / 1000000000000) (51394155268 / 1000000000000), orderedInterval (-20417620142 / 1000000000000) (-20417613163 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 3) <| besselDerivativeNearFromState (945699740932401 / 4000000000000) 3 (IntervalRat.scale (273 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-51881181538 / 1000000000000) (-51881181421 / 1000000000000), orderedInterval (1124613339 / 1000000000000) (1124613457 / 1000000000000)))) (orderedInterval (1202308433 / 1000000000000) (1202310875 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 3) <| besselDerivativeNearFromState (788425849835169 / 4000000000000) 3 (IntervalRat.scale (273 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (1654171538 / 1000000000000) (1654171543 / 1000000000000), orderedInterval (-56811775539 / 1000000000000) (-56811775534 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 3) <| besselDerivativeNearFromState (696598148886549 / 4000000000000) 3 (IntervalRat.scale (273 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-50711582333 / 1000000000000) (-50711542270 / 1000000000000), orderedInterval (33068575317 / 1000000000000) (33068615380 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 3) <| besselDerivativeNearFromState (201901294764351 / 800000000000) 3 (IntervalRat.scale (273 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (48493352018 / 1000000000000) (48493354680 / 1000000000000), orderedInterval (-13168542132 / 1000000000000) (-13168539470 / 1000000000000)))) (orderedInterval (8101850074 / 1000000000000) (8101855339 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate262_chunkChecks3_2 :
    compactCertificate262.chunkChecks (3 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 3) <| besselDerivativeNearFromState (558469606801197 / 4000000000000) 3 (IntervalRat.scale (273 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (55691958343 / 1000000000000) (55692001326 / 1000000000000), orderedInterval (-38385034754 / 1000000000000) (-38384991772 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 3) <| besselDerivativeNearFromState (473420870566917 / 4000000000000) 3 (IntervalRat.scale (273 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-17501713519 / 1000000000000) (-17501713317 / 1000000000000), orderedInterval (71296286187 / 1000000000000) (71296286390 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 3) <| besselDerivativeNearFromState (296244799164951 / 4000000000000) 3 (IntervalRat.scale (273 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-48721427738 / 1000000000000) (-48721418125 / 1000000000000), orderedInterval (79209648961 / 1000000000000) (79209658574 / 1000000000000)))) (orderedInterval (-4414753467 / 1000000000000) (-4414745972 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 3) <| besselDerivativeNearFromState (159321438256617 / 4000000000000) 3 (IntervalRat.scale (273 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (28585034268 / 1000000000000) (28585034550 / 1000000000000), orderedInterval (-123514390805 / 1000000000000) (-123514390524 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 3) <| besselDerivativeNearFromState (432588697300851 / 4000000000000) 3 (IntervalRat.scale (273 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (65550064182 / 1000000000000) (65550086801 / 1000000000000), orderedInterval (-40174912199 / 1000000000000) (-40174889580 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 3) <| besselDerivativeNearFromState (590662883019027 / 4000000000000) 3 (IntervalRat.scale (273 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-46891281115 / 1000000000000) (-46891281114 / 1000000000000), orderedInterval (-45802402978 / 1000000000000) (-45802402977 / 1000000000000)))) (orderedInterval (-4929801719 / 1000000000000) (-4929801446 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 3) <| besselDerivativeNearFromState (249755200835049 / 4000000000000) 3 (IntervalRat.scale (273 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (38420902566 / 1000000000000) (38420902567 / 1000000000000), orderedInterval (93073112356 / 1000000000000) (93073112357 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 3) <| besselDerivativeNearFromState (1015241025400329 / 4000000000000) 3 (IntervalRat.scale (273 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-6301501911 / 1000000000000) (-6301501910 / 1000000000000), orderedInterval (-49672056274 / 1000000000000) (-49672056273 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 3) <| besselDerivativeNearFromState (678133954572711 / 4000000000000) 3 (IntervalRat.scale (273 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (38156372339 / 1000000000000) (38156372340 / 1000000000000), orderedInterval (47837669509 / 1000000000000) (47837669510 / 1000000000000)))) (orderedInterval (-8919555686 / 1000000000000) (-8919555564 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate262_chunkChecks3 :
    compactCertificate262.chunkChecks (3 : Fin 5) 0 9 = true :=
  compactCertificate262.chunkChecks_nine_of_three (3 : Fin 5) compactCertificate262_chunkChecks3_0
    compactCertificate262_chunkChecks3_1 compactCertificate262_chunkChecks3_2

theorem compactCertificate262_chunkChecks4_0 :
    compactCertificate262.chunkChecks (4 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 4) <| besselDerivativeNearFromState (273 / 2) 4 (IntervalRat.scale (273 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-55374557701 / 1000000000000) (-55374505201 / 1000000000000), orderedInterval (40171949893 / 1000000000000) (40172002394 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 4) <| besselDerivativeNearFromState (402181128776973 / 4000000000000) 4 (IntervalRat.scale (273 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (56996206758 / 1000000000000) (56996206759 / 1000000000000), orderedInterval (55242264751 / 1000000000000) (55242264752 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 4) <| besselDerivativeNearFromState (130057113713709 / 800000000000) 4 (IntervalRat.scale (273 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-425307185 / 1000000000000) (-425307180 / 1000000000000), orderedInterval (62577480471 / 1000000000000) (62577480475 / 1000000000000)))) (orderedInterval (-21511750514 / 1000000000000) (-21511729386 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 4) <| besselDerivativeNearFromState (117355450323111 / 4000000000000) 4 (IntervalRat.scale (273 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-141765172486 / 1000000000000) (-141765171623 / 1000000000000), orderedInterval (42400432437 / 1000000000000) (42400433299 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 4) <| besselDerivativeNearFromState (315233246977467 / 4000000000000) 4 (IntervalRat.scale (273 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-78064584714 / 1000000000000) (-78064584713 / 1000000000000), orderedInterval (-44045921302 / 1000000000000) (-44045921301 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 4) <| besselDerivativeNearFromState (855919587143439 / 4000000000000) 4 (IntervalRat.scale (273 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (49479107057 / 1000000000000) (49479107058 / 1000000000000), orderedInterval (22839796695 / 1000000000000) (22839796696 / 1000000000000)))) (orderedInterval (-21649830702 / 1000000000000) (-21649830641 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 4) <| besselDerivativeNearFromState (630466493955207 / 4000000000000) 4 (IntervalRat.scale (273 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (61590113633 / 1000000000000) (61590113634 / 1000000000000), orderedInterval (15478791671 / 1000000000000) (15478791672 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 4) <| besselDerivativeNearFromState (1080315083349411 / 4000000000000) 4 (IntervalRat.scale (273 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (30781943217 / 1000000000000) (30781943218 / 1000000000000), orderedInterval (37488133871 / 1000000000000) (37488133872 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 4) <| besselDerivativeNearFromState (795755200835049 / 4000000000000) 4 (IntervalRat.scale (273 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-55047891550 / 1000000000000) (-55047890167 / 1000000000000), orderedInterval (13169052517 / 1000000000000) (13169053900 / 1000000000000)))) (orderedInterval (-20669366974 / 1000000000000) (-20669366741 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate262_chunkChecks4_1 :
    compactCertificate262.chunkChecks (4 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 4) <| besselDerivativeNearFromState (1220893115714727 / 4000000000000) 4 (IntervalRat.scale (273 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-43670287340 / 1000000000000) (-43670287338 / 1000000000000), orderedInterval (-13294640425 / 1000000000000) (-13294640423 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 4) <| besselDerivativeNearFromState (704882969009583 / 4000000000000) 4 (IntervalRat.scale (273 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (52903261642 / 1000000000000) (52903261643 / 1000000000000), orderedInterval (28378192535 / 1000000000000) (28378192536 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 4) <| besselDerivativeNearFromState (1250827198021947 / 4000000000000) 4 (IntervalRat.scale (273 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-27929365745 / 1000000000000) (-27929356658 / 1000000000000), orderedInterval (35481743699 / 1000000000000) (35481752786 / 1000000000000)))) (orderedInterval (96861430746 / 1000000000000) (96861467732 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 4) <| besselDerivativeNearFromState (1168685021428743 / 4000000000000) 4 (IntervalRat.scale (273 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-33096348301 / 1000000000000) (-33096348300 / 1000000000000), orderedInterval (-32860811197 / 1000000000000) (-32860811196 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 4) <| besselDerivativeNearFromState (834028776481719 / 4000000000000) 4 (IntervalRat.scale (273 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (51394148289 / 1000000000000) (51394155268 / 1000000000000), orderedInterval (-20417620142 / 1000000000000) (-20417613163 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 4) <| besselDerivativeNearFromState (945699740932401 / 4000000000000) 4 (IntervalRat.scale (273 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-51881181538 / 1000000000000) (-51881181421 / 1000000000000), orderedInterval (1124613339 / 1000000000000) (1124613457 / 1000000000000)))) (orderedInterval (41345945196 / 1000000000000) (41345948958 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 4) <| besselDerivativeNearFromState (788425849835169 / 4000000000000) 4 (IntervalRat.scale (273 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (1654171538 / 1000000000000) (1654171543 / 1000000000000), orderedInterval (-56811775539 / 1000000000000) (-56811775534 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 4) <| besselDerivativeNearFromState (696598148886549 / 4000000000000) 4 (IntervalRat.scale (273 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-50711582333 / 1000000000000) (-50711542270 / 1000000000000), orderedInterval (33068575317 / 1000000000000) (33068615380 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 4) <| besselDerivativeNearFromState (201901294764351 / 800000000000) 4 (IntervalRat.scale (273 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (48493352018 / 1000000000000) (48493354680 / 1000000000000), orderedInterval (-13168542132 / 1000000000000) (-13168539470 / 1000000000000)))) (orderedInterval (22162346209 / 1000000000000) (22162353225 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate262_chunkChecks4_2 :
    compactCertificate262.chunkChecks (4 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 4) <| besselDerivativeNearFromState (558469606801197 / 4000000000000) 4 (IntervalRat.scale (273 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (55691958343 / 1000000000000) (55692001326 / 1000000000000), orderedInterval (-38385034754 / 1000000000000) (-38384991772 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 4) <| besselDerivativeNearFromState (473420870566917 / 4000000000000) 4 (IntervalRat.scale (273 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-17501713519 / 1000000000000) (-17501713317 / 1000000000000), orderedInterval (71296286187 / 1000000000000) (71296286390 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 4) <| besselDerivativeNearFromState (296244799164951 / 4000000000000) 4 (IntervalRat.scale (273 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-48721427738 / 1000000000000) (-48721418125 / 1000000000000), orderedInterval (79209648961 / 1000000000000) (79209658574 / 1000000000000)))) (orderedInterval (-9258878391 / 1000000000000) (-9258870698 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 4) <| besselDerivativeNearFromState (159321438256617 / 4000000000000) 4 (IntervalRat.scale (273 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (28585034268 / 1000000000000) (28585034550 / 1000000000000), orderedInterval (-123514390805 / 1000000000000) (-123514390524 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 4) <| besselDerivativeNearFromState (432588697300851 / 4000000000000) 4 (IntervalRat.scale (273 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (65550064182 / 1000000000000) (65550086801 / 1000000000000), orderedInterval (-40174912199 / 1000000000000) (-40174889580 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 4) <| besselDerivativeNearFromState (590662883019027 / 4000000000000) 4 (IntervalRat.scale (273 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-46891281115 / 1000000000000) (-46891281114 / 1000000000000), orderedInterval (-45802402978 / 1000000000000) (-45802402977 / 1000000000000)))) (orderedInterval (4404115320 / 1000000000000) (4404115542 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 4) <| besselDerivativeNearFromState (249755200835049 / 4000000000000) 4 (IntervalRat.scale (273 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (38420902566 / 1000000000000) (38420902567 / 1000000000000), orderedInterval (93073112356 / 1000000000000) (93073112357 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 4) <| besselDerivativeNearFromState (1015241025400329 / 4000000000000) 4 (IntervalRat.scale (273 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-6301501911 / 1000000000000) (-6301501910 / 1000000000000), orderedInterval (-49672056274 / 1000000000000) (-49672056273 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 4) <| besselDerivativeNearFromState (678133954572711 / 4000000000000) 4 (IntervalRat.scale (273 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (38156372339 / 1000000000000) (38156372340 / 1000000000000), orderedInterval (47837669509 / 1000000000000) (47837669510 / 1000000000000)))) (orderedInterval (-10762343235 / 1000000000000) (-10762343039 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate262_chunkChecks4 :
    compactCertificate262.chunkChecks (4 : Fin 5) 0 9 = true :=
  compactCertificate262.chunkChecks_nine_of_three (4 : Fin 5) compactCertificate262_chunkChecks4_0
    compactCertificate262_chunkChecks4_1 compactCertificate262_chunkChecks4_2

theorem compactCertificate262_chunks :
    ∀ r : Fin 5, ∀ b, compactCertificate262.chunkCheck r b = true :=
  compactCertificate262.chunkChecks_all (by
    intro r
    fin_cases r
    · exact compactCertificate262_chunkChecks0
    · exact compactCertificate262_chunkChecks1
    · exact compactCertificate262_chunkChecks2
    · exact compactCertificate262_chunkChecks3
    · exact compactCertificate262_chunkChecks4)

theorem compactCertificate262_coefficient0 :
    compactCertificate262.coefficientCheck (0 : Fin 5) = true := by
  norm_num [CompactCertificate.coefficientCheck, intervalFinSumHull,
    compactCertificate262, rationalIntervalSubset, orderedInterval, Fin.sum_univ_succ]

theorem compactCertificate262_coefficient1 :
    compactCertificate262.coefficientCheck (1 : Fin 5) = true := by
  norm_num [CompactCertificate.coefficientCheck, intervalFinSumHull,
    compactCertificate262, rationalIntervalSubset, orderedInterval, Fin.sum_univ_succ]

theorem compactCertificate262_coefficient2 :
    compactCertificate262.coefficientCheck (2 : Fin 5) = true := by
  norm_num [CompactCertificate.coefficientCheck, intervalFinSumHull,
    compactCertificate262, rationalIntervalSubset, orderedInterval, Fin.sum_univ_succ]

theorem compactCertificate262_coefficient3 :
    compactCertificate262.coefficientCheck (3 : Fin 5) = true := by
  norm_num [CompactCertificate.coefficientCheck, intervalFinSumHull,
    compactCertificate262, rationalIntervalSubset, orderedInterval, Fin.sum_univ_succ]

theorem compactCertificate262_coefficient4 :
    compactCertificate262.coefficientCheck (4 : Fin 5) = true := by
  norm_num [CompactCertificate.coefficientCheck, intervalFinSumHull,
    compactCertificate262, rationalIntervalSubset, orderedInterval, Fin.sum_univ_succ]

theorem compactCertificate262_coefficients : ∀ r : Fin 5,
    compactCertificate262.coefficientCheck r = true := by
  intro r
  fin_cases r
  · exact compactCertificate262_coefficient0
  · exact compactCertificate262_coefficient1
  · exact compactCertificate262_coefficient2
  · exact compactCertificate262_coefficient3
  · exact compactCertificate262_coefficient4

theorem compactCertificate262_lower : (1 : ℚ) ≤ compactCertificate262.output.lo := by
  norm_num [CompactCertificate.output, CompactCertificate.interval,
    CompactCertificate.coefficientTargetNat, compactCertificate262, dualConstant,
    intervalTaylorSum, intervalPow, intervalSub, intervalMaxAbs, widenInterval,
    rationalErrorInterval, orderedInterval, IntervalRat.add, IntervalRat.mul, IntervalRat.scale,
    IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4]

theorem compactCertificate262_proves {t : ℝ} (ht : t ∈ compactCertificate262.interval) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t :=
  compactCertificate262.proves compactCertificate262_states compactCertificate262_chunks
    compactCertificate262_coefficients compactCertificate262_lower ht

end Erdos232
