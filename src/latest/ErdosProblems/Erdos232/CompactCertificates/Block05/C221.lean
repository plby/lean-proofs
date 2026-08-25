/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, OpenAI Codex
-/
import ErdosProblems.Erdos232.CompactBase

open LeanCert.Core
namespace Erdos232

def compactCertificate221 : CompactCertificate where
  left := 100
  right := 101
  center := 201 / 2
  grid := fun i =>
    match i.val with
    | 0 => 32
    | 1 => 24
    | 2 => 38
    | 3 => 7
    | 4 => 18
    | 5 => 50
    | 6 => 37
    | 7 => 63
    | 8 => 47
    | 9 => 72
    | 10 => 41
    | 11 => 73
    | 12 => 69
    | 13 => 49
    | 14 => 55
    | 15 => 46
    | 16 => 41
    | 17 => 59
    | 18 => 33
    | 19 => 28
    | 20 => 17
    | 21 => 9
    | 22 => 25
    | 23 => 35
    | 24 => 15
    | 25 => 60
    | _ => 40
  point := fun i =>
    match i.val with
    | 0 => 201 / 2
    | 1 => 296111380528101 / 4000000000000
    | 2 => 95756336470533 / 800000000000
    | 3 => 86404562325807 / 4000000000000
    | 4 => 232094808214179 / 4000000000000
    | 5 => 630182553171543 / 4000000000000
    | 6 => 464189616428559 / 4000000000000
    | 7 => 795396819608907 / 4000000000000
    | 8 => 585885697318113 / 4000000000000
    | 9 => 898899326954799 / 4000000000000
    | 10 => 518979768391671 / 4000000000000
    | 11 => 920938706235939 / 4000000000000
    | 12 => 860460400392591 / 4000000000000
    | 13 => 614065143123903 / 4000000000000
    | 14 => 696284424642537 / 4000000000000
    | 15 => 580489361966553 / 4000000000000
    | 16 => 512879955773613 / 4000000000000
    | 17 => 148652601639687 / 800000000000
    | 18 => 411180919293189 / 4000000000000
    | 19 => 348562618988829 / 4000000000000
    | 20 => 218114302681887 / 4000000000000
    | 21 => 117302597397729 / 4000000000000
    | 22 => 318499370540187 / 4000000000000
    | 23 => 434883661123899 / 4000000000000
    | 24 => 183885697318113 / 4000000000000
    | 25 => 747485150569473 / 4000000000000
    | _ => 499285439081007 / 4000000000000
  state := fun i =>
    match i.val with
    | 0 => (orderedInterval (54436573814 / 1000000000000) (54436573815 / 1000000000000), orderedInterval (57791123996 / 1000000000000) (57791123997 / 1000000000000))
    | 1 => (orderedInterval (-51336441989 / 1000000000000) (-51336428624 / 1000000000000), orderedInterval (77576114358 / 1000000000000) (77576127723 / 1000000000000))
    | 2 => (orderedInterval (64970024996 / 1000000000000) (64970024997 / 1000000000000), orderedInterval (32857643090 / 1000000000000) (32857643091 / 1000000000000))
    | 3 => (orderedInterval (-65197387715 / 1000000000000) (-65197387714 / 1000000000000), orderedInterval (-157320147385 / 1000000000000) (-157320147384 / 1000000000000))
    | 4 => (orderedInterval (80950999283 / 1000000000000) (80951063827 / 1000000000000), orderedInterval (-67169873553 / 1000000000000) (-67169809008 / 1000000000000))
    | 5 => (orderedInterval (60336892517 / 1000000000000) (60336892518 / 1000000000000), orderedInterval (19816072230 / 1000000000000) (19816072231 / 1000000000000))
    | 6 => (orderedInterval (-41379550155 / 1000000000000) (-41379550154 / 1000000000000), orderedInterval (-61251445124 / 1000000000000) (-61251445123 / 1000000000000))
    | 7 => (orderedInterval (-56005635084 / 1000000000000) (-56005634616 / 1000000000000), orderedInterval (8195603517 / 1000000000000) (8195603985 / 1000000000000))
    | 8 => (orderedInterval (25605440676 / 1000000000000) (25605441904 / 1000000000000), orderedInterval (-60838985779 / 1000000000000) (-60838984551 / 1000000000000))
    | 9 => (orderedInterval (-33673791186 / 1000000000000) (-33673774488 / 1000000000000), orderedInterval (41293397834 / 1000000000000) (41293414533 / 1000000000000))
    | 10 => (orderedInterval (-69226311077 / 1000000000000) (-69226310733 / 1000000000000), orderedInterval (10961875384 / 1000000000000) (10961875727 / 1000000000000))
    | 11 => (orderedInterval (-52251827224 / 1000000000000) (-52251826835 / 1000000000000), orderedInterval (6015250088 / 1000000000000) (6015250477 / 1000000000000))
    | 12 => (orderedInterval (41579092180 / 1000000000000) (41579183898 / 1000000000000), orderedInterval (-35176762400 / 1000000000000) (-35176670681 / 1000000000000))
    | 13 => (orderedInterval (-22855647182 / 1000000000000) (-22855647181 / 1000000000000), orderedInterval (-60129845491 / 1000000000000) (-60129845490 / 1000000000000))
    | 14 => (orderedInterval (-53147185073 / 1000000000000) (-53147165633 / 1000000000000), orderedInterval (29007617445 / 1000000000000) (29007636885 / 1000000000000))
    | 15 => (orderedInterval (65195667455 / 1000000000000) (65195667458 / 1000000000000), orderedInterval (11449302166 / 1000000000000) (11449302169 / 1000000000000))
    | 16 => (orderedInterval (-13937589231 / 1000000000000) (-13937589230 / 1000000000000), orderedInterval (-69016897119 / 1000000000000) (-69016897118 / 1000000000000))
    | 17 => (orderedInterval (-55481828098 / 1000000000000) (-55481828097 / 1000000000000), orderedInterval (-18501113937 / 1000000000000) (-18501113936 / 1000000000000))
    | 18 => (orderedInterval (7319558041 / 1000000000000) (7319558068 / 1000000000000), orderedInterval (-78391091506 / 1000000000000) (-78391091479 / 1000000000000))
    | 19 => (orderedInterval (-3415915082 / 1000000000000) (-3415915069 / 1000000000000), orderedInterval (85425154290 / 1000000000000) (85425154303 / 1000000000000))
    | 20 => (orderedInterval (-102084331363 / 1000000000000) (-102084329418 / 1000000000000), orderedInterval (36339083584 / 1000000000000) (36339085529 / 1000000000000))
    | 21 => (orderedInterval (-142313152014 / 1000000000000) (-142313151279 / 1000000000000), orderedInterval (40542290946 / 1000000000000) (40542291681 / 1000000000000))
    | 22 => (orderedInterval (-85472774439 / 1000000000000) (-85472772956 / 1000000000000), orderedInterval (26795319603 / 1000000000000) (26795321086 / 1000000000000))
    | 23 => (orderedInterval (33323937719 / 1000000000000) (33323940455 / 1000000000000), orderedInterval (-69037898649 / 1000000000000) (-69037895913 / 1000000000000))
    | 24 => (orderedInterval (42529491461 / 1000000000000) (42529493009 / 1000000000000), orderedInterval (-110189489129 / 1000000000000) (-110189487580 / 1000000000000))
    | 25 => (orderedInterval (-43444850286 / 1000000000000) (-43444770305 / 1000000000000), orderedInterval (39094087026 / 1000000000000) (39094167007 / 1000000000000))
    | _ => (orderedInterval (-4136197489 / 1000000000000) (-4136197475 / 1000000000000), orderedInterval (71312988611 / 1000000000000) (71312988624 / 1000000000000))
  chunkTarget := fun r b =>
    match r.val with
    | 0 =>
      match b.val with
      | 0 => orderedInterval (24910911281 / 1000000000000) (24910911414 / 1000000000000)
      | 1 => orderedInterval (-626320279 / 1000000000000) (-626317909 / 1000000000000)
      | 2 => orderedInterval (2346270828 / 1000000000000) (2346270879 / 1000000000000)
      | 3 => orderedInterval (-6573581966 / 1000000000000) (-6573578878 / 1000000000000)
      | 4 => orderedInterval (-2642972820 / 1000000000000) (-2642971053 / 1000000000000)
      | 5 => orderedInterval (129906012 / 1000000000000) (129906023 / 1000000000000)
      | 6 => orderedInterval (-4300384457 / 1000000000000) (-4300384362 / 1000000000000)
      | 7 => orderedInterval (2013028847 / 1000000000000) (2013029117 / 1000000000000)
      | _ => orderedInterval (4568923581 / 1000000000000) (4568930132 / 1000000000000)
    | 1 =>
      match b.val with
      | 0 => orderedInterval (25735227145 / 1000000000000) (25735227246 / 1000000000000)
      | 1 => orderedInterval (-3257420070 / 1000000000000) (-3257418695 / 1000000000000)
      | 2 => orderedInterval (-2643100571 / 1000000000000) (-2643100488 / 1000000000000)
      | 3 => orderedInterval (-13399318254 / 1000000000000) (-13399311376 / 1000000000000)
      | 4 => orderedInterval (-7580556108 / 1000000000000) (-7580552373 / 1000000000000)
      | 5 => orderedInterval (4354074224 / 1000000000000) (4354074238 / 1000000000000)
      | 6 => orderedInterval (9269937242 / 1000000000000) (9269937305 / 1000000000000)
      | 7 => orderedInterval (5023712249 / 1000000000000) (5023712518 / 1000000000000)
      | _ => orderedInterval (-22839399872 / 1000000000000) (-22839387719 / 1000000000000)
    | 2 =>
      match b.val with
      | 0 => orderedInterval (-26981254263 / 1000000000000) (-26981254184 / 1000000000000)
      | 1 => orderedInterval (9555223728 / 1000000000000) (9555224547 / 1000000000000)
      | 2 => orderedInterval (-8050827254 / 1000000000000) (-8050827116 / 1000000000000)
      | 3 => orderedInterval (17747734557 / 1000000000000) (17747749971 / 1000000000000)
      | 4 => orderedInterval (7750616362 / 1000000000000) (7750624313 / 1000000000000)
      | 5 => orderedInterval (1944719557 / 1000000000000) (1944719579 / 1000000000000)
      | 6 => orderedInterval (1965170381 / 1000000000000) (1965170428 / 1000000000000)
      | 7 => orderedInterval (1497867373 / 1000000000000) (1497867655 / 1000000000000)
      | _ => orderedInterval (-13250666858 / 1000000000000) (-13250644164 / 1000000000000)
    | 3 =>
      match b.val with
      | 0 => orderedInterval (-26181642854 / 1000000000000) (-26181642792 / 1000000000000)
      | 1 => orderedInterval (5786447094 / 1000000000000) (5786447584 / 1000000000000)
      | 2 => orderedInterval (6589707084 / 1000000000000) (6589707322 / 1000000000000)
      | 3 => orderedInterval (69827535682 / 1000000000000) (69827570114 / 1000000000000)
      | 4 => orderedInterval (14723649858 / 1000000000000) (14723666741 / 1000000000000)
      | 5 => orderedInterval (-5625050204 / 1000000000000) (-5625050171 / 1000000000000)
      | 6 => orderedInterval (-10468415028 / 1000000000000) (-10468414991 / 1000000000000)
      | 7 => orderedInterval (-6391980551 / 1000000000000) (-6391980254 / 1000000000000)
      | _ => orderedInterval (46286585029 / 1000000000000) (46286627201 / 1000000000000)
    | _ =>
      match b.val with
      | 0 => orderedInterval (29625359117 / 1000000000000) (29625359168 / 1000000000000)
      | 1 => orderedInterval (-25687316267 / 1000000000000) (-25687315951 / 1000000000000)
      | 2 => orderedInterval (29134958591 / 1000000000000) (29134959010 / 1000000000000)
      | 3 => orderedInterval (-70640055102 / 1000000000000) (-70639977800 / 1000000000000)
      | 4 => orderedInterval (-25394717669 / 1000000000000) (-25394681601 / 1000000000000)
      | 5 => orderedInterval (-11101941352 / 1000000000000) (-11101941300 / 1000000000000)
      | 6 => orderedInterval (-1251195224 / 1000000000000) (-1251195191 / 1000000000000)
      | 7 => orderedInterval (-2587322169 / 1000000000000) (-2587321851 / 1000000000000)
      | _ => orderedInterval (43209868515 / 1000000000000) (43209947318 / 1000000000000)
  coefficientTarget := fun i =>
    match i.val with
    | 0 => orderedInterval (19825781027 / 1000000000000) (19825795363 / 1000000000000)
    | 1 => orderedInterval (-5336844015 / 1000000000000) (-5336819344 / 1000000000000)
    | 2 => orderedInterval (-7821416417 / 1000000000000) (-7821368971 / 1000000000000)
    | 3 => orderedInterval (94546836110 / 1000000000000) (94546930754 / 1000000000000)
    | _ => orderedInterval (-34692361560 / 1000000000000) (-34692168198 / 1000000000000)

theorem compactCertificate221_stateChecks0 :
    compactCertificate221.stateChecks 0 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 32 12 (201 / 2)) (orderedInterval (54436573814 / 1000000000000) (54436573815 / 1000000000000), orderedInterval (57791123996 / 1000000000000) (57791123997 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 24 12 (296111380528101 / 4000000000000)) (orderedInterval (-51336441989 / 1000000000000) (-51336428624 / 1000000000000), orderedInterval (77576114358 / 1000000000000) (77576127723 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 38 12 (95756336470533 / 800000000000)) (orderedInterval (64970024996 / 1000000000000) (64970024997 / 1000000000000), orderedInterval (32857643090 / 1000000000000) (32857643091 / 1000000000000))) = true
  norm_num [besselStateAtRationalPoint, besselIntervalStepZero,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, besselZeroTransition,
    besselInitial, besselGridStateAt, besselGridStateBlock00, besselGridStateBlock01,
    besselGridStateBlock02, besselGridStateBlock03, besselGridStateBlock04,
    besselGridStateBlock05, besselGridStateBlock06, besselGridStateBlock07,
    besselGridStateBlock08, besselGridStateBlock09, besselGridStateBlock10,
    besselGridStateBlock11, besselGridStateBlock12, besselGridStateBlock13,
    besselGridStateBlock14, besselGridState007, besselGridState009, besselGridState015, besselGridState017, besselGridState018, besselGridState024, besselGridState025, besselGridState028, besselGridState032, besselGridState033, besselGridState035, besselGridState037, besselGridState038, besselGridState040, besselGridState041, besselGridState046, besselGridState047, besselGridState049, besselGridState050, besselGridState055, besselGridState059, besselGridState060, besselGridState063, besselGridState069, besselGridState072, besselGridState073, besselStateSubset, linearInterval, widenInterval,
    rationalErrorInterval, rationalIntervalSubset, orderedInterval, Finset.sum_range_succ,
    IntervalRat.add, IntervalRat.mul, IntervalRat.scale, IntervalRat.singleton]

theorem compactCertificate221_stateChecks1 :
    compactCertificate221.stateChecks 3 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 7 12 (86404562325807 / 4000000000000)) (orderedInterval (-65197387715 / 1000000000000) (-65197387714 / 1000000000000), orderedInterval (-157320147385 / 1000000000000) (-157320147384 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 18 12 (232094808214179 / 4000000000000)) (orderedInterval (80950999283 / 1000000000000) (80951063827 / 1000000000000), orderedInterval (-67169873553 / 1000000000000) (-67169809008 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 50 12 (630182553171543 / 4000000000000)) (orderedInterval (60336892517 / 1000000000000) (60336892518 / 1000000000000), orderedInterval (19816072230 / 1000000000000) (19816072231 / 1000000000000))) = true
  norm_num [besselStateAtRationalPoint, besselIntervalStepZero,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, besselZeroTransition,
    besselInitial, besselGridStateAt, besselGridStateBlock00, besselGridStateBlock01,
    besselGridStateBlock02, besselGridStateBlock03, besselGridStateBlock04,
    besselGridStateBlock05, besselGridStateBlock06, besselGridStateBlock07,
    besselGridStateBlock08, besselGridStateBlock09, besselGridStateBlock10,
    besselGridStateBlock11, besselGridStateBlock12, besselGridStateBlock13,
    besselGridStateBlock14, besselGridState007, besselGridState009, besselGridState015, besselGridState017, besselGridState018, besselGridState024, besselGridState025, besselGridState028, besselGridState032, besselGridState033, besselGridState035, besselGridState037, besselGridState038, besselGridState040, besselGridState041, besselGridState046, besselGridState047, besselGridState049, besselGridState050, besselGridState055, besselGridState059, besselGridState060, besselGridState063, besselGridState069, besselGridState072, besselGridState073, besselStateSubset, linearInterval, widenInterval,
    rationalErrorInterval, rationalIntervalSubset, orderedInterval, Finset.sum_range_succ,
    IntervalRat.add, IntervalRat.mul, IntervalRat.scale, IntervalRat.singleton]

theorem compactCertificate221_stateChecks2 :
    compactCertificate221.stateChecks 6 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 37 12 (464189616428559 / 4000000000000)) (orderedInterval (-41379550155 / 1000000000000) (-41379550154 / 1000000000000), orderedInterval (-61251445124 / 1000000000000) (-61251445123 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 63 12 (795396819608907 / 4000000000000)) (orderedInterval (-56005635084 / 1000000000000) (-56005634616 / 1000000000000), orderedInterval (8195603517 / 1000000000000) (8195603985 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 47 12 (585885697318113 / 4000000000000)) (orderedInterval (25605440676 / 1000000000000) (25605441904 / 1000000000000), orderedInterval (-60838985779 / 1000000000000) (-60838984551 / 1000000000000))) = true
  norm_num [besselStateAtRationalPoint, besselIntervalStepZero,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, besselZeroTransition,
    besselInitial, besselGridStateAt, besselGridStateBlock00, besselGridStateBlock01,
    besselGridStateBlock02, besselGridStateBlock03, besselGridStateBlock04,
    besselGridStateBlock05, besselGridStateBlock06, besselGridStateBlock07,
    besselGridStateBlock08, besselGridStateBlock09, besselGridStateBlock10,
    besselGridStateBlock11, besselGridStateBlock12, besselGridStateBlock13,
    besselGridStateBlock14, besselGridState007, besselGridState009, besselGridState015, besselGridState017, besselGridState018, besselGridState024, besselGridState025, besselGridState028, besselGridState032, besselGridState033, besselGridState035, besselGridState037, besselGridState038, besselGridState040, besselGridState041, besselGridState046, besselGridState047, besselGridState049, besselGridState050, besselGridState055, besselGridState059, besselGridState060, besselGridState063, besselGridState069, besselGridState072, besselGridState073, besselStateSubset, linearInterval, widenInterval,
    rationalErrorInterval, rationalIntervalSubset, orderedInterval, Finset.sum_range_succ,
    IntervalRat.add, IntervalRat.mul, IntervalRat.scale, IntervalRat.singleton]

theorem compactCertificate221_stateChecks3 :
    compactCertificate221.stateChecks 9 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 72 12 (898899326954799 / 4000000000000)) (orderedInterval (-33673791186 / 1000000000000) (-33673774488 / 1000000000000), orderedInterval (41293397834 / 1000000000000) (41293414533 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 41 12 (518979768391671 / 4000000000000)) (orderedInterval (-69226311077 / 1000000000000) (-69226310733 / 1000000000000), orderedInterval (10961875384 / 1000000000000) (10961875727 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 73 12 (920938706235939 / 4000000000000)) (orderedInterval (-52251827224 / 1000000000000) (-52251826835 / 1000000000000), orderedInterval (6015250088 / 1000000000000) (6015250477 / 1000000000000))) = true
  norm_num [besselStateAtRationalPoint, besselIntervalStepZero,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, besselZeroTransition,
    besselInitial, besselGridStateAt, besselGridStateBlock00, besselGridStateBlock01,
    besselGridStateBlock02, besselGridStateBlock03, besselGridStateBlock04,
    besselGridStateBlock05, besselGridStateBlock06, besselGridStateBlock07,
    besselGridStateBlock08, besselGridStateBlock09, besselGridStateBlock10,
    besselGridStateBlock11, besselGridStateBlock12, besselGridStateBlock13,
    besselGridStateBlock14, besselGridState007, besselGridState009, besselGridState015, besselGridState017, besselGridState018, besselGridState024, besselGridState025, besselGridState028, besselGridState032, besselGridState033, besselGridState035, besselGridState037, besselGridState038, besselGridState040, besselGridState041, besselGridState046, besselGridState047, besselGridState049, besselGridState050, besselGridState055, besselGridState059, besselGridState060, besselGridState063, besselGridState069, besselGridState072, besselGridState073, besselStateSubset, linearInterval, widenInterval,
    rationalErrorInterval, rationalIntervalSubset, orderedInterval, Finset.sum_range_succ,
    IntervalRat.add, IntervalRat.mul, IntervalRat.scale, IntervalRat.singleton]

theorem compactCertificate221_stateChecks4 :
    compactCertificate221.stateChecks 12 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 69 12 (860460400392591 / 4000000000000)) (orderedInterval (41579092180 / 1000000000000) (41579183898 / 1000000000000), orderedInterval (-35176762400 / 1000000000000) (-35176670681 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 49 12 (614065143123903 / 4000000000000)) (orderedInterval (-22855647182 / 1000000000000) (-22855647181 / 1000000000000), orderedInterval (-60129845491 / 1000000000000) (-60129845490 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 55 12 (696284424642537 / 4000000000000)) (orderedInterval (-53147185073 / 1000000000000) (-53147165633 / 1000000000000), orderedInterval (29007617445 / 1000000000000) (29007636885 / 1000000000000))) = true
  norm_num [besselStateAtRationalPoint, besselIntervalStepZero,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, besselZeroTransition,
    besselInitial, besselGridStateAt, besselGridStateBlock00, besselGridStateBlock01,
    besselGridStateBlock02, besselGridStateBlock03, besselGridStateBlock04,
    besselGridStateBlock05, besselGridStateBlock06, besselGridStateBlock07,
    besselGridStateBlock08, besselGridStateBlock09, besselGridStateBlock10,
    besselGridStateBlock11, besselGridStateBlock12, besselGridStateBlock13,
    besselGridStateBlock14, besselGridState007, besselGridState009, besselGridState015, besselGridState017, besselGridState018, besselGridState024, besselGridState025, besselGridState028, besselGridState032, besselGridState033, besselGridState035, besselGridState037, besselGridState038, besselGridState040, besselGridState041, besselGridState046, besselGridState047, besselGridState049, besselGridState050, besselGridState055, besselGridState059, besselGridState060, besselGridState063, besselGridState069, besselGridState072, besselGridState073, besselStateSubset, linearInterval, widenInterval,
    rationalErrorInterval, rationalIntervalSubset, orderedInterval, Finset.sum_range_succ,
    IntervalRat.add, IntervalRat.mul, IntervalRat.scale, IntervalRat.singleton]

theorem compactCertificate221_stateChecks5 :
    compactCertificate221.stateChecks 15 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 46 12 (580489361966553 / 4000000000000)) (orderedInterval (65195667455 / 1000000000000) (65195667458 / 1000000000000), orderedInterval (11449302166 / 1000000000000) (11449302169 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 41 12 (512879955773613 / 4000000000000)) (orderedInterval (-13937589231 / 1000000000000) (-13937589230 / 1000000000000), orderedInterval (-69016897119 / 1000000000000) (-69016897118 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 59 12 (148652601639687 / 800000000000)) (orderedInterval (-55481828098 / 1000000000000) (-55481828097 / 1000000000000), orderedInterval (-18501113937 / 1000000000000) (-18501113936 / 1000000000000))) = true
  norm_num [besselStateAtRationalPoint, besselIntervalStepZero,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, besselZeroTransition,
    besselInitial, besselGridStateAt, besselGridStateBlock00, besselGridStateBlock01,
    besselGridStateBlock02, besselGridStateBlock03, besselGridStateBlock04,
    besselGridStateBlock05, besselGridStateBlock06, besselGridStateBlock07,
    besselGridStateBlock08, besselGridStateBlock09, besselGridStateBlock10,
    besselGridStateBlock11, besselGridStateBlock12, besselGridStateBlock13,
    besselGridStateBlock14, besselGridState007, besselGridState009, besselGridState015, besselGridState017, besselGridState018, besselGridState024, besselGridState025, besselGridState028, besselGridState032, besselGridState033, besselGridState035, besselGridState037, besselGridState038, besselGridState040, besselGridState041, besselGridState046, besselGridState047, besselGridState049, besselGridState050, besselGridState055, besselGridState059, besselGridState060, besselGridState063, besselGridState069, besselGridState072, besselGridState073, besselStateSubset, linearInterval, widenInterval,
    rationalErrorInterval, rationalIntervalSubset, orderedInterval, Finset.sum_range_succ,
    IntervalRat.add, IntervalRat.mul, IntervalRat.scale, IntervalRat.singleton]

theorem compactCertificate221_stateChecks6 :
    compactCertificate221.stateChecks 18 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 33 12 (411180919293189 / 4000000000000)) (orderedInterval (7319558041 / 1000000000000) (7319558068 / 1000000000000), orderedInterval (-78391091506 / 1000000000000) (-78391091479 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 28 12 (348562618988829 / 4000000000000)) (orderedInterval (-3415915082 / 1000000000000) (-3415915069 / 1000000000000), orderedInterval (85425154290 / 1000000000000) (85425154303 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 17 12 (218114302681887 / 4000000000000)) (orderedInterval (-102084331363 / 1000000000000) (-102084329418 / 1000000000000), orderedInterval (36339083584 / 1000000000000) (36339085529 / 1000000000000))) = true
  norm_num [besselStateAtRationalPoint, besselIntervalStepZero,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, besselZeroTransition,
    besselInitial, besselGridStateAt, besselGridStateBlock00, besselGridStateBlock01,
    besselGridStateBlock02, besselGridStateBlock03, besselGridStateBlock04,
    besselGridStateBlock05, besselGridStateBlock06, besselGridStateBlock07,
    besselGridStateBlock08, besselGridStateBlock09, besselGridStateBlock10,
    besselGridStateBlock11, besselGridStateBlock12, besselGridStateBlock13,
    besselGridStateBlock14, besselGridState007, besselGridState009, besselGridState015, besselGridState017, besselGridState018, besselGridState024, besselGridState025, besselGridState028, besselGridState032, besselGridState033, besselGridState035, besselGridState037, besselGridState038, besselGridState040, besselGridState041, besselGridState046, besselGridState047, besselGridState049, besselGridState050, besselGridState055, besselGridState059, besselGridState060, besselGridState063, besselGridState069, besselGridState072, besselGridState073, besselStateSubset, linearInterval, widenInterval,
    rationalErrorInterval, rationalIntervalSubset, orderedInterval, Finset.sum_range_succ,
    IntervalRat.add, IntervalRat.mul, IntervalRat.scale, IntervalRat.singleton]

theorem compactCertificate221_stateChecks7 :
    compactCertificate221.stateChecks 21 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 9 12 (117302597397729 / 4000000000000)) (orderedInterval (-142313152014 / 1000000000000) (-142313151279 / 1000000000000), orderedInterval (40542290946 / 1000000000000) (40542291681 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 25 12 (318499370540187 / 4000000000000)) (orderedInterval (-85472774439 / 1000000000000) (-85472772956 / 1000000000000), orderedInterval (26795319603 / 1000000000000) (26795321086 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 35 12 (434883661123899 / 4000000000000)) (orderedInterval (33323937719 / 1000000000000) (33323940455 / 1000000000000), orderedInterval (-69037898649 / 1000000000000) (-69037895913 / 1000000000000))) = true
  norm_num [besselStateAtRationalPoint, besselIntervalStepZero,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, besselZeroTransition,
    besselInitial, besselGridStateAt, besselGridStateBlock00, besselGridStateBlock01,
    besselGridStateBlock02, besselGridStateBlock03, besselGridStateBlock04,
    besselGridStateBlock05, besselGridStateBlock06, besselGridStateBlock07,
    besselGridStateBlock08, besselGridStateBlock09, besselGridStateBlock10,
    besselGridStateBlock11, besselGridStateBlock12, besselGridStateBlock13,
    besselGridStateBlock14, besselGridState007, besselGridState009, besselGridState015, besselGridState017, besselGridState018, besselGridState024, besselGridState025, besselGridState028, besselGridState032, besselGridState033, besselGridState035, besselGridState037, besselGridState038, besselGridState040, besselGridState041, besselGridState046, besselGridState047, besselGridState049, besselGridState050, besselGridState055, besselGridState059, besselGridState060, besselGridState063, besselGridState069, besselGridState072, besselGridState073, besselStateSubset, linearInterval, widenInterval,
    rationalErrorInterval, rationalIntervalSubset, orderedInterval, Finset.sum_range_succ,
    IntervalRat.add, IntervalRat.mul, IntervalRat.scale, IntervalRat.singleton]

theorem compactCertificate221_stateChecks8 :
    compactCertificate221.stateChecks 24 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 15 12 (183885697318113 / 4000000000000)) (orderedInterval (42529491461 / 1000000000000) (42529493009 / 1000000000000), orderedInterval (-110189489129 / 1000000000000) (-110189487580 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 60 12 (747485150569473 / 4000000000000)) (orderedInterval (-43444850286 / 1000000000000) (-43444770305 / 1000000000000), orderedInterval (39094087026 / 1000000000000) (39094167007 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 40 12 (499285439081007 / 4000000000000)) (orderedInterval (-4136197489 / 1000000000000) (-4136197475 / 1000000000000), orderedInterval (71312988611 / 1000000000000) (71312988624 / 1000000000000))) = true
  norm_num [besselStateAtRationalPoint, besselIntervalStepZero,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, besselZeroTransition,
    besselInitial, besselGridStateAt, besselGridStateBlock00, besselGridStateBlock01,
    besselGridStateBlock02, besselGridStateBlock03, besselGridStateBlock04,
    besselGridStateBlock05, besselGridStateBlock06, besselGridStateBlock07,
    besselGridStateBlock08, besselGridStateBlock09, besselGridStateBlock10,
    besselGridStateBlock11, besselGridStateBlock12, besselGridStateBlock13,
    besselGridStateBlock14, besselGridState007, besselGridState009, besselGridState015, besselGridState017, besselGridState018, besselGridState024, besselGridState025, besselGridState028, besselGridState032, besselGridState033, besselGridState035, besselGridState037, besselGridState038, besselGridState040, besselGridState041, besselGridState046, besselGridState047, besselGridState049, besselGridState050, besselGridState055, besselGridState059, besselGridState060, besselGridState063, besselGridState069, besselGridState072, besselGridState073, besselStateSubset, linearInterval, widenInterval,
    rationalErrorInterval, rationalIntervalSubset, orderedInterval, Finset.sum_range_succ,
    IntervalRat.add, IntervalRat.mul, IntervalRat.scale, IntervalRat.singleton]

theorem compactCertificate221_states : ∀ j,
    BesselStateValid (compactCertificate221.point j) (compactCertificate221.state j) :=
  compactCertificate221.statesValid_of_checks3 compactCertificate221_stateChecks0
    compactCertificate221_stateChecks1 compactCertificate221_stateChecks2
    compactCertificate221_stateChecks3 compactCertificate221_stateChecks4
    compactCertificate221_stateChecks5 compactCertificate221_stateChecks6
    compactCertificate221_stateChecks7 compactCertificate221_stateChecks8

theorem compactCertificate221_chunkChecks0_0 :
    compactCertificate221.chunkChecks (0 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 0) <| besselDerivativeNearFromState (201 / 2) 0 (IntervalRat.scale (201 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (54436573814 / 1000000000000) (54436573815 / 1000000000000), orderedInterval (57791123996 / 1000000000000) (57791123997 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 0) <| besselDerivativeNearFromState (296111380528101 / 4000000000000) 0 (IntervalRat.scale (201 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-51336441989 / 1000000000000) (-51336428624 / 1000000000000), orderedInterval (77576114358 / 1000000000000) (77576127723 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 0) <| besselDerivativeNearFromState (95756336470533 / 800000000000) 0 (IntervalRat.scale (201 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (64970024996 / 1000000000000) (64970024997 / 1000000000000), orderedInterval (32857643090 / 1000000000000) (32857643091 / 1000000000000)))) (orderedInterval (24910911281 / 1000000000000) (24910911414 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 0) <| besselDerivativeNearFromState (86404562325807 / 4000000000000) 0 (IntervalRat.scale (201 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-65197387715 / 1000000000000) (-65197387714 / 1000000000000), orderedInterval (-157320147385 / 1000000000000) (-157320147384 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 0) <| besselDerivativeNearFromState (232094808214179 / 4000000000000) 0 (IntervalRat.scale (201 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (80950999283 / 1000000000000) (80951063827 / 1000000000000), orderedInterval (-67169873553 / 1000000000000) (-67169809008 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 0) <| besselDerivativeNearFromState (630182553171543 / 4000000000000) 0 (IntervalRat.scale (201 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (60336892517 / 1000000000000) (60336892518 / 1000000000000), orderedInterval (19816072230 / 1000000000000) (19816072231 / 1000000000000)))) (orderedInterval (-626320279 / 1000000000000) (-626317909 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 0) <| besselDerivativeNearFromState (464189616428559 / 4000000000000) 0 (IntervalRat.scale (201 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-41379550155 / 1000000000000) (-41379550154 / 1000000000000), orderedInterval (-61251445124 / 1000000000000) (-61251445123 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 0) <| besselDerivativeNearFromState (795396819608907 / 4000000000000) 0 (IntervalRat.scale (201 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-56005635084 / 1000000000000) (-56005634616 / 1000000000000), orderedInterval (8195603517 / 1000000000000) (8195603985 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 0) <| besselDerivativeNearFromState (585885697318113 / 4000000000000) 0 (IntervalRat.scale (201 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (25605440676 / 1000000000000) (25605441904 / 1000000000000), orderedInterval (-60838985779 / 1000000000000) (-60838984551 / 1000000000000)))) (orderedInterval (2346270828 / 1000000000000) (2346270879 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate221_chunkChecks0_1 :
    compactCertificate221.chunkChecks (0 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 0) <| besselDerivativeNearFromState (898899326954799 / 4000000000000) 0 (IntervalRat.scale (201 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-33673791186 / 1000000000000) (-33673774488 / 1000000000000), orderedInterval (41293397834 / 1000000000000) (41293414533 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 0) <| besselDerivativeNearFromState (518979768391671 / 4000000000000) 0 (IntervalRat.scale (201 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-69226311077 / 1000000000000) (-69226310733 / 1000000000000), orderedInterval (10961875384 / 1000000000000) (10961875727 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 0) <| besselDerivativeNearFromState (920938706235939 / 4000000000000) 0 (IntervalRat.scale (201 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-52251827224 / 1000000000000) (-52251826835 / 1000000000000), orderedInterval (6015250088 / 1000000000000) (6015250477 / 1000000000000)))) (orderedInterval (-6573581966 / 1000000000000) (-6573578878 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 0) <| besselDerivativeNearFromState (860460400392591 / 4000000000000) 0 (IntervalRat.scale (201 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (41579092180 / 1000000000000) (41579183898 / 1000000000000), orderedInterval (-35176762400 / 1000000000000) (-35176670681 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 0) <| besselDerivativeNearFromState (614065143123903 / 4000000000000) 0 (IntervalRat.scale (201 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-22855647182 / 1000000000000) (-22855647181 / 1000000000000), orderedInterval (-60129845491 / 1000000000000) (-60129845490 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 0) <| besselDerivativeNearFromState (696284424642537 / 4000000000000) 0 (IntervalRat.scale (201 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-53147185073 / 1000000000000) (-53147165633 / 1000000000000), orderedInterval (29007617445 / 1000000000000) (29007636885 / 1000000000000)))) (orderedInterval (-2642972820 / 1000000000000) (-2642971053 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 0) <| besselDerivativeNearFromState (580489361966553 / 4000000000000) 0 (IntervalRat.scale (201 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (65195667455 / 1000000000000) (65195667458 / 1000000000000), orderedInterval (11449302166 / 1000000000000) (11449302169 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 0) <| besselDerivativeNearFromState (512879955773613 / 4000000000000) 0 (IntervalRat.scale (201 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-13937589231 / 1000000000000) (-13937589230 / 1000000000000), orderedInterval (-69016897119 / 1000000000000) (-69016897118 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 0) <| besselDerivativeNearFromState (148652601639687 / 800000000000) 0 (IntervalRat.scale (201 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-55481828098 / 1000000000000) (-55481828097 / 1000000000000), orderedInterval (-18501113937 / 1000000000000) (-18501113936 / 1000000000000)))) (orderedInterval (129906012 / 1000000000000) (129906023 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate221_chunkChecks0_2 :
    compactCertificate221.chunkChecks (0 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 0) <| besselDerivativeNearFromState (411180919293189 / 4000000000000) 0 (IntervalRat.scale (201 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (7319558041 / 1000000000000) (7319558068 / 1000000000000), orderedInterval (-78391091506 / 1000000000000) (-78391091479 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 0) <| besselDerivativeNearFromState (348562618988829 / 4000000000000) 0 (IntervalRat.scale (201 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-3415915082 / 1000000000000) (-3415915069 / 1000000000000), orderedInterval (85425154290 / 1000000000000) (85425154303 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 0) <| besselDerivativeNearFromState (218114302681887 / 4000000000000) 0 (IntervalRat.scale (201 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-102084331363 / 1000000000000) (-102084329418 / 1000000000000), orderedInterval (36339083584 / 1000000000000) (36339085529 / 1000000000000)))) (orderedInterval (-4300384457 / 1000000000000) (-4300384362 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 0) <| besselDerivativeNearFromState (117302597397729 / 4000000000000) 0 (IntervalRat.scale (201 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-142313152014 / 1000000000000) (-142313151279 / 1000000000000), orderedInterval (40542290946 / 1000000000000) (40542291681 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 0) <| besselDerivativeNearFromState (318499370540187 / 4000000000000) 0 (IntervalRat.scale (201 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-85472774439 / 1000000000000) (-85472772956 / 1000000000000), orderedInterval (26795319603 / 1000000000000) (26795321086 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 0) <| besselDerivativeNearFromState (434883661123899 / 4000000000000) 0 (IntervalRat.scale (201 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (33323937719 / 1000000000000) (33323940455 / 1000000000000), orderedInterval (-69037898649 / 1000000000000) (-69037895913 / 1000000000000)))) (orderedInterval (2013028847 / 1000000000000) (2013029117 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 0) <| besselDerivativeNearFromState (183885697318113 / 4000000000000) 0 (IntervalRat.scale (201 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (42529491461 / 1000000000000) (42529493009 / 1000000000000), orderedInterval (-110189489129 / 1000000000000) (-110189487580 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 0) <| besselDerivativeNearFromState (747485150569473 / 4000000000000) 0 (IntervalRat.scale (201 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-43444850286 / 1000000000000) (-43444770305 / 1000000000000), orderedInterval (39094087026 / 1000000000000) (39094167007 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 0) <| besselDerivativeNearFromState (499285439081007 / 4000000000000) 0 (IntervalRat.scale (201 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-4136197489 / 1000000000000) (-4136197475 / 1000000000000), orderedInterval (71312988611 / 1000000000000) (71312988624 / 1000000000000)))) (orderedInterval (4568923581 / 1000000000000) (4568930132 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate221_chunkChecks0 :
    compactCertificate221.chunkChecks (0 : Fin 5) 0 9 = true :=
  compactCertificate221.chunkChecks_nine_of_three (0 : Fin 5) compactCertificate221_chunkChecks0_0
    compactCertificate221_chunkChecks0_1 compactCertificate221_chunkChecks0_2

theorem compactCertificate221_chunkChecks1_0 :
    compactCertificate221.chunkChecks (1 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 1) <| besselDerivativeNearFromState (201 / 2) 1 (IntervalRat.scale (201 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (54436573814 / 1000000000000) (54436573815 / 1000000000000), orderedInterval (57791123996 / 1000000000000) (57791123997 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 1) <| besselDerivativeNearFromState (296111380528101 / 4000000000000) 1 (IntervalRat.scale (201 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-51336441989 / 1000000000000) (-51336428624 / 1000000000000), orderedInterval (77576114358 / 1000000000000) (77576127723 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 1) <| besselDerivativeNearFromState (95756336470533 / 800000000000) 1 (IntervalRat.scale (201 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (64970024996 / 1000000000000) (64970024997 / 1000000000000), orderedInterval (32857643090 / 1000000000000) (32857643091 / 1000000000000)))) (orderedInterval (25735227145 / 1000000000000) (25735227246 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 1) <| besselDerivativeNearFromState (86404562325807 / 4000000000000) 1 (IntervalRat.scale (201 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-65197387715 / 1000000000000) (-65197387714 / 1000000000000), orderedInterval (-157320147385 / 1000000000000) (-157320147384 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 1) <| besselDerivativeNearFromState (232094808214179 / 4000000000000) 1 (IntervalRat.scale (201 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (80950999283 / 1000000000000) (80951063827 / 1000000000000), orderedInterval (-67169873553 / 1000000000000) (-67169809008 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 1) <| besselDerivativeNearFromState (630182553171543 / 4000000000000) 1 (IntervalRat.scale (201 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (60336892517 / 1000000000000) (60336892518 / 1000000000000), orderedInterval (19816072230 / 1000000000000) (19816072231 / 1000000000000)))) (orderedInterval (-3257420070 / 1000000000000) (-3257418695 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 1) <| besselDerivativeNearFromState (464189616428559 / 4000000000000) 1 (IntervalRat.scale (201 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-41379550155 / 1000000000000) (-41379550154 / 1000000000000), orderedInterval (-61251445124 / 1000000000000) (-61251445123 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 1) <| besselDerivativeNearFromState (795396819608907 / 4000000000000) 1 (IntervalRat.scale (201 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-56005635084 / 1000000000000) (-56005634616 / 1000000000000), orderedInterval (8195603517 / 1000000000000) (8195603985 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 1) <| besselDerivativeNearFromState (585885697318113 / 4000000000000) 1 (IntervalRat.scale (201 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (25605440676 / 1000000000000) (25605441904 / 1000000000000), orderedInterval (-60838985779 / 1000000000000) (-60838984551 / 1000000000000)))) (orderedInterval (-2643100571 / 1000000000000) (-2643100488 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate221_chunkChecks1_1 :
    compactCertificate221.chunkChecks (1 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 1) <| besselDerivativeNearFromState (898899326954799 / 4000000000000) 1 (IntervalRat.scale (201 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-33673791186 / 1000000000000) (-33673774488 / 1000000000000), orderedInterval (41293397834 / 1000000000000) (41293414533 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 1) <| besselDerivativeNearFromState (518979768391671 / 4000000000000) 1 (IntervalRat.scale (201 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-69226311077 / 1000000000000) (-69226310733 / 1000000000000), orderedInterval (10961875384 / 1000000000000) (10961875727 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 1) <| besselDerivativeNearFromState (920938706235939 / 4000000000000) 1 (IntervalRat.scale (201 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-52251827224 / 1000000000000) (-52251826835 / 1000000000000), orderedInterval (6015250088 / 1000000000000) (6015250477 / 1000000000000)))) (orderedInterval (-13399318254 / 1000000000000) (-13399311376 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 1) <| besselDerivativeNearFromState (860460400392591 / 4000000000000) 1 (IntervalRat.scale (201 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (41579092180 / 1000000000000) (41579183898 / 1000000000000), orderedInterval (-35176762400 / 1000000000000) (-35176670681 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 1) <| besselDerivativeNearFromState (614065143123903 / 4000000000000) 1 (IntervalRat.scale (201 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-22855647182 / 1000000000000) (-22855647181 / 1000000000000), orderedInterval (-60129845491 / 1000000000000) (-60129845490 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 1) <| besselDerivativeNearFromState (696284424642537 / 4000000000000) 1 (IntervalRat.scale (201 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-53147185073 / 1000000000000) (-53147165633 / 1000000000000), orderedInterval (29007617445 / 1000000000000) (29007636885 / 1000000000000)))) (orderedInterval (-7580556108 / 1000000000000) (-7580552373 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 1) <| besselDerivativeNearFromState (580489361966553 / 4000000000000) 1 (IntervalRat.scale (201 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (65195667455 / 1000000000000) (65195667458 / 1000000000000), orderedInterval (11449302166 / 1000000000000) (11449302169 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 1) <| besselDerivativeNearFromState (512879955773613 / 4000000000000) 1 (IntervalRat.scale (201 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-13937589231 / 1000000000000) (-13937589230 / 1000000000000), orderedInterval (-69016897119 / 1000000000000) (-69016897118 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 1) <| besselDerivativeNearFromState (148652601639687 / 800000000000) 1 (IntervalRat.scale (201 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-55481828098 / 1000000000000) (-55481828097 / 1000000000000), orderedInterval (-18501113937 / 1000000000000) (-18501113936 / 1000000000000)))) (orderedInterval (4354074224 / 1000000000000) (4354074238 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate221_chunkChecks1_2 :
    compactCertificate221.chunkChecks (1 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 1) <| besselDerivativeNearFromState (411180919293189 / 4000000000000) 1 (IntervalRat.scale (201 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (7319558041 / 1000000000000) (7319558068 / 1000000000000), orderedInterval (-78391091506 / 1000000000000) (-78391091479 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 1) <| besselDerivativeNearFromState (348562618988829 / 4000000000000) 1 (IntervalRat.scale (201 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-3415915082 / 1000000000000) (-3415915069 / 1000000000000), orderedInterval (85425154290 / 1000000000000) (85425154303 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 1) <| besselDerivativeNearFromState (218114302681887 / 4000000000000) 1 (IntervalRat.scale (201 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-102084331363 / 1000000000000) (-102084329418 / 1000000000000), orderedInterval (36339083584 / 1000000000000) (36339085529 / 1000000000000)))) (orderedInterval (9269937242 / 1000000000000) (9269937305 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 1) <| besselDerivativeNearFromState (117302597397729 / 4000000000000) 1 (IntervalRat.scale (201 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-142313152014 / 1000000000000) (-142313151279 / 1000000000000), orderedInterval (40542290946 / 1000000000000) (40542291681 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 1) <| besselDerivativeNearFromState (318499370540187 / 4000000000000) 1 (IntervalRat.scale (201 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-85472774439 / 1000000000000) (-85472772956 / 1000000000000), orderedInterval (26795319603 / 1000000000000) (26795321086 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 1) <| besselDerivativeNearFromState (434883661123899 / 4000000000000) 1 (IntervalRat.scale (201 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (33323937719 / 1000000000000) (33323940455 / 1000000000000), orderedInterval (-69037898649 / 1000000000000) (-69037895913 / 1000000000000)))) (orderedInterval (5023712249 / 1000000000000) (5023712518 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 1) <| besselDerivativeNearFromState (183885697318113 / 4000000000000) 1 (IntervalRat.scale (201 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (42529491461 / 1000000000000) (42529493009 / 1000000000000), orderedInterval (-110189489129 / 1000000000000) (-110189487580 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 1) <| besselDerivativeNearFromState (747485150569473 / 4000000000000) 1 (IntervalRat.scale (201 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-43444850286 / 1000000000000) (-43444770305 / 1000000000000), orderedInterval (39094087026 / 1000000000000) (39094167007 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 1) <| besselDerivativeNearFromState (499285439081007 / 4000000000000) 1 (IntervalRat.scale (201 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-4136197489 / 1000000000000) (-4136197475 / 1000000000000), orderedInterval (71312988611 / 1000000000000) (71312988624 / 1000000000000)))) (orderedInterval (-22839399872 / 1000000000000) (-22839387719 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate221_chunkChecks1 :
    compactCertificate221.chunkChecks (1 : Fin 5) 0 9 = true :=
  compactCertificate221.chunkChecks_nine_of_three (1 : Fin 5) compactCertificate221_chunkChecks1_0
    compactCertificate221_chunkChecks1_1 compactCertificate221_chunkChecks1_2

theorem compactCertificate221_chunkChecks2_0 :
    compactCertificate221.chunkChecks (2 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 2) <| besselDerivativeNearFromState (201 / 2) 2 (IntervalRat.scale (201 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (54436573814 / 1000000000000) (54436573815 / 1000000000000), orderedInterval (57791123996 / 1000000000000) (57791123997 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 2) <| besselDerivativeNearFromState (296111380528101 / 4000000000000) 2 (IntervalRat.scale (201 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-51336441989 / 1000000000000) (-51336428624 / 1000000000000), orderedInterval (77576114358 / 1000000000000) (77576127723 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 2) <| besselDerivativeNearFromState (95756336470533 / 800000000000) 2 (IntervalRat.scale (201 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (64970024996 / 1000000000000) (64970024997 / 1000000000000), orderedInterval (32857643090 / 1000000000000) (32857643091 / 1000000000000)))) (orderedInterval (-26981254263 / 1000000000000) (-26981254184 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 2) <| besselDerivativeNearFromState (86404562325807 / 4000000000000) 2 (IntervalRat.scale (201 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-65197387715 / 1000000000000) (-65197387714 / 1000000000000), orderedInterval (-157320147385 / 1000000000000) (-157320147384 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 2) <| besselDerivativeNearFromState (232094808214179 / 4000000000000) 2 (IntervalRat.scale (201 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (80950999283 / 1000000000000) (80951063827 / 1000000000000), orderedInterval (-67169873553 / 1000000000000) (-67169809008 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 2) <| besselDerivativeNearFromState (630182553171543 / 4000000000000) 2 (IntervalRat.scale (201 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (60336892517 / 1000000000000) (60336892518 / 1000000000000), orderedInterval (19816072230 / 1000000000000) (19816072231 / 1000000000000)))) (orderedInterval (9555223728 / 1000000000000) (9555224547 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 2) <| besselDerivativeNearFromState (464189616428559 / 4000000000000) 2 (IntervalRat.scale (201 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-41379550155 / 1000000000000) (-41379550154 / 1000000000000), orderedInterval (-61251445124 / 1000000000000) (-61251445123 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 2) <| besselDerivativeNearFromState (795396819608907 / 4000000000000) 2 (IntervalRat.scale (201 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-56005635084 / 1000000000000) (-56005634616 / 1000000000000), orderedInterval (8195603517 / 1000000000000) (8195603985 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 2) <| besselDerivativeNearFromState (585885697318113 / 4000000000000) 2 (IntervalRat.scale (201 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (25605440676 / 1000000000000) (25605441904 / 1000000000000), orderedInterval (-60838985779 / 1000000000000) (-60838984551 / 1000000000000)))) (orderedInterval (-8050827254 / 1000000000000) (-8050827116 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate221_chunkChecks2_1 :
    compactCertificate221.chunkChecks (2 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 2) <| besselDerivativeNearFromState (898899326954799 / 4000000000000) 2 (IntervalRat.scale (201 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-33673791186 / 1000000000000) (-33673774488 / 1000000000000), orderedInterval (41293397834 / 1000000000000) (41293414533 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 2) <| besselDerivativeNearFromState (518979768391671 / 4000000000000) 2 (IntervalRat.scale (201 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-69226311077 / 1000000000000) (-69226310733 / 1000000000000), orderedInterval (10961875384 / 1000000000000) (10961875727 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 2) <| besselDerivativeNearFromState (920938706235939 / 4000000000000) 2 (IntervalRat.scale (201 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-52251827224 / 1000000000000) (-52251826835 / 1000000000000), orderedInterval (6015250088 / 1000000000000) (6015250477 / 1000000000000)))) (orderedInterval (17747734557 / 1000000000000) (17747749971 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 2) <| besselDerivativeNearFromState (860460400392591 / 4000000000000) 2 (IntervalRat.scale (201 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (41579092180 / 1000000000000) (41579183898 / 1000000000000), orderedInterval (-35176762400 / 1000000000000) (-35176670681 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 2) <| besselDerivativeNearFromState (614065143123903 / 4000000000000) 2 (IntervalRat.scale (201 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-22855647182 / 1000000000000) (-22855647181 / 1000000000000), orderedInterval (-60129845491 / 1000000000000) (-60129845490 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 2) <| besselDerivativeNearFromState (696284424642537 / 4000000000000) 2 (IntervalRat.scale (201 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-53147185073 / 1000000000000) (-53147165633 / 1000000000000), orderedInterval (29007617445 / 1000000000000) (29007636885 / 1000000000000)))) (orderedInterval (7750616362 / 1000000000000) (7750624313 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 2) <| besselDerivativeNearFromState (580489361966553 / 4000000000000) 2 (IntervalRat.scale (201 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (65195667455 / 1000000000000) (65195667458 / 1000000000000), orderedInterval (11449302166 / 1000000000000) (11449302169 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 2) <| besselDerivativeNearFromState (512879955773613 / 4000000000000) 2 (IntervalRat.scale (201 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-13937589231 / 1000000000000) (-13937589230 / 1000000000000), orderedInterval (-69016897119 / 1000000000000) (-69016897118 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 2) <| besselDerivativeNearFromState (148652601639687 / 800000000000) 2 (IntervalRat.scale (201 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-55481828098 / 1000000000000) (-55481828097 / 1000000000000), orderedInterval (-18501113937 / 1000000000000) (-18501113936 / 1000000000000)))) (orderedInterval (1944719557 / 1000000000000) (1944719579 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate221_chunkChecks2_2 :
    compactCertificate221.chunkChecks (2 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 2) <| besselDerivativeNearFromState (411180919293189 / 4000000000000) 2 (IntervalRat.scale (201 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (7319558041 / 1000000000000) (7319558068 / 1000000000000), orderedInterval (-78391091506 / 1000000000000) (-78391091479 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 2) <| besselDerivativeNearFromState (348562618988829 / 4000000000000) 2 (IntervalRat.scale (201 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-3415915082 / 1000000000000) (-3415915069 / 1000000000000), orderedInterval (85425154290 / 1000000000000) (85425154303 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 2) <| besselDerivativeNearFromState (218114302681887 / 4000000000000) 2 (IntervalRat.scale (201 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-102084331363 / 1000000000000) (-102084329418 / 1000000000000), orderedInterval (36339083584 / 1000000000000) (36339085529 / 1000000000000)))) (orderedInterval (1965170381 / 1000000000000) (1965170428 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 2) <| besselDerivativeNearFromState (117302597397729 / 4000000000000) 2 (IntervalRat.scale (201 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-142313152014 / 1000000000000) (-142313151279 / 1000000000000), orderedInterval (40542290946 / 1000000000000) (40542291681 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 2) <| besselDerivativeNearFromState (318499370540187 / 4000000000000) 2 (IntervalRat.scale (201 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-85472774439 / 1000000000000) (-85472772956 / 1000000000000), orderedInterval (26795319603 / 1000000000000) (26795321086 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 2) <| besselDerivativeNearFromState (434883661123899 / 4000000000000) 2 (IntervalRat.scale (201 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (33323937719 / 1000000000000) (33323940455 / 1000000000000), orderedInterval (-69037898649 / 1000000000000) (-69037895913 / 1000000000000)))) (orderedInterval (1497867373 / 1000000000000) (1497867655 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 2) <| besselDerivativeNearFromState (183885697318113 / 4000000000000) 2 (IntervalRat.scale (201 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (42529491461 / 1000000000000) (42529493009 / 1000000000000), orderedInterval (-110189489129 / 1000000000000) (-110189487580 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 2) <| besselDerivativeNearFromState (747485150569473 / 4000000000000) 2 (IntervalRat.scale (201 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-43444850286 / 1000000000000) (-43444770305 / 1000000000000), orderedInterval (39094087026 / 1000000000000) (39094167007 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 2) <| besselDerivativeNearFromState (499285439081007 / 4000000000000) 2 (IntervalRat.scale (201 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-4136197489 / 1000000000000) (-4136197475 / 1000000000000), orderedInterval (71312988611 / 1000000000000) (71312988624 / 1000000000000)))) (orderedInterval (-13250666858 / 1000000000000) (-13250644164 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate221_chunkChecks2 :
    compactCertificate221.chunkChecks (2 : Fin 5) 0 9 = true :=
  compactCertificate221.chunkChecks_nine_of_three (2 : Fin 5) compactCertificate221_chunkChecks2_0
    compactCertificate221_chunkChecks2_1 compactCertificate221_chunkChecks2_2

theorem compactCertificate221_chunkChecks3_0 :
    compactCertificate221.chunkChecks (3 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 3) <| besselDerivativeNearFromState (201 / 2) 3 (IntervalRat.scale (201 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (54436573814 / 1000000000000) (54436573815 / 1000000000000), orderedInterval (57791123996 / 1000000000000) (57791123997 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 3) <| besselDerivativeNearFromState (296111380528101 / 4000000000000) 3 (IntervalRat.scale (201 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-51336441989 / 1000000000000) (-51336428624 / 1000000000000), orderedInterval (77576114358 / 1000000000000) (77576127723 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 3) <| besselDerivativeNearFromState (95756336470533 / 800000000000) 3 (IntervalRat.scale (201 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (64970024996 / 1000000000000) (64970024997 / 1000000000000), orderedInterval (32857643090 / 1000000000000) (32857643091 / 1000000000000)))) (orderedInterval (-26181642854 / 1000000000000) (-26181642792 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 3) <| besselDerivativeNearFromState (86404562325807 / 4000000000000) 3 (IntervalRat.scale (201 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-65197387715 / 1000000000000) (-65197387714 / 1000000000000), orderedInterval (-157320147385 / 1000000000000) (-157320147384 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 3) <| besselDerivativeNearFromState (232094808214179 / 4000000000000) 3 (IntervalRat.scale (201 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (80950999283 / 1000000000000) (80951063827 / 1000000000000), orderedInterval (-67169873553 / 1000000000000) (-67169809008 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 3) <| besselDerivativeNearFromState (630182553171543 / 4000000000000) 3 (IntervalRat.scale (201 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (60336892517 / 1000000000000) (60336892518 / 1000000000000), orderedInterval (19816072230 / 1000000000000) (19816072231 / 1000000000000)))) (orderedInterval (5786447094 / 1000000000000) (5786447584 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 3) <| besselDerivativeNearFromState (464189616428559 / 4000000000000) 3 (IntervalRat.scale (201 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-41379550155 / 1000000000000) (-41379550154 / 1000000000000), orderedInterval (-61251445124 / 1000000000000) (-61251445123 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 3) <| besselDerivativeNearFromState (795396819608907 / 4000000000000) 3 (IntervalRat.scale (201 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-56005635084 / 1000000000000) (-56005634616 / 1000000000000), orderedInterval (8195603517 / 1000000000000) (8195603985 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 3) <| besselDerivativeNearFromState (585885697318113 / 4000000000000) 3 (IntervalRat.scale (201 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (25605440676 / 1000000000000) (25605441904 / 1000000000000), orderedInterval (-60838985779 / 1000000000000) (-60838984551 / 1000000000000)))) (orderedInterval (6589707084 / 1000000000000) (6589707322 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate221_chunkChecks3_1 :
    compactCertificate221.chunkChecks (3 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 3) <| besselDerivativeNearFromState (898899326954799 / 4000000000000) 3 (IntervalRat.scale (201 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-33673791186 / 1000000000000) (-33673774488 / 1000000000000), orderedInterval (41293397834 / 1000000000000) (41293414533 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 3) <| besselDerivativeNearFromState (518979768391671 / 4000000000000) 3 (IntervalRat.scale (201 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-69226311077 / 1000000000000) (-69226310733 / 1000000000000), orderedInterval (10961875384 / 1000000000000) (10961875727 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 3) <| besselDerivativeNearFromState (920938706235939 / 4000000000000) 3 (IntervalRat.scale (201 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-52251827224 / 1000000000000) (-52251826835 / 1000000000000), orderedInterval (6015250088 / 1000000000000) (6015250477 / 1000000000000)))) (orderedInterval (69827535682 / 1000000000000) (69827570114 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 3) <| besselDerivativeNearFromState (860460400392591 / 4000000000000) 3 (IntervalRat.scale (201 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (41579092180 / 1000000000000) (41579183898 / 1000000000000), orderedInterval (-35176762400 / 1000000000000) (-35176670681 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 3) <| besselDerivativeNearFromState (614065143123903 / 4000000000000) 3 (IntervalRat.scale (201 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-22855647182 / 1000000000000) (-22855647181 / 1000000000000), orderedInterval (-60129845491 / 1000000000000) (-60129845490 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 3) <| besselDerivativeNearFromState (696284424642537 / 4000000000000) 3 (IntervalRat.scale (201 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-53147185073 / 1000000000000) (-53147165633 / 1000000000000), orderedInterval (29007617445 / 1000000000000) (29007636885 / 1000000000000)))) (orderedInterval (14723649858 / 1000000000000) (14723666741 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 3) <| besselDerivativeNearFromState (580489361966553 / 4000000000000) 3 (IntervalRat.scale (201 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (65195667455 / 1000000000000) (65195667458 / 1000000000000), orderedInterval (11449302166 / 1000000000000) (11449302169 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 3) <| besselDerivativeNearFromState (512879955773613 / 4000000000000) 3 (IntervalRat.scale (201 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-13937589231 / 1000000000000) (-13937589230 / 1000000000000), orderedInterval (-69016897119 / 1000000000000) (-69016897118 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 3) <| besselDerivativeNearFromState (148652601639687 / 800000000000) 3 (IntervalRat.scale (201 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-55481828098 / 1000000000000) (-55481828097 / 1000000000000), orderedInterval (-18501113937 / 1000000000000) (-18501113936 / 1000000000000)))) (orderedInterval (-5625050204 / 1000000000000) (-5625050171 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate221_chunkChecks3_2 :
    compactCertificate221.chunkChecks (3 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 3) <| besselDerivativeNearFromState (411180919293189 / 4000000000000) 3 (IntervalRat.scale (201 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (7319558041 / 1000000000000) (7319558068 / 1000000000000), orderedInterval (-78391091506 / 1000000000000) (-78391091479 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 3) <| besselDerivativeNearFromState (348562618988829 / 4000000000000) 3 (IntervalRat.scale (201 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-3415915082 / 1000000000000) (-3415915069 / 1000000000000), orderedInterval (85425154290 / 1000000000000) (85425154303 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 3) <| besselDerivativeNearFromState (218114302681887 / 4000000000000) 3 (IntervalRat.scale (201 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-102084331363 / 1000000000000) (-102084329418 / 1000000000000), orderedInterval (36339083584 / 1000000000000) (36339085529 / 1000000000000)))) (orderedInterval (-10468415028 / 1000000000000) (-10468414991 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 3) <| besselDerivativeNearFromState (117302597397729 / 4000000000000) 3 (IntervalRat.scale (201 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-142313152014 / 1000000000000) (-142313151279 / 1000000000000), orderedInterval (40542290946 / 1000000000000) (40542291681 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 3) <| besselDerivativeNearFromState (318499370540187 / 4000000000000) 3 (IntervalRat.scale (201 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-85472774439 / 1000000000000) (-85472772956 / 1000000000000), orderedInterval (26795319603 / 1000000000000) (26795321086 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 3) <| besselDerivativeNearFromState (434883661123899 / 4000000000000) 3 (IntervalRat.scale (201 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (33323937719 / 1000000000000) (33323940455 / 1000000000000), orderedInterval (-69037898649 / 1000000000000) (-69037895913 / 1000000000000)))) (orderedInterval (-6391980551 / 1000000000000) (-6391980254 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 3) <| besselDerivativeNearFromState (183885697318113 / 4000000000000) 3 (IntervalRat.scale (201 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (42529491461 / 1000000000000) (42529493009 / 1000000000000), orderedInterval (-110189489129 / 1000000000000) (-110189487580 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 3) <| besselDerivativeNearFromState (747485150569473 / 4000000000000) 3 (IntervalRat.scale (201 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-43444850286 / 1000000000000) (-43444770305 / 1000000000000), orderedInterval (39094087026 / 1000000000000) (39094167007 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 3) <| besselDerivativeNearFromState (499285439081007 / 4000000000000) 3 (IntervalRat.scale (201 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-4136197489 / 1000000000000) (-4136197475 / 1000000000000), orderedInterval (71312988611 / 1000000000000) (71312988624 / 1000000000000)))) (orderedInterval (46286585029 / 1000000000000) (46286627201 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate221_chunkChecks3 :
    compactCertificate221.chunkChecks (3 : Fin 5) 0 9 = true :=
  compactCertificate221.chunkChecks_nine_of_three (3 : Fin 5) compactCertificate221_chunkChecks3_0
    compactCertificate221_chunkChecks3_1 compactCertificate221_chunkChecks3_2

theorem compactCertificate221_chunkChecks4_0 :
    compactCertificate221.chunkChecks (4 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 4) <| besselDerivativeNearFromState (201 / 2) 4 (IntervalRat.scale (201 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (54436573814 / 1000000000000) (54436573815 / 1000000000000), orderedInterval (57791123996 / 1000000000000) (57791123997 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 4) <| besselDerivativeNearFromState (296111380528101 / 4000000000000) 4 (IntervalRat.scale (201 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-51336441989 / 1000000000000) (-51336428624 / 1000000000000), orderedInterval (77576114358 / 1000000000000) (77576127723 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 4) <| besselDerivativeNearFromState (95756336470533 / 800000000000) 4 (IntervalRat.scale (201 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (64970024996 / 1000000000000) (64970024997 / 1000000000000), orderedInterval (32857643090 / 1000000000000) (32857643091 / 1000000000000)))) (orderedInterval (29625359117 / 1000000000000) (29625359168 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 4) <| besselDerivativeNearFromState (86404562325807 / 4000000000000) 4 (IntervalRat.scale (201 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-65197387715 / 1000000000000) (-65197387714 / 1000000000000), orderedInterval (-157320147385 / 1000000000000) (-157320147384 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 4) <| besselDerivativeNearFromState (232094808214179 / 4000000000000) 4 (IntervalRat.scale (201 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (80950999283 / 1000000000000) (80951063827 / 1000000000000), orderedInterval (-67169873553 / 1000000000000) (-67169809008 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 4) <| besselDerivativeNearFromState (630182553171543 / 4000000000000) 4 (IntervalRat.scale (201 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (60336892517 / 1000000000000) (60336892518 / 1000000000000), orderedInterval (19816072230 / 1000000000000) (19816072231 / 1000000000000)))) (orderedInterval (-25687316267 / 1000000000000) (-25687315951 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 4) <| besselDerivativeNearFromState (464189616428559 / 4000000000000) 4 (IntervalRat.scale (201 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-41379550155 / 1000000000000) (-41379550154 / 1000000000000), orderedInterval (-61251445124 / 1000000000000) (-61251445123 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 4) <| besselDerivativeNearFromState (795396819608907 / 4000000000000) 4 (IntervalRat.scale (201 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-56005635084 / 1000000000000) (-56005634616 / 1000000000000), orderedInterval (8195603517 / 1000000000000) (8195603985 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 4) <| besselDerivativeNearFromState (585885697318113 / 4000000000000) 4 (IntervalRat.scale (201 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (25605440676 / 1000000000000) (25605441904 / 1000000000000), orderedInterval (-60838985779 / 1000000000000) (-60838984551 / 1000000000000)))) (orderedInterval (29134958591 / 1000000000000) (29134959010 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate221_chunkChecks4_1 :
    compactCertificate221.chunkChecks (4 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 4) <| besselDerivativeNearFromState (898899326954799 / 4000000000000) 4 (IntervalRat.scale (201 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-33673791186 / 1000000000000) (-33673774488 / 1000000000000), orderedInterval (41293397834 / 1000000000000) (41293414533 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 4) <| besselDerivativeNearFromState (518979768391671 / 4000000000000) 4 (IntervalRat.scale (201 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-69226311077 / 1000000000000) (-69226310733 / 1000000000000), orderedInterval (10961875384 / 1000000000000) (10961875727 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 4) <| besselDerivativeNearFromState (920938706235939 / 4000000000000) 4 (IntervalRat.scale (201 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-52251827224 / 1000000000000) (-52251826835 / 1000000000000), orderedInterval (6015250088 / 1000000000000) (6015250477 / 1000000000000)))) (orderedInterval (-70640055102 / 1000000000000) (-70639977800 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 4) <| besselDerivativeNearFromState (860460400392591 / 4000000000000) 4 (IntervalRat.scale (201 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (41579092180 / 1000000000000) (41579183898 / 1000000000000), orderedInterval (-35176762400 / 1000000000000) (-35176670681 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 4) <| besselDerivativeNearFromState (614065143123903 / 4000000000000) 4 (IntervalRat.scale (201 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-22855647182 / 1000000000000) (-22855647181 / 1000000000000), orderedInterval (-60129845491 / 1000000000000) (-60129845490 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 4) <| besselDerivativeNearFromState (696284424642537 / 4000000000000) 4 (IntervalRat.scale (201 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-53147185073 / 1000000000000) (-53147165633 / 1000000000000), orderedInterval (29007617445 / 1000000000000) (29007636885 / 1000000000000)))) (orderedInterval (-25394717669 / 1000000000000) (-25394681601 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 4) <| besselDerivativeNearFromState (580489361966553 / 4000000000000) 4 (IntervalRat.scale (201 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (65195667455 / 1000000000000) (65195667458 / 1000000000000), orderedInterval (11449302166 / 1000000000000) (11449302169 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 4) <| besselDerivativeNearFromState (512879955773613 / 4000000000000) 4 (IntervalRat.scale (201 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-13937589231 / 1000000000000) (-13937589230 / 1000000000000), orderedInterval (-69016897119 / 1000000000000) (-69016897118 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 4) <| besselDerivativeNearFromState (148652601639687 / 800000000000) 4 (IntervalRat.scale (201 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-55481828098 / 1000000000000) (-55481828097 / 1000000000000), orderedInterval (-18501113937 / 1000000000000) (-18501113936 / 1000000000000)))) (orderedInterval (-11101941352 / 1000000000000) (-11101941300 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate221_chunkChecks4_2 :
    compactCertificate221.chunkChecks (4 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 4) <| besselDerivativeNearFromState (411180919293189 / 4000000000000) 4 (IntervalRat.scale (201 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (7319558041 / 1000000000000) (7319558068 / 1000000000000), orderedInterval (-78391091506 / 1000000000000) (-78391091479 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 4) <| besselDerivativeNearFromState (348562618988829 / 4000000000000) 4 (IntervalRat.scale (201 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-3415915082 / 1000000000000) (-3415915069 / 1000000000000), orderedInterval (85425154290 / 1000000000000) (85425154303 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 4) <| besselDerivativeNearFromState (218114302681887 / 4000000000000) 4 (IntervalRat.scale (201 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-102084331363 / 1000000000000) (-102084329418 / 1000000000000), orderedInterval (36339083584 / 1000000000000) (36339085529 / 1000000000000)))) (orderedInterval (-1251195224 / 1000000000000) (-1251195191 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 4) <| besselDerivativeNearFromState (117302597397729 / 4000000000000) 4 (IntervalRat.scale (201 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-142313152014 / 1000000000000) (-142313151279 / 1000000000000), orderedInterval (40542290946 / 1000000000000) (40542291681 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 4) <| besselDerivativeNearFromState (318499370540187 / 4000000000000) 4 (IntervalRat.scale (201 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-85472774439 / 1000000000000) (-85472772956 / 1000000000000), orderedInterval (26795319603 / 1000000000000) (26795321086 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 4) <| besselDerivativeNearFromState (434883661123899 / 4000000000000) 4 (IntervalRat.scale (201 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (33323937719 / 1000000000000) (33323940455 / 1000000000000), orderedInterval (-69037898649 / 1000000000000) (-69037895913 / 1000000000000)))) (orderedInterval (-2587322169 / 1000000000000) (-2587321851 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 4) <| besselDerivativeNearFromState (183885697318113 / 4000000000000) 4 (IntervalRat.scale (201 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (42529491461 / 1000000000000) (42529493009 / 1000000000000), orderedInterval (-110189489129 / 1000000000000) (-110189487580 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 4) <| besselDerivativeNearFromState (747485150569473 / 4000000000000) 4 (IntervalRat.scale (201 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-43444850286 / 1000000000000) (-43444770305 / 1000000000000), orderedInterval (39094087026 / 1000000000000) (39094167007 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 4) <| besselDerivativeNearFromState (499285439081007 / 4000000000000) 4 (IntervalRat.scale (201 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-4136197489 / 1000000000000) (-4136197475 / 1000000000000), orderedInterval (71312988611 / 1000000000000) (71312988624 / 1000000000000)))) (orderedInterval (43209868515 / 1000000000000) (43209947318 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate221_chunkChecks4 :
    compactCertificate221.chunkChecks (4 : Fin 5) 0 9 = true :=
  compactCertificate221.chunkChecks_nine_of_three (4 : Fin 5) compactCertificate221_chunkChecks4_0
    compactCertificate221_chunkChecks4_1 compactCertificate221_chunkChecks4_2

theorem compactCertificate221_chunks :
    ∀ r : Fin 5, ∀ b, compactCertificate221.chunkCheck r b = true :=
  compactCertificate221.chunkChecks_all (by
    intro r
    fin_cases r
    · exact compactCertificate221_chunkChecks0
    · exact compactCertificate221_chunkChecks1
    · exact compactCertificate221_chunkChecks2
    · exact compactCertificate221_chunkChecks3
    · exact compactCertificate221_chunkChecks4)

theorem compactCertificate221_coefficient0 :
    compactCertificate221.coefficientCheck (0 : Fin 5) = true := by
  norm_num [CompactCertificate.coefficientCheck, intervalFinSumHull,
    compactCertificate221, rationalIntervalSubset, orderedInterval, Fin.sum_univ_succ]

theorem compactCertificate221_coefficient1 :
    compactCertificate221.coefficientCheck (1 : Fin 5) = true := by
  norm_num [CompactCertificate.coefficientCheck, intervalFinSumHull,
    compactCertificate221, rationalIntervalSubset, orderedInterval, Fin.sum_univ_succ]

theorem compactCertificate221_coefficient2 :
    compactCertificate221.coefficientCheck (2 : Fin 5) = true := by
  norm_num [CompactCertificate.coefficientCheck, intervalFinSumHull,
    compactCertificate221, rationalIntervalSubset, orderedInterval, Fin.sum_univ_succ]

theorem compactCertificate221_coefficient3 :
    compactCertificate221.coefficientCheck (3 : Fin 5) = true := by
  norm_num [CompactCertificate.coefficientCheck, intervalFinSumHull,
    compactCertificate221, rationalIntervalSubset, orderedInterval, Fin.sum_univ_succ]

theorem compactCertificate221_coefficient4 :
    compactCertificate221.coefficientCheck (4 : Fin 5) = true := by
  norm_num [CompactCertificate.coefficientCheck, intervalFinSumHull,
    compactCertificate221, rationalIntervalSubset, orderedInterval, Fin.sum_univ_succ]

theorem compactCertificate221_coefficients : ∀ r : Fin 5,
    compactCertificate221.coefficientCheck r = true := by
  intro r
  fin_cases r
  · exact compactCertificate221_coefficient0
  · exact compactCertificate221_coefficient1
  · exact compactCertificate221_coefficient2
  · exact compactCertificate221_coefficient3
  · exact compactCertificate221_coefficient4

theorem compactCertificate221_lower : (1 : ℚ) ≤ compactCertificate221.output.lo := by
  norm_num [CompactCertificate.output, CompactCertificate.interval,
    CompactCertificate.coefficientTargetNat, compactCertificate221, dualConstant,
    intervalTaylorSum, intervalPow, intervalSub, intervalMaxAbs, widenInterval,
    rationalErrorInterval, orderedInterval, IntervalRat.add, IntervalRat.mul, IntervalRat.scale,
    IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4]

theorem compactCertificate221_proves {t : ℝ} (ht : t ∈ compactCertificate221.interval) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t :=
  compactCertificate221.proves compactCertificate221_states compactCertificate221_chunks
    compactCertificate221_coefficients compactCertificate221_lower ht

end Erdos232
