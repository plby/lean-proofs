/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, OpenAI Codex
-/
import ErdosProblems.Erdos232.CompactBase

open LeanCert.Core
namespace Erdos232

def compactCertificate214 : CompactCertificate where
  left := 95
  right := 96
  center := 191 / 2
  grid := fun i =>
    match i.val with
    | 0 => 30
    | 1 => 22
    | 2 => 36
    | 3 => 7
    | 4 => 18
    | 5 => 48
    | 6 => 35
    | 7 => 60
    | 8 => 44
    | 9 => 68
    | 10 => 39
    | 11 => 70
    | 12 => 65
    | 13 => 46
    | 14 => 53
    | 15 => 44
    | 16 => 39
    | 17 => 56
    | 18 => 31
    | 19 => 26
    | 20 => 17
    | 21 => 9
    | 22 => 24
    | 23 => 33
    | 24 => 14
    | 25 => 57
    | _ => 38
  point := fun i =>
    match i.val with
    | 0 => 191 / 2
    | 1 => 281379471049091 / 4000000000000
    | 2 => 90992339631203 / 800000000000
    | 3 => 82105827881737 / 4000000000000
    | 4 => 220547802830389 / 4000000000000
    | 5 => 598830187342113 / 4000000000000
    | 6 => 441095605660969 / 4000000000000
    | 7 => 755824838533837 / 4000000000000
    | 8 => 556737155162983 / 4000000000000
    | 9 => 854177967404809 / 4000000000000
    | 10 => 493159879416961 / 4000000000000
    | 11 => 875120860154549 / 4000000000000
    | 12 => 817651425248681 / 4000000000000
    | 13 => 583514638490873 / 4000000000000
    | 14 => 661643408491167 / 4000000000000
    | 15 => 551609294207023 / 4000000000000
    | 16 => 487363540063483 / 4000000000000
    | 17 => 141256949816817 / 800000000000
    | 18 => 390724157139299 / 4000000000000
    | 19 => 331221195158539 / 4000000000000
    | 20 => 207262844837017 / 4000000000000
    | 21 => 111466647278439 / 4000000000000
    | 22 => 302653630712317 / 4000000000000
    | 23 => 413247658082909 / 4000000000000
    | 24 => 174737155162983 / 4000000000000
    | 25 => 710296834620743 / 4000000000000
    | _ => 474445367484937 / 4000000000000
  state := fun i =>
    match i.val with
    | 0 => (orderedInterval (72958226021 / 1000000000000) (72958235750 / 1000000000000), orderedInterval (-37031907524 / 1000000000000) (-37031897795 / 1000000000000))
    | 1 => (orderedInterval (85961334525 / 1000000000000) (85961341339 / 1000000000000), orderedInterval (-41360026476 / 1000000000000) (-41360019662 / 1000000000000))
    | 2 => (orderedInterval (74045611559 / 1000000000000) (74045611563 / 1000000000000), orderedInterval (10366746115 / 1000000000000) (10366746120 / 1000000000000))
    | 3 => (orderedInterval (111454533145 / 1000000000000) (111454574671 / 1000000000000), orderedInterval (-139074240824 / 1000000000000) (-139074199298 / 1000000000000))
    | 4 => (orderedInterval (-63181234891 / 1000000000000) (-63181213131 / 1000000000000), orderedInterval (87489137011 / 1000000000000) (87489158771 / 1000000000000))
    | 5 => (orderedInterval (-19541020742 / 1000000000000) (-19541020364 / 1000000000000), orderedInterval (62279334485 / 1000000000000) (62279334863 / 1000000000000))
    | 6 => (orderedInterval (-67797589254 / 1000000000000) (-67797589253 / 1000000000000), orderedInterval (-33993172029 / 1000000000000) (-33993172028 / 1000000000000))
    | 7 => (orderedInterval (54998024072 / 1000000000000) (54998024073 / 1000000000000), orderedInterval (18411063353 / 1000000000000) (18411063354 / 1000000000000))
    | 8 => (orderedInterval (66679439312 / 1000000000000) (66679439752 / 1000000000000), orderedInterval (-11542570186 / 1000000000000) (-11542569746 / 1000000000000))
    | 9 => (orderedInterval (35216418359 / 1000000000000) (35216418360 / 1000000000000), orderedInterval (41642950967 / 1000000000000) (41642950968 / 1000000000000))
    | 10 => (orderedInterval (-71845510045 / 1000000000000) (-71845510015 / 1000000000000), orderedInterval (-1041939789 / 1000000000000) (-1041939760 / 1000000000000))
    | 11 => (orderedInterval (-18316638779 / 1000000000000) (-18316638363 / 1000000000000), orderedInterval (50780075643 / 1000000000000) (50780076059 / 1000000000000))
    | 12 => (orderedInterval (-46781515023 / 1000000000000) (-46781515022 / 1000000000000), orderedInterval (-30313656252 / 1000000000000) (-30313656251 / 1000000000000))
    | 13 => (orderedInterval (55288277422 / 1000000000000) (55288313748 / 1000000000000), orderedInterval (-36345156675 / 1000000000000) (-36345120349 / 1000000000000))
    | 14 => (orderedInterval (18861143522 / 1000000000000) (18861143884 / 1000000000000), orderedInterval (-59158534500 / 1000000000000) (-59158534137 / 1000000000000))
    | 15 => (orderedInterval (29965007543 / 1000000000000) (29965007544 / 1000000000000), orderedInterval (60871443770 / 1000000000000) (60871443771 / 1000000000000))
    | 16 => (orderedInterval (-7442425604 / 1000000000000) (-7442425603 / 1000000000000), orderedInterval (-71869825995 / 1000000000000) (-71869825994 / 1000000000000))
    | 17 => (orderedInterval (59422934136 / 1000000000000) (59422934142 / 1000000000000), orderedInterval (8454826416 / 1000000000000) (8454826422 / 1000000000000))
    | 18 => (orderedInterval (-71038992234 / 1000000000000) (-71038992233 / 1000000000000), orderedInterval (-37986699522 / 1000000000000) (-37986699521 / 1000000000000))
    | 19 => (orderedInterval (82749830908 / 1000000000000) (82749833255 / 1000000000000), orderedInterval (-29491170600 / 1000000000000) (-29491168252 / 1000000000000))
    | 20 => (orderedInterval (80156341471 / 1000000000000) (80156449334 / 1000000000000), orderedInterval (-77331639974 / 1000000000000) (-77331532110 / 1000000000000))
    | 21 => (orderedInterval (-55109188431 / 1000000000000) (-55109188430 / 1000000000000), orderedInterval (-139762652794 / 1000000000000) (-139762652793 / 1000000000000))
    | 22 => (orderedInterval (79516378746 / 1000000000000) (79516378747 / 1000000000000), orderedInterval (45200841736 / 1000000000000) (45200841737 / 1000000000000))
    | 23 => (orderedInterval (-32262562731 / 1000000000000) (-32262562730 / 1000000000000), orderedInterval (-71407041255 / 1000000000000) (-71407041254 / 1000000000000))
    | 24 => (orderedInterval (56228307256 / 1000000000000) (56228307257 / 1000000000000), orderedInterval (106184009444 / 1000000000000) (106184009445 / 1000000000000))
    | 25 => (orderedInterval (39114090341 / 1000000000000) (39114117240 / 1000000000000), orderedInterval (-45444243507 / 1000000000000) (-45444216608 / 1000000000000))
    | _ => (orderedInterval (1110993534 / 1000000000000) (1110993539 / 1000000000000), orderedInterval (73248910850 / 1000000000000) (73248910855 / 1000000000000))
  chunkTarget := fun r b =>
    match r.val with
    | 0 =>
      match b.val with
      | 0 => orderedInterval (34064160513 / 1000000000000) (34064164441 / 1000000000000)
      | 1 => orderedInterval (-2126896198 / 1000000000000) (-2126894914 / 1000000000000)
      | 2 => orderedInterval (-84848623 / 1000000000000) (-84848606 / 1000000000000)
      | 3 => orderedInterval (-14184511561 / 1000000000000) (-14184511460 / 1000000000000)
      | 4 => orderedInterval (5977320425 / 1000000000000) (5977323874 / 1000000000000)
      | 5 => orderedInterval (2293393134 / 1000000000000) (2293393144 / 1000000000000)
      | 6 => orderedInterval (9284472431 / 1000000000000) (9284476100 / 1000000000000)
      | 7 => orderedInterval (1686186846 / 1000000000000) (1686186858 / 1000000000000)
      | _ => orderedInterval (-3053447843 / 1000000000000) (-3053445625 / 1000000000000)
    | 1 =>
      match b.val with
      | 0 => orderedInterval (-14237508634 / 1000000000000) (-14237504722 / 1000000000000)
      | 1 => orderedInterval (-4771912141 / 1000000000000) (-4771911529 / 1000000000000)
      | 2 => orderedInterval (-1530154283 / 1000000000000) (-1530154258 / 1000000000000)
      | 3 => orderedInterval (-108101635 / 1000000000000) (-108101417 / 1000000000000)
      | 4 => orderedInterval (-3560048542 / 1000000000000) (-3560043272 / 1000000000000)
      | 5 => orderedInterval (6662557443 / 1000000000000) (6662557458 / 1000000000000)
      | 6 => orderedInterval (6293858396 / 1000000000000) (6293860440 / 1000000000000)
      | 7 => orderedInterval (5860799656 / 1000000000000) (5860799668 / 1000000000000)
      | _ => orderedInterval (-9898170279 / 1000000000000) (-9898166168 / 1000000000000)
    | 2 =>
      match b.val with
      | 0 => orderedInterval (-35367010362 / 1000000000000) (-35367006420 / 1000000000000)
      | 1 => orderedInterval (-2538987356 / 1000000000000) (-2538986979 / 1000000000000)
      | 2 => orderedInterval (3234021739 / 1000000000000) (3234021779 / 1000000000000)
      | 3 => orderedInterval (53826054238 / 1000000000000) (53826054724 / 1000000000000)
      | 4 => orderedInterval (-15744887333 / 1000000000000) (-15744879226 / 1000000000000)
      | 5 => orderedInterval (-6685619203 / 1000000000000) (-6685619182 / 1000000000000)
      | 6 => orderedInterval (-9196230923 / 1000000000000) (-9196229746 / 1000000000000)
      | 7 => orderedInterval (-1909247212 / 1000000000000) (-1909247200 / 1000000000000)
      | _ => orderedInterval (11362570849 / 1000000000000) (11362578519 / 1000000000000)
    | 3 =>
      match b.val with
      | 0 => orderedInterval (14173226270 / 1000000000000) (14173230203 / 1000000000000)
      | 1 => orderedInterval (16452088443 / 1000000000000) (16452088735 / 1000000000000)
      | 2 => orderedInterval (5228237516 / 1000000000000) (5228237581 / 1000000000000)
      | 3 => orderedInterval (-4459676361 / 1000000000000) (-4459675270 / 1000000000000)
      | 4 => orderedInterval (5492092659 / 1000000000000) (5492105048 / 1000000000000)
      | 5 => orderedInterval (-11955078128 / 1000000000000) (-11955078096 / 1000000000000)
      | 6 => orderedInterval (-7088510187 / 1000000000000) (-7088509506 / 1000000000000)
      | 7 => orderedInterval (-6461859147 / 1000000000000) (-6461859135 / 1000000000000)
      | _ => orderedInterval (2367794338 / 1000000000000) (2367808580 / 1000000000000)
    | _ =>
      match b.val with
      | 0 => orderedInterval (37595867662 / 1000000000000) (37595871630 / 1000000000000)
      | 1 => orderedInterval (7785372400 / 1000000000000) (7785372699 / 1000000000000)
      | 2 => orderedInterval (-18836905255 / 1000000000000) (-18836905149 / 1000000000000)
      | 3 => orderedInterval (-242843762180 / 1000000000000) (-242843759707 / 1000000000000)
      | 4 => orderedInterval (45216369003 / 1000000000000) (45216388066 / 1000000000000)
      | 5 => orderedInterval (20662315395 / 1000000000000) (20662315446 / 1000000000000)
      | 6 => orderedInterval (10158612055 / 1000000000000) (10158612469 / 1000000000000)
      | 7 => orderedInterval (2818049019 / 1000000000000) (2818049031 / 1000000000000)
      | _ => orderedInterval (-38589919872 / 1000000000000) (-38589893267 / 1000000000000)
  coefficientTarget := fun i =>
    match i.val with
    | 0 => orderedInterval (33855829124 / 1000000000000) (33855843812 / 1000000000000)
    | 1 => orderedInterval (-15288680019 / 1000000000000) (-15288663800 / 1000000000000)
    | 2 => orderedInterval (-3019335563 / 1000000000000) (-3019313731 / 1000000000000)
    | 3 => orderedInterval (13748315403 / 1000000000000) (13748348140 / 1000000000000)
    | _ => orderedInterval (-176034001773 / 1000000000000) (-176033948782 / 1000000000000)

theorem compactCertificate214_stateChecks0 :
    compactCertificate214.stateChecks 0 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 30 12 (191 / 2)) (orderedInterval (72958226021 / 1000000000000) (72958235750 / 1000000000000), orderedInterval (-37031907524 / 1000000000000) (-37031897795 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 22 12 (281379471049091 / 4000000000000)) (orderedInterval (85961334525 / 1000000000000) (85961341339 / 1000000000000), orderedInterval (-41360026476 / 1000000000000) (-41360019662 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 36 12 (90992339631203 / 800000000000)) (orderedInterval (74045611559 / 1000000000000) (74045611563 / 1000000000000), orderedInterval (10366746115 / 1000000000000) (10366746120 / 1000000000000))) = true
  norm_num [besselStateAtRationalPoint, besselIntervalStepZero,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, besselZeroTransition,
    besselInitial, besselGridStateAt, besselGridStateBlock00, besselGridStateBlock01,
    besselGridStateBlock02, besselGridStateBlock03, besselGridStateBlock04,
    besselGridStateBlock05, besselGridStateBlock06, besselGridStateBlock07,
    besselGridStateBlock08, besselGridStateBlock09, besselGridStateBlock10,
    besselGridStateBlock11, besselGridStateBlock12, besselGridStateBlock13,
    besselGridStateBlock14, besselGridState007, besselGridState009, besselGridState014, besselGridState017, besselGridState018, besselGridState022, besselGridState024, besselGridState026, besselGridState030, besselGridState031, besselGridState033, besselGridState035, besselGridState036, besselGridState038, besselGridState039, besselGridState044, besselGridState046, besselGridState048, besselGridState053, besselGridState056, besselGridState057, besselGridState060, besselGridState065, besselGridState068, besselGridState070, besselStateSubset, linearInterval, widenInterval,
    rationalErrorInterval, rationalIntervalSubset, orderedInterval, Finset.sum_range_succ,
    IntervalRat.add, IntervalRat.mul, IntervalRat.scale, IntervalRat.singleton]

theorem compactCertificate214_stateChecks1 :
    compactCertificate214.stateChecks 3 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 7 12 (82105827881737 / 4000000000000)) (orderedInterval (111454533145 / 1000000000000) (111454574671 / 1000000000000), orderedInterval (-139074240824 / 1000000000000) (-139074199298 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 18 12 (220547802830389 / 4000000000000)) (orderedInterval (-63181234891 / 1000000000000) (-63181213131 / 1000000000000), orderedInterval (87489137011 / 1000000000000) (87489158771 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 48 12 (598830187342113 / 4000000000000)) (orderedInterval (-19541020742 / 1000000000000) (-19541020364 / 1000000000000), orderedInterval (62279334485 / 1000000000000) (62279334863 / 1000000000000))) = true
  norm_num [besselStateAtRationalPoint, besselIntervalStepZero,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, besselZeroTransition,
    besselInitial, besselGridStateAt, besselGridStateBlock00, besselGridStateBlock01,
    besselGridStateBlock02, besselGridStateBlock03, besselGridStateBlock04,
    besselGridStateBlock05, besselGridStateBlock06, besselGridStateBlock07,
    besselGridStateBlock08, besselGridStateBlock09, besselGridStateBlock10,
    besselGridStateBlock11, besselGridStateBlock12, besselGridStateBlock13,
    besselGridStateBlock14, besselGridState007, besselGridState009, besselGridState014, besselGridState017, besselGridState018, besselGridState022, besselGridState024, besselGridState026, besselGridState030, besselGridState031, besselGridState033, besselGridState035, besselGridState036, besselGridState038, besselGridState039, besselGridState044, besselGridState046, besselGridState048, besselGridState053, besselGridState056, besselGridState057, besselGridState060, besselGridState065, besselGridState068, besselGridState070, besselStateSubset, linearInterval, widenInterval,
    rationalErrorInterval, rationalIntervalSubset, orderedInterval, Finset.sum_range_succ,
    IntervalRat.add, IntervalRat.mul, IntervalRat.scale, IntervalRat.singleton]

theorem compactCertificate214_stateChecks2 :
    compactCertificate214.stateChecks 6 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 35 12 (441095605660969 / 4000000000000)) (orderedInterval (-67797589254 / 1000000000000) (-67797589253 / 1000000000000), orderedInterval (-33993172029 / 1000000000000) (-33993172028 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 60 12 (755824838533837 / 4000000000000)) (orderedInterval (54998024072 / 1000000000000) (54998024073 / 1000000000000), orderedInterval (18411063353 / 1000000000000) (18411063354 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 44 12 (556737155162983 / 4000000000000)) (orderedInterval (66679439312 / 1000000000000) (66679439752 / 1000000000000), orderedInterval (-11542570186 / 1000000000000) (-11542569746 / 1000000000000))) = true
  norm_num [besselStateAtRationalPoint, besselIntervalStepZero,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, besselZeroTransition,
    besselInitial, besselGridStateAt, besselGridStateBlock00, besselGridStateBlock01,
    besselGridStateBlock02, besselGridStateBlock03, besselGridStateBlock04,
    besselGridStateBlock05, besselGridStateBlock06, besselGridStateBlock07,
    besselGridStateBlock08, besselGridStateBlock09, besselGridStateBlock10,
    besselGridStateBlock11, besselGridStateBlock12, besselGridStateBlock13,
    besselGridStateBlock14, besselGridState007, besselGridState009, besselGridState014, besselGridState017, besselGridState018, besselGridState022, besselGridState024, besselGridState026, besselGridState030, besselGridState031, besselGridState033, besselGridState035, besselGridState036, besselGridState038, besselGridState039, besselGridState044, besselGridState046, besselGridState048, besselGridState053, besselGridState056, besselGridState057, besselGridState060, besselGridState065, besselGridState068, besselGridState070, besselStateSubset, linearInterval, widenInterval,
    rationalErrorInterval, rationalIntervalSubset, orderedInterval, Finset.sum_range_succ,
    IntervalRat.add, IntervalRat.mul, IntervalRat.scale, IntervalRat.singleton]

theorem compactCertificate214_stateChecks3 :
    compactCertificate214.stateChecks 9 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 68 12 (854177967404809 / 4000000000000)) (orderedInterval (35216418359 / 1000000000000) (35216418360 / 1000000000000), orderedInterval (41642950967 / 1000000000000) (41642950968 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 39 12 (493159879416961 / 4000000000000)) (orderedInterval (-71845510045 / 1000000000000) (-71845510015 / 1000000000000), orderedInterval (-1041939789 / 1000000000000) (-1041939760 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 70 12 (875120860154549 / 4000000000000)) (orderedInterval (-18316638779 / 1000000000000) (-18316638363 / 1000000000000), orderedInterval (50780075643 / 1000000000000) (50780076059 / 1000000000000))) = true
  norm_num [besselStateAtRationalPoint, besselIntervalStepZero,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, besselZeroTransition,
    besselInitial, besselGridStateAt, besselGridStateBlock00, besselGridStateBlock01,
    besselGridStateBlock02, besselGridStateBlock03, besselGridStateBlock04,
    besselGridStateBlock05, besselGridStateBlock06, besselGridStateBlock07,
    besselGridStateBlock08, besselGridStateBlock09, besselGridStateBlock10,
    besselGridStateBlock11, besselGridStateBlock12, besselGridStateBlock13,
    besselGridStateBlock14, besselGridState007, besselGridState009, besselGridState014, besselGridState017, besselGridState018, besselGridState022, besselGridState024, besselGridState026, besselGridState030, besselGridState031, besselGridState033, besselGridState035, besselGridState036, besselGridState038, besselGridState039, besselGridState044, besselGridState046, besselGridState048, besselGridState053, besselGridState056, besselGridState057, besselGridState060, besselGridState065, besselGridState068, besselGridState070, besselStateSubset, linearInterval, widenInterval,
    rationalErrorInterval, rationalIntervalSubset, orderedInterval, Finset.sum_range_succ,
    IntervalRat.add, IntervalRat.mul, IntervalRat.scale, IntervalRat.singleton]

theorem compactCertificate214_stateChecks4 :
    compactCertificate214.stateChecks 12 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 65 12 (817651425248681 / 4000000000000)) (orderedInterval (-46781515023 / 1000000000000) (-46781515022 / 1000000000000), orderedInterval (-30313656252 / 1000000000000) (-30313656251 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 46 12 (583514638490873 / 4000000000000)) (orderedInterval (55288277422 / 1000000000000) (55288313748 / 1000000000000), orderedInterval (-36345156675 / 1000000000000) (-36345120349 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 53 12 (661643408491167 / 4000000000000)) (orderedInterval (18861143522 / 1000000000000) (18861143884 / 1000000000000), orderedInterval (-59158534500 / 1000000000000) (-59158534137 / 1000000000000))) = true
  norm_num [besselStateAtRationalPoint, besselIntervalStepZero,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, besselZeroTransition,
    besselInitial, besselGridStateAt, besselGridStateBlock00, besselGridStateBlock01,
    besselGridStateBlock02, besselGridStateBlock03, besselGridStateBlock04,
    besselGridStateBlock05, besselGridStateBlock06, besselGridStateBlock07,
    besselGridStateBlock08, besselGridStateBlock09, besselGridStateBlock10,
    besselGridStateBlock11, besselGridStateBlock12, besselGridStateBlock13,
    besselGridStateBlock14, besselGridState007, besselGridState009, besselGridState014, besselGridState017, besselGridState018, besselGridState022, besselGridState024, besselGridState026, besselGridState030, besselGridState031, besselGridState033, besselGridState035, besselGridState036, besselGridState038, besselGridState039, besselGridState044, besselGridState046, besselGridState048, besselGridState053, besselGridState056, besselGridState057, besselGridState060, besselGridState065, besselGridState068, besselGridState070, besselStateSubset, linearInterval, widenInterval,
    rationalErrorInterval, rationalIntervalSubset, orderedInterval, Finset.sum_range_succ,
    IntervalRat.add, IntervalRat.mul, IntervalRat.scale, IntervalRat.singleton]

theorem compactCertificate214_stateChecks5 :
    compactCertificate214.stateChecks 15 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 44 12 (551609294207023 / 4000000000000)) (orderedInterval (29965007543 / 1000000000000) (29965007544 / 1000000000000), orderedInterval (60871443770 / 1000000000000) (60871443771 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 39 12 (487363540063483 / 4000000000000)) (orderedInterval (-7442425604 / 1000000000000) (-7442425603 / 1000000000000), orderedInterval (-71869825995 / 1000000000000) (-71869825994 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 56 12 (141256949816817 / 800000000000)) (orderedInterval (59422934136 / 1000000000000) (59422934142 / 1000000000000), orderedInterval (8454826416 / 1000000000000) (8454826422 / 1000000000000))) = true
  norm_num [besselStateAtRationalPoint, besselIntervalStepZero,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, besselZeroTransition,
    besselInitial, besselGridStateAt, besselGridStateBlock00, besselGridStateBlock01,
    besselGridStateBlock02, besselGridStateBlock03, besselGridStateBlock04,
    besselGridStateBlock05, besselGridStateBlock06, besselGridStateBlock07,
    besselGridStateBlock08, besselGridStateBlock09, besselGridStateBlock10,
    besselGridStateBlock11, besselGridStateBlock12, besselGridStateBlock13,
    besselGridStateBlock14, besselGridState007, besselGridState009, besselGridState014, besselGridState017, besselGridState018, besselGridState022, besselGridState024, besselGridState026, besselGridState030, besselGridState031, besselGridState033, besselGridState035, besselGridState036, besselGridState038, besselGridState039, besselGridState044, besselGridState046, besselGridState048, besselGridState053, besselGridState056, besselGridState057, besselGridState060, besselGridState065, besselGridState068, besselGridState070, besselStateSubset, linearInterval, widenInterval,
    rationalErrorInterval, rationalIntervalSubset, orderedInterval, Finset.sum_range_succ,
    IntervalRat.add, IntervalRat.mul, IntervalRat.scale, IntervalRat.singleton]

theorem compactCertificate214_stateChecks6 :
    compactCertificate214.stateChecks 18 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 31 12 (390724157139299 / 4000000000000)) (orderedInterval (-71038992234 / 1000000000000) (-71038992233 / 1000000000000), orderedInterval (-37986699522 / 1000000000000) (-37986699521 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 26 12 (331221195158539 / 4000000000000)) (orderedInterval (82749830908 / 1000000000000) (82749833255 / 1000000000000), orderedInterval (-29491170600 / 1000000000000) (-29491168252 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 17 12 (207262844837017 / 4000000000000)) (orderedInterval (80156341471 / 1000000000000) (80156449334 / 1000000000000), orderedInterval (-77331639974 / 1000000000000) (-77331532110 / 1000000000000))) = true
  norm_num [besselStateAtRationalPoint, besselIntervalStepZero,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, besselZeroTransition,
    besselInitial, besselGridStateAt, besselGridStateBlock00, besselGridStateBlock01,
    besselGridStateBlock02, besselGridStateBlock03, besselGridStateBlock04,
    besselGridStateBlock05, besselGridStateBlock06, besselGridStateBlock07,
    besselGridStateBlock08, besselGridStateBlock09, besselGridStateBlock10,
    besselGridStateBlock11, besselGridStateBlock12, besselGridStateBlock13,
    besselGridStateBlock14, besselGridState007, besselGridState009, besselGridState014, besselGridState017, besselGridState018, besselGridState022, besselGridState024, besselGridState026, besselGridState030, besselGridState031, besselGridState033, besselGridState035, besselGridState036, besselGridState038, besselGridState039, besselGridState044, besselGridState046, besselGridState048, besselGridState053, besselGridState056, besselGridState057, besselGridState060, besselGridState065, besselGridState068, besselGridState070, besselStateSubset, linearInterval, widenInterval,
    rationalErrorInterval, rationalIntervalSubset, orderedInterval, Finset.sum_range_succ,
    IntervalRat.add, IntervalRat.mul, IntervalRat.scale, IntervalRat.singleton]

theorem compactCertificate214_stateChecks7 :
    compactCertificate214.stateChecks 21 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 9 12 (111466647278439 / 4000000000000)) (orderedInterval (-55109188431 / 1000000000000) (-55109188430 / 1000000000000), orderedInterval (-139762652794 / 1000000000000) (-139762652793 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 24 12 (302653630712317 / 4000000000000)) (orderedInterval (79516378746 / 1000000000000) (79516378747 / 1000000000000), orderedInterval (45200841736 / 1000000000000) (45200841737 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 33 12 (413247658082909 / 4000000000000)) (orderedInterval (-32262562731 / 1000000000000) (-32262562730 / 1000000000000), orderedInterval (-71407041255 / 1000000000000) (-71407041254 / 1000000000000))) = true
  norm_num [besselStateAtRationalPoint, besselIntervalStepZero,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, besselZeroTransition,
    besselInitial, besselGridStateAt, besselGridStateBlock00, besselGridStateBlock01,
    besselGridStateBlock02, besselGridStateBlock03, besselGridStateBlock04,
    besselGridStateBlock05, besselGridStateBlock06, besselGridStateBlock07,
    besselGridStateBlock08, besselGridStateBlock09, besselGridStateBlock10,
    besselGridStateBlock11, besselGridStateBlock12, besselGridStateBlock13,
    besselGridStateBlock14, besselGridState007, besselGridState009, besselGridState014, besselGridState017, besselGridState018, besselGridState022, besselGridState024, besselGridState026, besselGridState030, besselGridState031, besselGridState033, besselGridState035, besselGridState036, besselGridState038, besselGridState039, besselGridState044, besselGridState046, besselGridState048, besselGridState053, besselGridState056, besselGridState057, besselGridState060, besselGridState065, besselGridState068, besselGridState070, besselStateSubset, linearInterval, widenInterval,
    rationalErrorInterval, rationalIntervalSubset, orderedInterval, Finset.sum_range_succ,
    IntervalRat.add, IntervalRat.mul, IntervalRat.scale, IntervalRat.singleton]

theorem compactCertificate214_stateChecks8 :
    compactCertificate214.stateChecks 24 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 14 12 (174737155162983 / 4000000000000)) (orderedInterval (56228307256 / 1000000000000) (56228307257 / 1000000000000), orderedInterval (106184009444 / 1000000000000) (106184009445 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 57 12 (710296834620743 / 4000000000000)) (orderedInterval (39114090341 / 1000000000000) (39114117240 / 1000000000000), orderedInterval (-45444243507 / 1000000000000) (-45444216608 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 38 12 (474445367484937 / 4000000000000)) (orderedInterval (1110993534 / 1000000000000) (1110993539 / 1000000000000), orderedInterval (73248910850 / 1000000000000) (73248910855 / 1000000000000))) = true
  norm_num [besselStateAtRationalPoint, besselIntervalStepZero,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, besselZeroTransition,
    besselInitial, besselGridStateAt, besselGridStateBlock00, besselGridStateBlock01,
    besselGridStateBlock02, besselGridStateBlock03, besselGridStateBlock04,
    besselGridStateBlock05, besselGridStateBlock06, besselGridStateBlock07,
    besselGridStateBlock08, besselGridStateBlock09, besselGridStateBlock10,
    besselGridStateBlock11, besselGridStateBlock12, besselGridStateBlock13,
    besselGridStateBlock14, besselGridState007, besselGridState009, besselGridState014, besselGridState017, besselGridState018, besselGridState022, besselGridState024, besselGridState026, besselGridState030, besselGridState031, besselGridState033, besselGridState035, besselGridState036, besselGridState038, besselGridState039, besselGridState044, besselGridState046, besselGridState048, besselGridState053, besselGridState056, besselGridState057, besselGridState060, besselGridState065, besselGridState068, besselGridState070, besselStateSubset, linearInterval, widenInterval,
    rationalErrorInterval, rationalIntervalSubset, orderedInterval, Finset.sum_range_succ,
    IntervalRat.add, IntervalRat.mul, IntervalRat.scale, IntervalRat.singleton]

theorem compactCertificate214_states : ∀ j,
    BesselStateValid (compactCertificate214.point j) (compactCertificate214.state j) :=
  compactCertificate214.statesValid_of_checks3 compactCertificate214_stateChecks0
    compactCertificate214_stateChecks1 compactCertificate214_stateChecks2
    compactCertificate214_stateChecks3 compactCertificate214_stateChecks4
    compactCertificate214_stateChecks5 compactCertificate214_stateChecks6
    compactCertificate214_stateChecks7 compactCertificate214_stateChecks8

theorem compactCertificate214_chunkChecks0_0 :
    compactCertificate214.chunkChecks (0 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 0) <| besselDerivativeNearFromState (191 / 2) 0 (IntervalRat.scale (191 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (72958226021 / 1000000000000) (72958235750 / 1000000000000), orderedInterval (-37031907524 / 1000000000000) (-37031897795 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 0) <| besselDerivativeNearFromState (281379471049091 / 4000000000000) 0 (IntervalRat.scale (191 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (85961334525 / 1000000000000) (85961341339 / 1000000000000), orderedInterval (-41360026476 / 1000000000000) (-41360019662 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 0) <| besselDerivativeNearFromState (90992339631203 / 800000000000) 0 (IntervalRat.scale (191 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (74045611559 / 1000000000000) (74045611563 / 1000000000000), orderedInterval (10366746115 / 1000000000000) (10366746120 / 1000000000000)))) (orderedInterval (34064160513 / 1000000000000) (34064164441 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 0) <| besselDerivativeNearFromState (82105827881737 / 4000000000000) 0 (IntervalRat.scale (191 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (111454533145 / 1000000000000) (111454574671 / 1000000000000), orderedInterval (-139074240824 / 1000000000000) (-139074199298 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 0) <| besselDerivativeNearFromState (220547802830389 / 4000000000000) 0 (IntervalRat.scale (191 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-63181234891 / 1000000000000) (-63181213131 / 1000000000000), orderedInterval (87489137011 / 1000000000000) (87489158771 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 0) <| besselDerivativeNearFromState (598830187342113 / 4000000000000) 0 (IntervalRat.scale (191 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-19541020742 / 1000000000000) (-19541020364 / 1000000000000), orderedInterval (62279334485 / 1000000000000) (62279334863 / 1000000000000)))) (orderedInterval (-2126896198 / 1000000000000) (-2126894914 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 0) <| besselDerivativeNearFromState (441095605660969 / 4000000000000) 0 (IntervalRat.scale (191 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-67797589254 / 1000000000000) (-67797589253 / 1000000000000), orderedInterval (-33993172029 / 1000000000000) (-33993172028 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 0) <| besselDerivativeNearFromState (755824838533837 / 4000000000000) 0 (IntervalRat.scale (191 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (54998024072 / 1000000000000) (54998024073 / 1000000000000), orderedInterval (18411063353 / 1000000000000) (18411063354 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 0) <| besselDerivativeNearFromState (556737155162983 / 4000000000000) 0 (IntervalRat.scale (191 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (66679439312 / 1000000000000) (66679439752 / 1000000000000), orderedInterval (-11542570186 / 1000000000000) (-11542569746 / 1000000000000)))) (orderedInterval (-84848623 / 1000000000000) (-84848606 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate214_chunkChecks0_1 :
    compactCertificate214.chunkChecks (0 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 0) <| besselDerivativeNearFromState (854177967404809 / 4000000000000) 0 (IntervalRat.scale (191 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (35216418359 / 1000000000000) (35216418360 / 1000000000000), orderedInterval (41642950967 / 1000000000000) (41642950968 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 0) <| besselDerivativeNearFromState (493159879416961 / 4000000000000) 0 (IntervalRat.scale (191 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-71845510045 / 1000000000000) (-71845510015 / 1000000000000), orderedInterval (-1041939789 / 1000000000000) (-1041939760 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 0) <| besselDerivativeNearFromState (875120860154549 / 4000000000000) 0 (IntervalRat.scale (191 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-18316638779 / 1000000000000) (-18316638363 / 1000000000000), orderedInterval (50780075643 / 1000000000000) (50780076059 / 1000000000000)))) (orderedInterval (-14184511561 / 1000000000000) (-14184511460 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 0) <| besselDerivativeNearFromState (817651425248681 / 4000000000000) 0 (IntervalRat.scale (191 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-46781515023 / 1000000000000) (-46781515022 / 1000000000000), orderedInterval (-30313656252 / 1000000000000) (-30313656251 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 0) <| besselDerivativeNearFromState (583514638490873 / 4000000000000) 0 (IntervalRat.scale (191 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (55288277422 / 1000000000000) (55288313748 / 1000000000000), orderedInterval (-36345156675 / 1000000000000) (-36345120349 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 0) <| besselDerivativeNearFromState (661643408491167 / 4000000000000) 0 (IntervalRat.scale (191 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (18861143522 / 1000000000000) (18861143884 / 1000000000000), orderedInterval (-59158534500 / 1000000000000) (-59158534137 / 1000000000000)))) (orderedInterval (5977320425 / 1000000000000) (5977323874 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 0) <| besselDerivativeNearFromState (551609294207023 / 4000000000000) 0 (IntervalRat.scale (191 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (29965007543 / 1000000000000) (29965007544 / 1000000000000), orderedInterval (60871443770 / 1000000000000) (60871443771 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 0) <| besselDerivativeNearFromState (487363540063483 / 4000000000000) 0 (IntervalRat.scale (191 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-7442425604 / 1000000000000) (-7442425603 / 1000000000000), orderedInterval (-71869825995 / 1000000000000) (-71869825994 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 0) <| besselDerivativeNearFromState (141256949816817 / 800000000000) 0 (IntervalRat.scale (191 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (59422934136 / 1000000000000) (59422934142 / 1000000000000), orderedInterval (8454826416 / 1000000000000) (8454826422 / 1000000000000)))) (orderedInterval (2293393134 / 1000000000000) (2293393144 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate214_chunkChecks0_2 :
    compactCertificate214.chunkChecks (0 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 0) <| besselDerivativeNearFromState (390724157139299 / 4000000000000) 0 (IntervalRat.scale (191 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-71038992234 / 1000000000000) (-71038992233 / 1000000000000), orderedInterval (-37986699522 / 1000000000000) (-37986699521 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 0) <| besselDerivativeNearFromState (331221195158539 / 4000000000000) 0 (IntervalRat.scale (191 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (82749830908 / 1000000000000) (82749833255 / 1000000000000), orderedInterval (-29491170600 / 1000000000000) (-29491168252 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 0) <| besselDerivativeNearFromState (207262844837017 / 4000000000000) 0 (IntervalRat.scale (191 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (80156341471 / 1000000000000) (80156449334 / 1000000000000), orderedInterval (-77331639974 / 1000000000000) (-77331532110 / 1000000000000)))) (orderedInterval (9284472431 / 1000000000000) (9284476100 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 0) <| besselDerivativeNearFromState (111466647278439 / 4000000000000) 0 (IntervalRat.scale (191 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-55109188431 / 1000000000000) (-55109188430 / 1000000000000), orderedInterval (-139762652794 / 1000000000000) (-139762652793 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 0) <| besselDerivativeNearFromState (302653630712317 / 4000000000000) 0 (IntervalRat.scale (191 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (79516378746 / 1000000000000) (79516378747 / 1000000000000), orderedInterval (45200841736 / 1000000000000) (45200841737 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 0) <| besselDerivativeNearFromState (413247658082909 / 4000000000000) 0 (IntervalRat.scale (191 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-32262562731 / 1000000000000) (-32262562730 / 1000000000000), orderedInterval (-71407041255 / 1000000000000) (-71407041254 / 1000000000000)))) (orderedInterval (1686186846 / 1000000000000) (1686186858 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 0) <| besselDerivativeNearFromState (174737155162983 / 4000000000000) 0 (IntervalRat.scale (191 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (56228307256 / 1000000000000) (56228307257 / 1000000000000), orderedInterval (106184009444 / 1000000000000) (106184009445 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 0) <| besselDerivativeNearFromState (710296834620743 / 4000000000000) 0 (IntervalRat.scale (191 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (39114090341 / 1000000000000) (39114117240 / 1000000000000), orderedInterval (-45444243507 / 1000000000000) (-45444216608 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 0) <| besselDerivativeNearFromState (474445367484937 / 4000000000000) 0 (IntervalRat.scale (191 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (1110993534 / 1000000000000) (1110993539 / 1000000000000), orderedInterval (73248910850 / 1000000000000) (73248910855 / 1000000000000)))) (orderedInterval (-3053447843 / 1000000000000) (-3053445625 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate214_chunkChecks0 :
    compactCertificate214.chunkChecks (0 : Fin 5) 0 9 = true :=
  compactCertificate214.chunkChecks_nine_of_three (0 : Fin 5) compactCertificate214_chunkChecks0_0
    compactCertificate214_chunkChecks0_1 compactCertificate214_chunkChecks0_2

theorem compactCertificate214_chunkChecks1_0 :
    compactCertificate214.chunkChecks (1 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 1) <| besselDerivativeNearFromState (191 / 2) 1 (IntervalRat.scale (191 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (72958226021 / 1000000000000) (72958235750 / 1000000000000), orderedInterval (-37031907524 / 1000000000000) (-37031897795 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 1) <| besselDerivativeNearFromState (281379471049091 / 4000000000000) 1 (IntervalRat.scale (191 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (85961334525 / 1000000000000) (85961341339 / 1000000000000), orderedInterval (-41360026476 / 1000000000000) (-41360019662 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 1) <| besselDerivativeNearFromState (90992339631203 / 800000000000) 1 (IntervalRat.scale (191 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (74045611559 / 1000000000000) (74045611563 / 1000000000000), orderedInterval (10366746115 / 1000000000000) (10366746120 / 1000000000000)))) (orderedInterval (-14237508634 / 1000000000000) (-14237504722 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 1) <| besselDerivativeNearFromState (82105827881737 / 4000000000000) 1 (IntervalRat.scale (191 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (111454533145 / 1000000000000) (111454574671 / 1000000000000), orderedInterval (-139074240824 / 1000000000000) (-139074199298 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 1) <| besselDerivativeNearFromState (220547802830389 / 4000000000000) 1 (IntervalRat.scale (191 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-63181234891 / 1000000000000) (-63181213131 / 1000000000000), orderedInterval (87489137011 / 1000000000000) (87489158771 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 1) <| besselDerivativeNearFromState (598830187342113 / 4000000000000) 1 (IntervalRat.scale (191 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-19541020742 / 1000000000000) (-19541020364 / 1000000000000), orderedInterval (62279334485 / 1000000000000) (62279334863 / 1000000000000)))) (orderedInterval (-4771912141 / 1000000000000) (-4771911529 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 1) <| besselDerivativeNearFromState (441095605660969 / 4000000000000) 1 (IntervalRat.scale (191 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-67797589254 / 1000000000000) (-67797589253 / 1000000000000), orderedInterval (-33993172029 / 1000000000000) (-33993172028 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 1) <| besselDerivativeNearFromState (755824838533837 / 4000000000000) 1 (IntervalRat.scale (191 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (54998024072 / 1000000000000) (54998024073 / 1000000000000), orderedInterval (18411063353 / 1000000000000) (18411063354 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 1) <| besselDerivativeNearFromState (556737155162983 / 4000000000000) 1 (IntervalRat.scale (191 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (66679439312 / 1000000000000) (66679439752 / 1000000000000), orderedInterval (-11542570186 / 1000000000000) (-11542569746 / 1000000000000)))) (orderedInterval (-1530154283 / 1000000000000) (-1530154258 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate214_chunkChecks1_1 :
    compactCertificate214.chunkChecks (1 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 1) <| besselDerivativeNearFromState (854177967404809 / 4000000000000) 1 (IntervalRat.scale (191 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (35216418359 / 1000000000000) (35216418360 / 1000000000000), orderedInterval (41642950967 / 1000000000000) (41642950968 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 1) <| besselDerivativeNearFromState (493159879416961 / 4000000000000) 1 (IntervalRat.scale (191 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-71845510045 / 1000000000000) (-71845510015 / 1000000000000), orderedInterval (-1041939789 / 1000000000000) (-1041939760 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 1) <| besselDerivativeNearFromState (875120860154549 / 4000000000000) 1 (IntervalRat.scale (191 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-18316638779 / 1000000000000) (-18316638363 / 1000000000000), orderedInterval (50780075643 / 1000000000000) (50780076059 / 1000000000000)))) (orderedInterval (-108101635 / 1000000000000) (-108101417 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 1) <| besselDerivativeNearFromState (817651425248681 / 4000000000000) 1 (IntervalRat.scale (191 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-46781515023 / 1000000000000) (-46781515022 / 1000000000000), orderedInterval (-30313656252 / 1000000000000) (-30313656251 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 1) <| besselDerivativeNearFromState (583514638490873 / 4000000000000) 1 (IntervalRat.scale (191 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (55288277422 / 1000000000000) (55288313748 / 1000000000000), orderedInterval (-36345156675 / 1000000000000) (-36345120349 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 1) <| besselDerivativeNearFromState (661643408491167 / 4000000000000) 1 (IntervalRat.scale (191 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (18861143522 / 1000000000000) (18861143884 / 1000000000000), orderedInterval (-59158534500 / 1000000000000) (-59158534137 / 1000000000000)))) (orderedInterval (-3560048542 / 1000000000000) (-3560043272 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 1) <| besselDerivativeNearFromState (551609294207023 / 4000000000000) 1 (IntervalRat.scale (191 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (29965007543 / 1000000000000) (29965007544 / 1000000000000), orderedInterval (60871443770 / 1000000000000) (60871443771 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 1) <| besselDerivativeNearFromState (487363540063483 / 4000000000000) 1 (IntervalRat.scale (191 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-7442425604 / 1000000000000) (-7442425603 / 1000000000000), orderedInterval (-71869825995 / 1000000000000) (-71869825994 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 1) <| besselDerivativeNearFromState (141256949816817 / 800000000000) 1 (IntervalRat.scale (191 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (59422934136 / 1000000000000) (59422934142 / 1000000000000), orderedInterval (8454826416 / 1000000000000) (8454826422 / 1000000000000)))) (orderedInterval (6662557443 / 1000000000000) (6662557458 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate214_chunkChecks1_2 :
    compactCertificate214.chunkChecks (1 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 1) <| besselDerivativeNearFromState (390724157139299 / 4000000000000) 1 (IntervalRat.scale (191 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-71038992234 / 1000000000000) (-71038992233 / 1000000000000), orderedInterval (-37986699522 / 1000000000000) (-37986699521 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 1) <| besselDerivativeNearFromState (331221195158539 / 4000000000000) 1 (IntervalRat.scale (191 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (82749830908 / 1000000000000) (82749833255 / 1000000000000), orderedInterval (-29491170600 / 1000000000000) (-29491168252 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 1) <| besselDerivativeNearFromState (207262844837017 / 4000000000000) 1 (IntervalRat.scale (191 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (80156341471 / 1000000000000) (80156449334 / 1000000000000), orderedInterval (-77331639974 / 1000000000000) (-77331532110 / 1000000000000)))) (orderedInterval (6293858396 / 1000000000000) (6293860440 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 1) <| besselDerivativeNearFromState (111466647278439 / 4000000000000) 1 (IntervalRat.scale (191 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-55109188431 / 1000000000000) (-55109188430 / 1000000000000), orderedInterval (-139762652794 / 1000000000000) (-139762652793 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 1) <| besselDerivativeNearFromState (302653630712317 / 4000000000000) 1 (IntervalRat.scale (191 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (79516378746 / 1000000000000) (79516378747 / 1000000000000), orderedInterval (45200841736 / 1000000000000) (45200841737 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 1) <| besselDerivativeNearFromState (413247658082909 / 4000000000000) 1 (IntervalRat.scale (191 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-32262562731 / 1000000000000) (-32262562730 / 1000000000000), orderedInterval (-71407041255 / 1000000000000) (-71407041254 / 1000000000000)))) (orderedInterval (5860799656 / 1000000000000) (5860799668 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 1) <| besselDerivativeNearFromState (174737155162983 / 4000000000000) 1 (IntervalRat.scale (191 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (56228307256 / 1000000000000) (56228307257 / 1000000000000), orderedInterval (106184009444 / 1000000000000) (106184009445 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 1) <| besselDerivativeNearFromState (710296834620743 / 4000000000000) 1 (IntervalRat.scale (191 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (39114090341 / 1000000000000) (39114117240 / 1000000000000), orderedInterval (-45444243507 / 1000000000000) (-45444216608 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 1) <| besselDerivativeNearFromState (474445367484937 / 4000000000000) 1 (IntervalRat.scale (191 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (1110993534 / 1000000000000) (1110993539 / 1000000000000), orderedInterval (73248910850 / 1000000000000) (73248910855 / 1000000000000)))) (orderedInterval (-9898170279 / 1000000000000) (-9898166168 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate214_chunkChecks1 :
    compactCertificate214.chunkChecks (1 : Fin 5) 0 9 = true :=
  compactCertificate214.chunkChecks_nine_of_three (1 : Fin 5) compactCertificate214_chunkChecks1_0
    compactCertificate214_chunkChecks1_1 compactCertificate214_chunkChecks1_2

theorem compactCertificate214_chunkChecks2_0 :
    compactCertificate214.chunkChecks (2 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 2) <| besselDerivativeNearFromState (191 / 2) 2 (IntervalRat.scale (191 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (72958226021 / 1000000000000) (72958235750 / 1000000000000), orderedInterval (-37031907524 / 1000000000000) (-37031897795 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 2) <| besselDerivativeNearFromState (281379471049091 / 4000000000000) 2 (IntervalRat.scale (191 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (85961334525 / 1000000000000) (85961341339 / 1000000000000), orderedInterval (-41360026476 / 1000000000000) (-41360019662 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 2) <| besselDerivativeNearFromState (90992339631203 / 800000000000) 2 (IntervalRat.scale (191 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (74045611559 / 1000000000000) (74045611563 / 1000000000000), orderedInterval (10366746115 / 1000000000000) (10366746120 / 1000000000000)))) (orderedInterval (-35367010362 / 1000000000000) (-35367006420 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 2) <| besselDerivativeNearFromState (82105827881737 / 4000000000000) 2 (IntervalRat.scale (191 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (111454533145 / 1000000000000) (111454574671 / 1000000000000), orderedInterval (-139074240824 / 1000000000000) (-139074199298 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 2) <| besselDerivativeNearFromState (220547802830389 / 4000000000000) 2 (IntervalRat.scale (191 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-63181234891 / 1000000000000) (-63181213131 / 1000000000000), orderedInterval (87489137011 / 1000000000000) (87489158771 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 2) <| besselDerivativeNearFromState (598830187342113 / 4000000000000) 2 (IntervalRat.scale (191 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-19541020742 / 1000000000000) (-19541020364 / 1000000000000), orderedInterval (62279334485 / 1000000000000) (62279334863 / 1000000000000)))) (orderedInterval (-2538987356 / 1000000000000) (-2538986979 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 2) <| besselDerivativeNearFromState (441095605660969 / 4000000000000) 2 (IntervalRat.scale (191 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-67797589254 / 1000000000000) (-67797589253 / 1000000000000), orderedInterval (-33993172029 / 1000000000000) (-33993172028 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 2) <| besselDerivativeNearFromState (755824838533837 / 4000000000000) 2 (IntervalRat.scale (191 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (54998024072 / 1000000000000) (54998024073 / 1000000000000), orderedInterval (18411063353 / 1000000000000) (18411063354 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 2) <| besselDerivativeNearFromState (556737155162983 / 4000000000000) 2 (IntervalRat.scale (191 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (66679439312 / 1000000000000) (66679439752 / 1000000000000), orderedInterval (-11542570186 / 1000000000000) (-11542569746 / 1000000000000)))) (orderedInterval (3234021739 / 1000000000000) (3234021779 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate214_chunkChecks2_1 :
    compactCertificate214.chunkChecks (2 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 2) <| besselDerivativeNearFromState (854177967404809 / 4000000000000) 2 (IntervalRat.scale (191 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (35216418359 / 1000000000000) (35216418360 / 1000000000000), orderedInterval (41642950967 / 1000000000000) (41642950968 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 2) <| besselDerivativeNearFromState (493159879416961 / 4000000000000) 2 (IntervalRat.scale (191 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-71845510045 / 1000000000000) (-71845510015 / 1000000000000), orderedInterval (-1041939789 / 1000000000000) (-1041939760 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 2) <| besselDerivativeNearFromState (875120860154549 / 4000000000000) 2 (IntervalRat.scale (191 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-18316638779 / 1000000000000) (-18316638363 / 1000000000000), orderedInterval (50780075643 / 1000000000000) (50780076059 / 1000000000000)))) (orderedInterval (53826054238 / 1000000000000) (53826054724 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 2) <| besselDerivativeNearFromState (817651425248681 / 4000000000000) 2 (IntervalRat.scale (191 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-46781515023 / 1000000000000) (-46781515022 / 1000000000000), orderedInterval (-30313656252 / 1000000000000) (-30313656251 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 2) <| besselDerivativeNearFromState (583514638490873 / 4000000000000) 2 (IntervalRat.scale (191 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (55288277422 / 1000000000000) (55288313748 / 1000000000000), orderedInterval (-36345156675 / 1000000000000) (-36345120349 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 2) <| besselDerivativeNearFromState (661643408491167 / 4000000000000) 2 (IntervalRat.scale (191 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (18861143522 / 1000000000000) (18861143884 / 1000000000000), orderedInterval (-59158534500 / 1000000000000) (-59158534137 / 1000000000000)))) (orderedInterval (-15744887333 / 1000000000000) (-15744879226 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 2) <| besselDerivativeNearFromState (551609294207023 / 4000000000000) 2 (IntervalRat.scale (191 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (29965007543 / 1000000000000) (29965007544 / 1000000000000), orderedInterval (60871443770 / 1000000000000) (60871443771 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 2) <| besselDerivativeNearFromState (487363540063483 / 4000000000000) 2 (IntervalRat.scale (191 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-7442425604 / 1000000000000) (-7442425603 / 1000000000000), orderedInterval (-71869825995 / 1000000000000) (-71869825994 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 2) <| besselDerivativeNearFromState (141256949816817 / 800000000000) 2 (IntervalRat.scale (191 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (59422934136 / 1000000000000) (59422934142 / 1000000000000), orderedInterval (8454826416 / 1000000000000) (8454826422 / 1000000000000)))) (orderedInterval (-6685619203 / 1000000000000) (-6685619182 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate214_chunkChecks2_2 :
    compactCertificate214.chunkChecks (2 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 2) <| besselDerivativeNearFromState (390724157139299 / 4000000000000) 2 (IntervalRat.scale (191 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-71038992234 / 1000000000000) (-71038992233 / 1000000000000), orderedInterval (-37986699522 / 1000000000000) (-37986699521 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 2) <| besselDerivativeNearFromState (331221195158539 / 4000000000000) 2 (IntervalRat.scale (191 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (82749830908 / 1000000000000) (82749833255 / 1000000000000), orderedInterval (-29491170600 / 1000000000000) (-29491168252 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 2) <| besselDerivativeNearFromState (207262844837017 / 4000000000000) 2 (IntervalRat.scale (191 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (80156341471 / 1000000000000) (80156449334 / 1000000000000), orderedInterval (-77331639974 / 1000000000000) (-77331532110 / 1000000000000)))) (orderedInterval (-9196230923 / 1000000000000) (-9196229746 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 2) <| besselDerivativeNearFromState (111466647278439 / 4000000000000) 2 (IntervalRat.scale (191 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-55109188431 / 1000000000000) (-55109188430 / 1000000000000), orderedInterval (-139762652794 / 1000000000000) (-139762652793 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 2) <| besselDerivativeNearFromState (302653630712317 / 4000000000000) 2 (IntervalRat.scale (191 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (79516378746 / 1000000000000) (79516378747 / 1000000000000), orderedInterval (45200841736 / 1000000000000) (45200841737 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 2) <| besselDerivativeNearFromState (413247658082909 / 4000000000000) 2 (IntervalRat.scale (191 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-32262562731 / 1000000000000) (-32262562730 / 1000000000000), orderedInterval (-71407041255 / 1000000000000) (-71407041254 / 1000000000000)))) (orderedInterval (-1909247212 / 1000000000000) (-1909247200 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 2) <| besselDerivativeNearFromState (174737155162983 / 4000000000000) 2 (IntervalRat.scale (191 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (56228307256 / 1000000000000) (56228307257 / 1000000000000), orderedInterval (106184009444 / 1000000000000) (106184009445 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 2) <| besselDerivativeNearFromState (710296834620743 / 4000000000000) 2 (IntervalRat.scale (191 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (39114090341 / 1000000000000) (39114117240 / 1000000000000), orderedInterval (-45444243507 / 1000000000000) (-45444216608 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 2) <| besselDerivativeNearFromState (474445367484937 / 4000000000000) 2 (IntervalRat.scale (191 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (1110993534 / 1000000000000) (1110993539 / 1000000000000), orderedInterval (73248910850 / 1000000000000) (73248910855 / 1000000000000)))) (orderedInterval (11362570849 / 1000000000000) (11362578519 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate214_chunkChecks2 :
    compactCertificate214.chunkChecks (2 : Fin 5) 0 9 = true :=
  compactCertificate214.chunkChecks_nine_of_three (2 : Fin 5) compactCertificate214_chunkChecks2_0
    compactCertificate214_chunkChecks2_1 compactCertificate214_chunkChecks2_2

theorem compactCertificate214_chunkChecks3_0 :
    compactCertificate214.chunkChecks (3 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 3) <| besselDerivativeNearFromState (191 / 2) 3 (IntervalRat.scale (191 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (72958226021 / 1000000000000) (72958235750 / 1000000000000), orderedInterval (-37031907524 / 1000000000000) (-37031897795 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 3) <| besselDerivativeNearFromState (281379471049091 / 4000000000000) 3 (IntervalRat.scale (191 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (85961334525 / 1000000000000) (85961341339 / 1000000000000), orderedInterval (-41360026476 / 1000000000000) (-41360019662 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 3) <| besselDerivativeNearFromState (90992339631203 / 800000000000) 3 (IntervalRat.scale (191 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (74045611559 / 1000000000000) (74045611563 / 1000000000000), orderedInterval (10366746115 / 1000000000000) (10366746120 / 1000000000000)))) (orderedInterval (14173226270 / 1000000000000) (14173230203 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 3) <| besselDerivativeNearFromState (82105827881737 / 4000000000000) 3 (IntervalRat.scale (191 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (111454533145 / 1000000000000) (111454574671 / 1000000000000), orderedInterval (-139074240824 / 1000000000000) (-139074199298 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 3) <| besselDerivativeNearFromState (220547802830389 / 4000000000000) 3 (IntervalRat.scale (191 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-63181234891 / 1000000000000) (-63181213131 / 1000000000000), orderedInterval (87489137011 / 1000000000000) (87489158771 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 3) <| besselDerivativeNearFromState (598830187342113 / 4000000000000) 3 (IntervalRat.scale (191 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-19541020742 / 1000000000000) (-19541020364 / 1000000000000), orderedInterval (62279334485 / 1000000000000) (62279334863 / 1000000000000)))) (orderedInterval (16452088443 / 1000000000000) (16452088735 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 3) <| besselDerivativeNearFromState (441095605660969 / 4000000000000) 3 (IntervalRat.scale (191 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-67797589254 / 1000000000000) (-67797589253 / 1000000000000), orderedInterval (-33993172029 / 1000000000000) (-33993172028 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 3) <| besselDerivativeNearFromState (755824838533837 / 4000000000000) 3 (IntervalRat.scale (191 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (54998024072 / 1000000000000) (54998024073 / 1000000000000), orderedInterval (18411063353 / 1000000000000) (18411063354 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 3) <| besselDerivativeNearFromState (556737155162983 / 4000000000000) 3 (IntervalRat.scale (191 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (66679439312 / 1000000000000) (66679439752 / 1000000000000), orderedInterval (-11542570186 / 1000000000000) (-11542569746 / 1000000000000)))) (orderedInterval (5228237516 / 1000000000000) (5228237581 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate214_chunkChecks3_1 :
    compactCertificate214.chunkChecks (3 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 3) <| besselDerivativeNearFromState (854177967404809 / 4000000000000) 3 (IntervalRat.scale (191 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (35216418359 / 1000000000000) (35216418360 / 1000000000000), orderedInterval (41642950967 / 1000000000000) (41642950968 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 3) <| besselDerivativeNearFromState (493159879416961 / 4000000000000) 3 (IntervalRat.scale (191 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-71845510045 / 1000000000000) (-71845510015 / 1000000000000), orderedInterval (-1041939789 / 1000000000000) (-1041939760 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 3) <| besselDerivativeNearFromState (875120860154549 / 4000000000000) 3 (IntervalRat.scale (191 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-18316638779 / 1000000000000) (-18316638363 / 1000000000000), orderedInterval (50780075643 / 1000000000000) (50780076059 / 1000000000000)))) (orderedInterval (-4459676361 / 1000000000000) (-4459675270 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 3) <| besselDerivativeNearFromState (817651425248681 / 4000000000000) 3 (IntervalRat.scale (191 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-46781515023 / 1000000000000) (-46781515022 / 1000000000000), orderedInterval (-30313656252 / 1000000000000) (-30313656251 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 3) <| besselDerivativeNearFromState (583514638490873 / 4000000000000) 3 (IntervalRat.scale (191 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (55288277422 / 1000000000000) (55288313748 / 1000000000000), orderedInterval (-36345156675 / 1000000000000) (-36345120349 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 3) <| besselDerivativeNearFromState (661643408491167 / 4000000000000) 3 (IntervalRat.scale (191 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (18861143522 / 1000000000000) (18861143884 / 1000000000000), orderedInterval (-59158534500 / 1000000000000) (-59158534137 / 1000000000000)))) (orderedInterval (5492092659 / 1000000000000) (5492105048 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 3) <| besselDerivativeNearFromState (551609294207023 / 4000000000000) 3 (IntervalRat.scale (191 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (29965007543 / 1000000000000) (29965007544 / 1000000000000), orderedInterval (60871443770 / 1000000000000) (60871443771 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 3) <| besselDerivativeNearFromState (487363540063483 / 4000000000000) 3 (IntervalRat.scale (191 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-7442425604 / 1000000000000) (-7442425603 / 1000000000000), orderedInterval (-71869825995 / 1000000000000) (-71869825994 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 3) <| besselDerivativeNearFromState (141256949816817 / 800000000000) 3 (IntervalRat.scale (191 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (59422934136 / 1000000000000) (59422934142 / 1000000000000), orderedInterval (8454826416 / 1000000000000) (8454826422 / 1000000000000)))) (orderedInterval (-11955078128 / 1000000000000) (-11955078096 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate214_chunkChecks3_2 :
    compactCertificate214.chunkChecks (3 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 3) <| besselDerivativeNearFromState (390724157139299 / 4000000000000) 3 (IntervalRat.scale (191 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-71038992234 / 1000000000000) (-71038992233 / 1000000000000), orderedInterval (-37986699522 / 1000000000000) (-37986699521 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 3) <| besselDerivativeNearFromState (331221195158539 / 4000000000000) 3 (IntervalRat.scale (191 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (82749830908 / 1000000000000) (82749833255 / 1000000000000), orderedInterval (-29491170600 / 1000000000000) (-29491168252 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 3) <| besselDerivativeNearFromState (207262844837017 / 4000000000000) 3 (IntervalRat.scale (191 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (80156341471 / 1000000000000) (80156449334 / 1000000000000), orderedInterval (-77331639974 / 1000000000000) (-77331532110 / 1000000000000)))) (orderedInterval (-7088510187 / 1000000000000) (-7088509506 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 3) <| besselDerivativeNearFromState (111466647278439 / 4000000000000) 3 (IntervalRat.scale (191 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-55109188431 / 1000000000000) (-55109188430 / 1000000000000), orderedInterval (-139762652794 / 1000000000000) (-139762652793 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 3) <| besselDerivativeNearFromState (302653630712317 / 4000000000000) 3 (IntervalRat.scale (191 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (79516378746 / 1000000000000) (79516378747 / 1000000000000), orderedInterval (45200841736 / 1000000000000) (45200841737 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 3) <| besselDerivativeNearFromState (413247658082909 / 4000000000000) 3 (IntervalRat.scale (191 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-32262562731 / 1000000000000) (-32262562730 / 1000000000000), orderedInterval (-71407041255 / 1000000000000) (-71407041254 / 1000000000000)))) (orderedInterval (-6461859147 / 1000000000000) (-6461859135 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 3) <| besselDerivativeNearFromState (174737155162983 / 4000000000000) 3 (IntervalRat.scale (191 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (56228307256 / 1000000000000) (56228307257 / 1000000000000), orderedInterval (106184009444 / 1000000000000) (106184009445 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 3) <| besselDerivativeNearFromState (710296834620743 / 4000000000000) 3 (IntervalRat.scale (191 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (39114090341 / 1000000000000) (39114117240 / 1000000000000), orderedInterval (-45444243507 / 1000000000000) (-45444216608 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 3) <| besselDerivativeNearFromState (474445367484937 / 4000000000000) 3 (IntervalRat.scale (191 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (1110993534 / 1000000000000) (1110993539 / 1000000000000), orderedInterval (73248910850 / 1000000000000) (73248910855 / 1000000000000)))) (orderedInterval (2367794338 / 1000000000000) (2367808580 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate214_chunkChecks3 :
    compactCertificate214.chunkChecks (3 : Fin 5) 0 9 = true :=
  compactCertificate214.chunkChecks_nine_of_three (3 : Fin 5) compactCertificate214_chunkChecks3_0
    compactCertificate214_chunkChecks3_1 compactCertificate214_chunkChecks3_2

theorem compactCertificate214_chunkChecks4_0 :
    compactCertificate214.chunkChecks (4 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 4) <| besselDerivativeNearFromState (191 / 2) 4 (IntervalRat.scale (191 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (72958226021 / 1000000000000) (72958235750 / 1000000000000), orderedInterval (-37031907524 / 1000000000000) (-37031897795 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 4) <| besselDerivativeNearFromState (281379471049091 / 4000000000000) 4 (IntervalRat.scale (191 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (85961334525 / 1000000000000) (85961341339 / 1000000000000), orderedInterval (-41360026476 / 1000000000000) (-41360019662 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 4) <| besselDerivativeNearFromState (90992339631203 / 800000000000) 4 (IntervalRat.scale (191 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (74045611559 / 1000000000000) (74045611563 / 1000000000000), orderedInterval (10366746115 / 1000000000000) (10366746120 / 1000000000000)))) (orderedInterval (37595867662 / 1000000000000) (37595871630 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 4) <| besselDerivativeNearFromState (82105827881737 / 4000000000000) 4 (IntervalRat.scale (191 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (111454533145 / 1000000000000) (111454574671 / 1000000000000), orderedInterval (-139074240824 / 1000000000000) (-139074199298 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 4) <| besselDerivativeNearFromState (220547802830389 / 4000000000000) 4 (IntervalRat.scale (191 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-63181234891 / 1000000000000) (-63181213131 / 1000000000000), orderedInterval (87489137011 / 1000000000000) (87489158771 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 4) <| besselDerivativeNearFromState (598830187342113 / 4000000000000) 4 (IntervalRat.scale (191 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-19541020742 / 1000000000000) (-19541020364 / 1000000000000), orderedInterval (62279334485 / 1000000000000) (62279334863 / 1000000000000)))) (orderedInterval (7785372400 / 1000000000000) (7785372699 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 4) <| besselDerivativeNearFromState (441095605660969 / 4000000000000) 4 (IntervalRat.scale (191 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-67797589254 / 1000000000000) (-67797589253 / 1000000000000), orderedInterval (-33993172029 / 1000000000000) (-33993172028 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 4) <| besselDerivativeNearFromState (755824838533837 / 4000000000000) 4 (IntervalRat.scale (191 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (54998024072 / 1000000000000) (54998024073 / 1000000000000), orderedInterval (18411063353 / 1000000000000) (18411063354 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 4) <| besselDerivativeNearFromState (556737155162983 / 4000000000000) 4 (IntervalRat.scale (191 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (66679439312 / 1000000000000) (66679439752 / 1000000000000), orderedInterval (-11542570186 / 1000000000000) (-11542569746 / 1000000000000)))) (orderedInterval (-18836905255 / 1000000000000) (-18836905149 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate214_chunkChecks4_1 :
    compactCertificate214.chunkChecks (4 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 4) <| besselDerivativeNearFromState (854177967404809 / 4000000000000) 4 (IntervalRat.scale (191 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (35216418359 / 1000000000000) (35216418360 / 1000000000000), orderedInterval (41642950967 / 1000000000000) (41642950968 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 4) <| besselDerivativeNearFromState (493159879416961 / 4000000000000) 4 (IntervalRat.scale (191 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-71845510045 / 1000000000000) (-71845510015 / 1000000000000), orderedInterval (-1041939789 / 1000000000000) (-1041939760 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 4) <| besselDerivativeNearFromState (875120860154549 / 4000000000000) 4 (IntervalRat.scale (191 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-18316638779 / 1000000000000) (-18316638363 / 1000000000000), orderedInterval (50780075643 / 1000000000000) (50780076059 / 1000000000000)))) (orderedInterval (-242843762180 / 1000000000000) (-242843759707 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 4) <| besselDerivativeNearFromState (817651425248681 / 4000000000000) 4 (IntervalRat.scale (191 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-46781515023 / 1000000000000) (-46781515022 / 1000000000000), orderedInterval (-30313656252 / 1000000000000) (-30313656251 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 4) <| besselDerivativeNearFromState (583514638490873 / 4000000000000) 4 (IntervalRat.scale (191 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (55288277422 / 1000000000000) (55288313748 / 1000000000000), orderedInterval (-36345156675 / 1000000000000) (-36345120349 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 4) <| besselDerivativeNearFromState (661643408491167 / 4000000000000) 4 (IntervalRat.scale (191 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (18861143522 / 1000000000000) (18861143884 / 1000000000000), orderedInterval (-59158534500 / 1000000000000) (-59158534137 / 1000000000000)))) (orderedInterval (45216369003 / 1000000000000) (45216388066 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 4) <| besselDerivativeNearFromState (551609294207023 / 4000000000000) 4 (IntervalRat.scale (191 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (29965007543 / 1000000000000) (29965007544 / 1000000000000), orderedInterval (60871443770 / 1000000000000) (60871443771 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 4) <| besselDerivativeNearFromState (487363540063483 / 4000000000000) 4 (IntervalRat.scale (191 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-7442425604 / 1000000000000) (-7442425603 / 1000000000000), orderedInterval (-71869825995 / 1000000000000) (-71869825994 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 4) <| besselDerivativeNearFromState (141256949816817 / 800000000000) 4 (IntervalRat.scale (191 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (59422934136 / 1000000000000) (59422934142 / 1000000000000), orderedInterval (8454826416 / 1000000000000) (8454826422 / 1000000000000)))) (orderedInterval (20662315395 / 1000000000000) (20662315446 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate214_chunkChecks4_2 :
    compactCertificate214.chunkChecks (4 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 4) <| besselDerivativeNearFromState (390724157139299 / 4000000000000) 4 (IntervalRat.scale (191 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-71038992234 / 1000000000000) (-71038992233 / 1000000000000), orderedInterval (-37986699522 / 1000000000000) (-37986699521 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 4) <| besselDerivativeNearFromState (331221195158539 / 4000000000000) 4 (IntervalRat.scale (191 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (82749830908 / 1000000000000) (82749833255 / 1000000000000), orderedInterval (-29491170600 / 1000000000000) (-29491168252 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 4) <| besselDerivativeNearFromState (207262844837017 / 4000000000000) 4 (IntervalRat.scale (191 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (80156341471 / 1000000000000) (80156449334 / 1000000000000), orderedInterval (-77331639974 / 1000000000000) (-77331532110 / 1000000000000)))) (orderedInterval (10158612055 / 1000000000000) (10158612469 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 4) <| besselDerivativeNearFromState (111466647278439 / 4000000000000) 4 (IntervalRat.scale (191 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-55109188431 / 1000000000000) (-55109188430 / 1000000000000), orderedInterval (-139762652794 / 1000000000000) (-139762652793 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 4) <| besselDerivativeNearFromState (302653630712317 / 4000000000000) 4 (IntervalRat.scale (191 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (79516378746 / 1000000000000) (79516378747 / 1000000000000), orderedInterval (45200841736 / 1000000000000) (45200841737 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 4) <| besselDerivativeNearFromState (413247658082909 / 4000000000000) 4 (IntervalRat.scale (191 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-32262562731 / 1000000000000) (-32262562730 / 1000000000000), orderedInterval (-71407041255 / 1000000000000) (-71407041254 / 1000000000000)))) (orderedInterval (2818049019 / 1000000000000) (2818049031 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 4) <| besselDerivativeNearFromState (174737155162983 / 4000000000000) 4 (IntervalRat.scale (191 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (56228307256 / 1000000000000) (56228307257 / 1000000000000), orderedInterval (106184009444 / 1000000000000) (106184009445 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 4) <| besselDerivativeNearFromState (710296834620743 / 4000000000000) 4 (IntervalRat.scale (191 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (39114090341 / 1000000000000) (39114117240 / 1000000000000), orderedInterval (-45444243507 / 1000000000000) (-45444216608 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 4) <| besselDerivativeNearFromState (474445367484937 / 4000000000000) 4 (IntervalRat.scale (191 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (1110993534 / 1000000000000) (1110993539 / 1000000000000), orderedInterval (73248910850 / 1000000000000) (73248910855 / 1000000000000)))) (orderedInterval (-38589919872 / 1000000000000) (-38589893267 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate214_chunkChecks4 :
    compactCertificate214.chunkChecks (4 : Fin 5) 0 9 = true :=
  compactCertificate214.chunkChecks_nine_of_three (4 : Fin 5) compactCertificate214_chunkChecks4_0
    compactCertificate214_chunkChecks4_1 compactCertificate214_chunkChecks4_2

theorem compactCertificate214_chunks :
    ∀ r : Fin 5, ∀ b, compactCertificate214.chunkCheck r b = true :=
  compactCertificate214.chunkChecks_all (by
    intro r
    fin_cases r
    · exact compactCertificate214_chunkChecks0
    · exact compactCertificate214_chunkChecks1
    · exact compactCertificate214_chunkChecks2
    · exact compactCertificate214_chunkChecks3
    · exact compactCertificate214_chunkChecks4)

theorem compactCertificate214_coefficient0 :
    compactCertificate214.coefficientCheck (0 : Fin 5) = true := by
  norm_num [CompactCertificate.coefficientCheck, intervalFinSumHull,
    compactCertificate214, rationalIntervalSubset, orderedInterval, Fin.sum_univ_succ]

theorem compactCertificate214_coefficient1 :
    compactCertificate214.coefficientCheck (1 : Fin 5) = true := by
  norm_num [CompactCertificate.coefficientCheck, intervalFinSumHull,
    compactCertificate214, rationalIntervalSubset, orderedInterval, Fin.sum_univ_succ]

theorem compactCertificate214_coefficient2 :
    compactCertificate214.coefficientCheck (2 : Fin 5) = true := by
  norm_num [CompactCertificate.coefficientCheck, intervalFinSumHull,
    compactCertificate214, rationalIntervalSubset, orderedInterval, Fin.sum_univ_succ]

theorem compactCertificate214_coefficient3 :
    compactCertificate214.coefficientCheck (3 : Fin 5) = true := by
  norm_num [CompactCertificate.coefficientCheck, intervalFinSumHull,
    compactCertificate214, rationalIntervalSubset, orderedInterval, Fin.sum_univ_succ]

theorem compactCertificate214_coefficient4 :
    compactCertificate214.coefficientCheck (4 : Fin 5) = true := by
  norm_num [CompactCertificate.coefficientCheck, intervalFinSumHull,
    compactCertificate214, rationalIntervalSubset, orderedInterval, Fin.sum_univ_succ]

theorem compactCertificate214_coefficients : ∀ r : Fin 5,
    compactCertificate214.coefficientCheck r = true := by
  intro r
  fin_cases r
  · exact compactCertificate214_coefficient0
  · exact compactCertificate214_coefficient1
  · exact compactCertificate214_coefficient2
  · exact compactCertificate214_coefficient3
  · exact compactCertificate214_coefficient4

theorem compactCertificate214_lower : (1 : ℚ) ≤ compactCertificate214.output.lo := by
  norm_num [CompactCertificate.output, CompactCertificate.interval,
    CompactCertificate.coefficientTargetNat, compactCertificate214, dualConstant,
    intervalTaylorSum, intervalPow, intervalSub, intervalMaxAbs, widenInterval,
    rationalErrorInterval, orderedInterval, IntervalRat.add, IntervalRat.mul, IntervalRat.scale,
    IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4]

theorem compactCertificate214_proves {t : ℝ} (ht : t ∈ compactCertificate214.interval) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t :=
  compactCertificate214.proves compactCertificate214_states compactCertificate214_chunks
    compactCertificate214_coefficients compactCertificate214_lower ht

end Erdos232
