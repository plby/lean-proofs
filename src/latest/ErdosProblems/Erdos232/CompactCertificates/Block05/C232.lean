/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, OpenAI Codex
-/
import ErdosProblems.Erdos232.CompactBase

open LeanCert.Core
namespace Erdos232

def compactCertificate232 : CompactCertificate where
  left := 109
  right := 110
  center := 219 / 2
  grid := fun i =>
    match i.val with
    | 0 => 35
    | 1 => 26
    | 2 => 42
    | 3 => 7
    | 4 => 20
    | 5 => 55
    | 6 => 40
    | 7 => 69
    | 8 => 51
    | 9 => 78
    | 10 => 45
    | 11 => 80
    | 12 => 75
    | 13 => 53
    | 14 => 60
    | 15 => 50
    | 16 => 44
    | 17 => 64
    | 18 => 36
    | 19 => 30
    | 20 => 19
    | 21 => 10
    | 22 => 28
    | 23 => 38
    | 24 => 16
    | 25 => 65
    | _ => 43
  point := fun i =>
    match i.val with
    | 0 => 219 / 2
    | 1 => 322628817590319 / 4000000000000
    | 2 => 104331530781327 / 800000000000
    | 3 => 94142284325133 / 4000000000000
    | 4 => 252879417905001 / 4000000000000
    | 5 => 686616811664517 / 4000000000000
    | 6 => 505758835810221 / 4000000000000
    | 7 => 866626385544033 / 4000000000000
    | 8 => 638353073197347 / 4000000000000
    | 9 => 979397774144781 / 4000000000000
    | 10 => 565455568546149 / 4000000000000
    | 11 => 1003410829182441 / 4000000000000
    | 12 => 937516555651629 / 4000000000000
    | 13 => 669056051463357 / 4000000000000
    | 14 => 758638253715003 / 4000000000000
    | 15 => 632473483933707 / 4000000000000
    | 16 => 558809504051847 / 4000000000000
    | 17 => 161964774920853 / 800000000000
    | 18 => 448003091170191 / 4000000000000
    | 19 => 379777181883351 / 4000000000000
    | 20 => 237646926802653 / 4000000000000
    | 21 => 127807307612451 / 4000000000000
    | 22 => 347021702230353 / 4000000000000
    | 23 => 473828466597681 / 4000000000000
    | 24 => 200353073197347 / 4000000000000
    | 25 => 814424119277187 / 4000000000000
    | _ => 543997567953933 / 4000000000000
  state := fun i =>
    match i.val with
    | 0 => (orderedInterval (-24600528434 / 1000000000000) (-24600528433 / 1000000000000), orderedInterval (-72059280444 / 1000000000000) (-72059280443 / 1000000000000))
    | 1 => (orderedInterval (-21148507674 / 1000000000000) (-21148507416 / 1000000000000), orderedInterval (86420038270 / 1000000000000) (86420038527 / 1000000000000))
    | 2 => (orderedInterval (-47524090904 / 1000000000000) (-47524044675 / 1000000000000), orderedInterval (51397208670 / 1000000000000) (51397254899 / 1000000000000))
    | 3 => (orderedInterval (-119907264057 / 1000000000000) (-119907163752 / 1000000000000), orderedInterval (115112293764 / 1000000000000) (115112394069 / 1000000000000))
    | 4 => (orderedInterval (92450616445 / 1000000000000) (92450616446 / 1000000000000), orderedInterval (38289345013 / 1000000000000) (38289345014 / 1000000000000))
    | 5 => (orderedInterval (20809150977 / 1000000000000) (20809151553 / 1000000000000), orderedInterval (-57294565204 / 1000000000000) (-57294564628 / 1000000000000))
    | 6 => (orderedInterval (70953399060 / 1000000000000) (70953399094 / 1000000000000), orderedInterval (456230202 / 1000000000000) (456230236 / 1000000000000))
    | 7 => (orderedInterval (-33726379039 / 1000000000000) (-33726379038 / 1000000000000), orderedInterval (-42359353187 / 1000000000000) (-42359353186 / 1000000000000))
    | 8 => (orderedInterval (-9541956092 / 1000000000000) (-9541956091 / 1000000000000), orderedInterval (-62404940208 / 1000000000000) (-62404940207 / 1000000000000))
    | 9 => (orderedInterval (28373592606 / 1000000000000) (28373592607 / 1000000000000), orderedInterval (42309347755 / 1000000000000) (42309347756 / 1000000000000))
    | 10 => (orderedInterval (-47039213094 / 1000000000000) (-47039213093 / 1000000000000), orderedInterval (-47695138289 / 1000000000000) (-47695138288 / 1000000000000))
    | 11 => (orderedInterval (15377214730 / 1000000000000) (15377214731 / 1000000000000), orderedInterval (47941929667 / 1000000000000) (47941929668 / 1000000000000))
    | 12 => (orderedInterval (22924335164 / 1000000000000) (22924336580 / 1000000000000), orderedInterval (-46853552143 / 1000000000000) (-46853550727 / 1000000000000))
    | 13 => (orderedInterval (-61671544899 / 1000000000000) (-61671544863 / 1000000000000), orderedInterval (-1453002584 / 1000000000000) (-1453002548 / 1000000000000))
    | 14 => (orderedInterval (53847540956 / 1000000000000) (53847547407 / 1000000000000), orderedInterval (-21521347921 / 1000000000000) (-21521341469 / 1000000000000))
    | 15 => (orderedInterval (61439558917 / 1000000000000) (61439560293 / 1000000000000), orderedInterval (-16049425888 / 1000000000000) (-16049424512 / 1000000000000))
    | 16 => (orderedInterval (52234204595 / 1000000000000) (52234294385 / 1000000000000), orderedInterval (-42948523826 / 1000000000000) (-42948434036 / 1000000000000))
    | 17 => (orderedInterval (46025653023 / 1000000000000) (46025713383 / 1000000000000), orderedInterval (-32146775266 / 1000000000000) (-32146714906 / 1000000000000))
    | 18 => (orderedInterval (-23162776901 / 1000000000000) (-23162776370 / 1000000000000), orderedInterval (71850162482 / 1000000000000) (71850163013 / 1000000000000))
    | 19 => (orderedInterval (81551798085 / 1000000000000) (81551798093 / 1000000000000), orderedInterval (6946529327 / 1000000000000) (6946529335 / 1000000000000))
    | 20 => (orderedInterval (-50059299454 / 1000000000000) (-50059299453 / 1000000000000), orderedInterval (-90185894264 / 1000000000000) (-90185894263 / 1000000000000))
    | 21 => (orderedInterval (136637398711 / 1000000000000) (136637398712 / 1000000000000), orderedInterval (33252372761 / 1000000000000) (33252372762 / 1000000000000))
    | 22 => (orderedInterval (-35336707984 / 1000000000000) (-35336705656 / 1000000000000), orderedInterval (78238865684 / 1000000000000) (78238868012 / 1000000000000))
    | 23 => (orderedInterval (-10161619865 / 1000000000000) (-10161619817 / 1000000000000), orderedInterval (72644895770 / 1000000000000) (72644895818 / 1000000000000))
    | 24 => (orderedInterval (64183623449 / 1000000000000) (64183623450 / 1000000000000), orderedInterval (92045079241 / 1000000000000) (92045079242 / 1000000000000))
    | 25 => (orderedInterval (-10411668173 / 1000000000000) (-10411668172 / 1000000000000), orderedInterval (-54913757692 / 1000000000000) (-54913757691 / 1000000000000))
    | _ => (orderedInterval (-67887625123 / 1000000000000) (-67887624877 / 1000000000000), orderedInterval (8751841855 / 1000000000000) (8751842101 / 1000000000000))
  chunkTarget := fun r b =>
    match r.val with
    | 0 =>
      match b.val with
      | 0 => orderedInterval (-12736619180 / 1000000000000) (-12736616456 / 1000000000000)
      | 1 => orderedInterval (3197126017 / 1000000000000) (3197127161 / 1000000000000)
      | 2 => orderedInterval (809646213 / 1000000000000) (809646220 / 1000000000000)
      | 3 => orderedInterval (-6340901774 / 1000000000000) (-6340901729 / 1000000000000)
      | 4 => orderedInterval (-6518192669 / 1000000000000) (-6518192594 / 1000000000000)
      | 5 => orderedInterval (-1101272829 / 1000000000000) (-1101266118 / 1000000000000)
      | 6 => orderedInterval (-2541969380 / 1000000000000) (-2541969267 / 1000000000000)
      | 7 => orderedInterval (-942571536 / 1000000000000) (-942571465 / 1000000000000)
      | _ => orderedInterval (13971967492 / 1000000000000) (13971967569 / 1000000000000)
    | 1 =>
      match b.val with
      | 0 => orderedInterval (-24376510738 / 1000000000000) (-24376507496 / 1000000000000)
      | 1 => orderedInterval (6923697794 / 1000000000000) (6923698107 / 1000000000000)
      | 2 => orderedInterval (387005037 / 1000000000000) (387005049 / 1000000000000)
      | 3 => orderedInterval (-5759632225 / 1000000000000) (-5759632133 / 1000000000000)
      | 4 => orderedInterval (1789257314 / 1000000000000) (1789257452 / 1000000000000)
      | 5 => orderedInterval (1346273798 / 1000000000000) (1346283250 / 1000000000000)
      | 6 => orderedInterval (-13684586468 / 1000000000000) (-13684586354 / 1000000000000)
      | 7 => orderedInterval (-7608310014 / 1000000000000) (-7608309956 / 1000000000000)
      | _ => orderedInterval (6526082396 / 1000000000000) (6526082497 / 1000000000000)
    | 2 =>
      match b.val with
      | 0 => orderedInterval (14036130942 / 1000000000000) (14036134832 / 1000000000000)
      | 1 => orderedInterval (2386801904 / 1000000000000) (2386802079 / 1000000000000)
      | 2 => orderedInterval (-3586148923 / 1000000000000) (-3586148903 / 1000000000000)
      | 3 => orderedInterval (19597184221 / 1000000000000) (19597184417 / 1000000000000)
      | 4 => orderedInterval (16304865827 / 1000000000000) (16304866087 / 1000000000000)
      | 5 => orderedInterval (-654584356 / 1000000000000) (-654570566 / 1000000000000)
      | 6 => orderedInterval (200319584 / 1000000000000) (200319699 / 1000000000000)
      | 7 => orderedInterval (-1130315517 / 1000000000000) (-1130315466 / 1000000000000)
      | _ => orderedInterval (-22719377232 / 1000000000000) (-22719377097 / 1000000000000)
    | 3 =>
      match b.val with
      | 0 => orderedInterval (23014392164 / 1000000000000) (23014396795 / 1000000000000)
      | 1 => orderedInterval (-15968508302 / 1000000000000) (-15968508100 / 1000000000000)
      | 2 => orderedInterval (-5418552435 / 1000000000000) (-5418552399 / 1000000000000)
      | 3 => orderedInterval (9536641866 / 1000000000000) (9536642293 / 1000000000000)
      | 4 => orderedInterval (-8519792810 / 1000000000000) (-8519792315 / 1000000000000)
      | 5 => orderedInterval (662331967 / 1000000000000) (662352612 / 1000000000000)
      | 6 => orderedInterval (13015811248 / 1000000000000) (13015811364 / 1000000000000)
      | 7 => orderedInterval (7956184501 / 1000000000000) (7956184545 / 1000000000000)
      | _ => orderedInterval (-25436265467 / 1000000000000) (-25436265279 / 1000000000000)
    | _ =>
      match b.val with
      | 0 => orderedInterval (-15839198215 / 1000000000000) (-15839192659 / 1000000000000)
      | 1 => orderedInterval (-8263815304 / 1000000000000) (-8263815003 / 1000000000000)
      | 2 => orderedInterval (15001265685 / 1000000000000) (15001265750 / 1000000000000)
      | 3 => orderedInterval (-75685854853 / 1000000000000) (-75685853905 / 1000000000000)
      | 4 => orderedInterval (-42733598502 / 1000000000000) (-42733597541 / 1000000000000)
      | 5 => orderedInterval (8924018319 / 1000000000000) (8924050489 / 1000000000000)
      | 6 => orderedInterval (1065743290 / 1000000000000) (1065743408 / 1000000000000)
      | 7 => orderedInterval (1218784373 / 1000000000000) (1218784413 / 1000000000000)
      | _ => orderedInterval (40920138442 / 1000000000000) (40920138711 / 1000000000000)
  coefficientTarget := fun i =>
    match i.val with
    | 0 => orderedInterval (-12202787646 / 1000000000000) (-12202776679 / 1000000000000)
    | 1 => orderedInterval (-34456723106 / 1000000000000) (-34456709584 / 1000000000000)
    | 2 => orderedInterval (24434876450 / 1000000000000) (24434895082 / 1000000000000)
    | 3 => orderedInterval (-1157757268 / 1000000000000) (-1157730484 / 1000000000000)
    | _ => orderedInterval (-75392516765 / 1000000000000) (-75392476337 / 1000000000000)

theorem compactCertificate232_stateChecks0 :
    compactCertificate232.stateChecks 0 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 35 12 (219 / 2)) (orderedInterval (-24600528434 / 1000000000000) (-24600528433 / 1000000000000), orderedInterval (-72059280444 / 1000000000000) (-72059280443 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 26 12 (322628817590319 / 4000000000000)) (orderedInterval (-21148507674 / 1000000000000) (-21148507416 / 1000000000000), orderedInterval (86420038270 / 1000000000000) (86420038527 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 42 12 (104331530781327 / 800000000000)) (orderedInterval (-47524090904 / 1000000000000) (-47524044675 / 1000000000000), orderedInterval (51397208670 / 1000000000000) (51397254899 / 1000000000000))) = true
  norm_num [besselStateAtRationalPoint, besselIntervalStepZero,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, besselZeroTransition,
    besselInitial, besselGridStateAt, besselGridStateBlock00, besselGridStateBlock01,
    besselGridStateBlock02, besselGridStateBlock03, besselGridStateBlock04,
    besselGridStateBlock05, besselGridStateBlock06, besselGridStateBlock07,
    besselGridStateBlock08, besselGridStateBlock09, besselGridStateBlock10,
    besselGridStateBlock11, besselGridStateBlock12, besselGridStateBlock13,
    besselGridStateBlock14, besselGridState007, besselGridState010, besselGridState016, besselGridState019, besselGridState020, besselGridState026, besselGridState028, besselGridState030, besselGridState035, besselGridState036, besselGridState038, besselGridState040, besselGridState042, besselGridState043, besselGridState044, besselGridState045, besselGridState050, besselGridState051, besselGridState053, besselGridState055, besselGridState060, besselGridState064, besselGridState065, besselGridState069, besselGridState075, besselGridState078, besselGridState080, besselStateSubset, linearInterval, widenInterval,
    rationalErrorInterval, rationalIntervalSubset, orderedInterval, Finset.sum_range_succ,
    IntervalRat.add, IntervalRat.mul, IntervalRat.scale, IntervalRat.singleton]

theorem compactCertificate232_stateChecks1 :
    compactCertificate232.stateChecks 3 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 7 12 (94142284325133 / 4000000000000)) (orderedInterval (-119907264057 / 1000000000000) (-119907163752 / 1000000000000), orderedInterval (115112293764 / 1000000000000) (115112394069 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 20 12 (252879417905001 / 4000000000000)) (orderedInterval (92450616445 / 1000000000000) (92450616446 / 1000000000000), orderedInterval (38289345013 / 1000000000000) (38289345014 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 55 12 (686616811664517 / 4000000000000)) (orderedInterval (20809150977 / 1000000000000) (20809151553 / 1000000000000), orderedInterval (-57294565204 / 1000000000000) (-57294564628 / 1000000000000))) = true
  norm_num [besselStateAtRationalPoint, besselIntervalStepZero,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, besselZeroTransition,
    besselInitial, besselGridStateAt, besselGridStateBlock00, besselGridStateBlock01,
    besselGridStateBlock02, besselGridStateBlock03, besselGridStateBlock04,
    besselGridStateBlock05, besselGridStateBlock06, besselGridStateBlock07,
    besselGridStateBlock08, besselGridStateBlock09, besselGridStateBlock10,
    besselGridStateBlock11, besselGridStateBlock12, besselGridStateBlock13,
    besselGridStateBlock14, besselGridState007, besselGridState010, besselGridState016, besselGridState019, besselGridState020, besselGridState026, besselGridState028, besselGridState030, besselGridState035, besselGridState036, besselGridState038, besselGridState040, besselGridState042, besselGridState043, besselGridState044, besselGridState045, besselGridState050, besselGridState051, besselGridState053, besselGridState055, besselGridState060, besselGridState064, besselGridState065, besselGridState069, besselGridState075, besselGridState078, besselGridState080, besselStateSubset, linearInterval, widenInterval,
    rationalErrorInterval, rationalIntervalSubset, orderedInterval, Finset.sum_range_succ,
    IntervalRat.add, IntervalRat.mul, IntervalRat.scale, IntervalRat.singleton]

theorem compactCertificate232_stateChecks2 :
    compactCertificate232.stateChecks 6 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 40 12 (505758835810221 / 4000000000000)) (orderedInterval (70953399060 / 1000000000000) (70953399094 / 1000000000000), orderedInterval (456230202 / 1000000000000) (456230236 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 69 12 (866626385544033 / 4000000000000)) (orderedInterval (-33726379039 / 1000000000000) (-33726379038 / 1000000000000), orderedInterval (-42359353187 / 1000000000000) (-42359353186 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 51 12 (638353073197347 / 4000000000000)) (orderedInterval (-9541956092 / 1000000000000) (-9541956091 / 1000000000000), orderedInterval (-62404940208 / 1000000000000) (-62404940207 / 1000000000000))) = true
  norm_num [besselStateAtRationalPoint, besselIntervalStepZero,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, besselZeroTransition,
    besselInitial, besselGridStateAt, besselGridStateBlock00, besselGridStateBlock01,
    besselGridStateBlock02, besselGridStateBlock03, besselGridStateBlock04,
    besselGridStateBlock05, besselGridStateBlock06, besselGridStateBlock07,
    besselGridStateBlock08, besselGridStateBlock09, besselGridStateBlock10,
    besselGridStateBlock11, besselGridStateBlock12, besselGridStateBlock13,
    besselGridStateBlock14, besselGridState007, besselGridState010, besselGridState016, besselGridState019, besselGridState020, besselGridState026, besselGridState028, besselGridState030, besselGridState035, besselGridState036, besselGridState038, besselGridState040, besselGridState042, besselGridState043, besselGridState044, besselGridState045, besselGridState050, besselGridState051, besselGridState053, besselGridState055, besselGridState060, besselGridState064, besselGridState065, besselGridState069, besselGridState075, besselGridState078, besselGridState080, besselStateSubset, linearInterval, widenInterval,
    rationalErrorInterval, rationalIntervalSubset, orderedInterval, Finset.sum_range_succ,
    IntervalRat.add, IntervalRat.mul, IntervalRat.scale, IntervalRat.singleton]

theorem compactCertificate232_stateChecks3 :
    compactCertificate232.stateChecks 9 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 78 12 (979397774144781 / 4000000000000)) (orderedInterval (28373592606 / 1000000000000) (28373592607 / 1000000000000), orderedInterval (42309347755 / 1000000000000) (42309347756 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 45 12 (565455568546149 / 4000000000000)) (orderedInterval (-47039213094 / 1000000000000) (-47039213093 / 1000000000000), orderedInterval (-47695138289 / 1000000000000) (-47695138288 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 80 12 (1003410829182441 / 4000000000000)) (orderedInterval (15377214730 / 1000000000000) (15377214731 / 1000000000000), orderedInterval (47941929667 / 1000000000000) (47941929668 / 1000000000000))) = true
  norm_num [besselStateAtRationalPoint, besselIntervalStepZero,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, besselZeroTransition,
    besselInitial, besselGridStateAt, besselGridStateBlock00, besselGridStateBlock01,
    besselGridStateBlock02, besselGridStateBlock03, besselGridStateBlock04,
    besselGridStateBlock05, besselGridStateBlock06, besselGridStateBlock07,
    besselGridStateBlock08, besselGridStateBlock09, besselGridStateBlock10,
    besselGridStateBlock11, besselGridStateBlock12, besselGridStateBlock13,
    besselGridStateBlock14, besselGridState007, besselGridState010, besselGridState016, besselGridState019, besselGridState020, besselGridState026, besselGridState028, besselGridState030, besselGridState035, besselGridState036, besselGridState038, besselGridState040, besselGridState042, besselGridState043, besselGridState044, besselGridState045, besselGridState050, besselGridState051, besselGridState053, besselGridState055, besselGridState060, besselGridState064, besselGridState065, besselGridState069, besselGridState075, besselGridState078, besselGridState080, besselStateSubset, linearInterval, widenInterval,
    rationalErrorInterval, rationalIntervalSubset, orderedInterval, Finset.sum_range_succ,
    IntervalRat.add, IntervalRat.mul, IntervalRat.scale, IntervalRat.singleton]

theorem compactCertificate232_stateChecks4 :
    compactCertificate232.stateChecks 12 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 75 12 (937516555651629 / 4000000000000)) (orderedInterval (22924335164 / 1000000000000) (22924336580 / 1000000000000), orderedInterval (-46853552143 / 1000000000000) (-46853550727 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 53 12 (669056051463357 / 4000000000000)) (orderedInterval (-61671544899 / 1000000000000) (-61671544863 / 1000000000000), orderedInterval (-1453002584 / 1000000000000) (-1453002548 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 60 12 (758638253715003 / 4000000000000)) (orderedInterval (53847540956 / 1000000000000) (53847547407 / 1000000000000), orderedInterval (-21521347921 / 1000000000000) (-21521341469 / 1000000000000))) = true
  norm_num [besselStateAtRationalPoint, besselIntervalStepZero,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, besselZeroTransition,
    besselInitial, besselGridStateAt, besselGridStateBlock00, besselGridStateBlock01,
    besselGridStateBlock02, besselGridStateBlock03, besselGridStateBlock04,
    besselGridStateBlock05, besselGridStateBlock06, besselGridStateBlock07,
    besselGridStateBlock08, besselGridStateBlock09, besselGridStateBlock10,
    besselGridStateBlock11, besselGridStateBlock12, besselGridStateBlock13,
    besselGridStateBlock14, besselGridState007, besselGridState010, besselGridState016, besselGridState019, besselGridState020, besselGridState026, besselGridState028, besselGridState030, besselGridState035, besselGridState036, besselGridState038, besselGridState040, besselGridState042, besselGridState043, besselGridState044, besselGridState045, besselGridState050, besselGridState051, besselGridState053, besselGridState055, besselGridState060, besselGridState064, besselGridState065, besselGridState069, besselGridState075, besselGridState078, besselGridState080, besselStateSubset, linearInterval, widenInterval,
    rationalErrorInterval, rationalIntervalSubset, orderedInterval, Finset.sum_range_succ,
    IntervalRat.add, IntervalRat.mul, IntervalRat.scale, IntervalRat.singleton]

theorem compactCertificate232_stateChecks5 :
    compactCertificate232.stateChecks 15 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 50 12 (632473483933707 / 4000000000000)) (orderedInterval (61439558917 / 1000000000000) (61439560293 / 1000000000000), orderedInterval (-16049425888 / 1000000000000) (-16049424512 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 44 12 (558809504051847 / 4000000000000)) (orderedInterval (52234204595 / 1000000000000) (52234294385 / 1000000000000), orderedInterval (-42948523826 / 1000000000000) (-42948434036 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 64 12 (161964774920853 / 800000000000)) (orderedInterval (46025653023 / 1000000000000) (46025713383 / 1000000000000), orderedInterval (-32146775266 / 1000000000000) (-32146714906 / 1000000000000))) = true
  norm_num [besselStateAtRationalPoint, besselIntervalStepZero,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, besselZeroTransition,
    besselInitial, besselGridStateAt, besselGridStateBlock00, besselGridStateBlock01,
    besselGridStateBlock02, besselGridStateBlock03, besselGridStateBlock04,
    besselGridStateBlock05, besselGridStateBlock06, besselGridStateBlock07,
    besselGridStateBlock08, besselGridStateBlock09, besselGridStateBlock10,
    besselGridStateBlock11, besselGridStateBlock12, besselGridStateBlock13,
    besselGridStateBlock14, besselGridState007, besselGridState010, besselGridState016, besselGridState019, besselGridState020, besselGridState026, besselGridState028, besselGridState030, besselGridState035, besselGridState036, besselGridState038, besselGridState040, besselGridState042, besselGridState043, besselGridState044, besselGridState045, besselGridState050, besselGridState051, besselGridState053, besselGridState055, besselGridState060, besselGridState064, besselGridState065, besselGridState069, besselGridState075, besselGridState078, besselGridState080, besselStateSubset, linearInterval, widenInterval,
    rationalErrorInterval, rationalIntervalSubset, orderedInterval, Finset.sum_range_succ,
    IntervalRat.add, IntervalRat.mul, IntervalRat.scale, IntervalRat.singleton]

theorem compactCertificate232_stateChecks6 :
    compactCertificate232.stateChecks 18 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 36 12 (448003091170191 / 4000000000000)) (orderedInterval (-23162776901 / 1000000000000) (-23162776370 / 1000000000000), orderedInterval (71850162482 / 1000000000000) (71850163013 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 30 12 (379777181883351 / 4000000000000)) (orderedInterval (81551798085 / 1000000000000) (81551798093 / 1000000000000), orderedInterval (6946529327 / 1000000000000) (6946529335 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 19 12 (237646926802653 / 4000000000000)) (orderedInterval (-50059299454 / 1000000000000) (-50059299453 / 1000000000000), orderedInterval (-90185894264 / 1000000000000) (-90185894263 / 1000000000000))) = true
  norm_num [besselStateAtRationalPoint, besselIntervalStepZero,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, besselZeroTransition,
    besselInitial, besselGridStateAt, besselGridStateBlock00, besselGridStateBlock01,
    besselGridStateBlock02, besselGridStateBlock03, besselGridStateBlock04,
    besselGridStateBlock05, besselGridStateBlock06, besselGridStateBlock07,
    besselGridStateBlock08, besselGridStateBlock09, besselGridStateBlock10,
    besselGridStateBlock11, besselGridStateBlock12, besselGridStateBlock13,
    besselGridStateBlock14, besselGridState007, besselGridState010, besselGridState016, besselGridState019, besselGridState020, besselGridState026, besselGridState028, besselGridState030, besselGridState035, besselGridState036, besselGridState038, besselGridState040, besselGridState042, besselGridState043, besselGridState044, besselGridState045, besselGridState050, besselGridState051, besselGridState053, besselGridState055, besselGridState060, besselGridState064, besselGridState065, besselGridState069, besselGridState075, besselGridState078, besselGridState080, besselStateSubset, linearInterval, widenInterval,
    rationalErrorInterval, rationalIntervalSubset, orderedInterval, Finset.sum_range_succ,
    IntervalRat.add, IntervalRat.mul, IntervalRat.scale, IntervalRat.singleton]

theorem compactCertificate232_stateChecks7 :
    compactCertificate232.stateChecks 21 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 10 12 (127807307612451 / 4000000000000)) (orderedInterval (136637398711 / 1000000000000) (136637398712 / 1000000000000), orderedInterval (33252372761 / 1000000000000) (33252372762 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 28 12 (347021702230353 / 4000000000000)) (orderedInterval (-35336707984 / 1000000000000) (-35336705656 / 1000000000000), orderedInterval (78238865684 / 1000000000000) (78238868012 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 38 12 (473828466597681 / 4000000000000)) (orderedInterval (-10161619865 / 1000000000000) (-10161619817 / 1000000000000), orderedInterval (72644895770 / 1000000000000) (72644895818 / 1000000000000))) = true
  norm_num [besselStateAtRationalPoint, besselIntervalStepZero,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, besselZeroTransition,
    besselInitial, besselGridStateAt, besselGridStateBlock00, besselGridStateBlock01,
    besselGridStateBlock02, besselGridStateBlock03, besselGridStateBlock04,
    besselGridStateBlock05, besselGridStateBlock06, besselGridStateBlock07,
    besselGridStateBlock08, besselGridStateBlock09, besselGridStateBlock10,
    besselGridStateBlock11, besselGridStateBlock12, besselGridStateBlock13,
    besselGridStateBlock14, besselGridState007, besselGridState010, besselGridState016, besselGridState019, besselGridState020, besselGridState026, besselGridState028, besselGridState030, besselGridState035, besselGridState036, besselGridState038, besselGridState040, besselGridState042, besselGridState043, besselGridState044, besselGridState045, besselGridState050, besselGridState051, besselGridState053, besselGridState055, besselGridState060, besselGridState064, besselGridState065, besselGridState069, besselGridState075, besselGridState078, besselGridState080, besselStateSubset, linearInterval, widenInterval,
    rationalErrorInterval, rationalIntervalSubset, orderedInterval, Finset.sum_range_succ,
    IntervalRat.add, IntervalRat.mul, IntervalRat.scale, IntervalRat.singleton]

theorem compactCertificate232_stateChecks8 :
    compactCertificate232.stateChecks 24 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 16 12 (200353073197347 / 4000000000000)) (orderedInterval (64183623449 / 1000000000000) (64183623450 / 1000000000000), orderedInterval (92045079241 / 1000000000000) (92045079242 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 65 12 (814424119277187 / 4000000000000)) (orderedInterval (-10411668173 / 1000000000000) (-10411668172 / 1000000000000), orderedInterval (-54913757692 / 1000000000000) (-54913757691 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 43 12 (543997567953933 / 4000000000000)) (orderedInterval (-67887625123 / 1000000000000) (-67887624877 / 1000000000000), orderedInterval (8751841855 / 1000000000000) (8751842101 / 1000000000000))) = true
  norm_num [besselStateAtRationalPoint, besselIntervalStepZero,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, besselZeroTransition,
    besselInitial, besselGridStateAt, besselGridStateBlock00, besselGridStateBlock01,
    besselGridStateBlock02, besselGridStateBlock03, besselGridStateBlock04,
    besselGridStateBlock05, besselGridStateBlock06, besselGridStateBlock07,
    besselGridStateBlock08, besselGridStateBlock09, besselGridStateBlock10,
    besselGridStateBlock11, besselGridStateBlock12, besselGridStateBlock13,
    besselGridStateBlock14, besselGridState007, besselGridState010, besselGridState016, besselGridState019, besselGridState020, besselGridState026, besselGridState028, besselGridState030, besselGridState035, besselGridState036, besselGridState038, besselGridState040, besselGridState042, besselGridState043, besselGridState044, besselGridState045, besselGridState050, besselGridState051, besselGridState053, besselGridState055, besselGridState060, besselGridState064, besselGridState065, besselGridState069, besselGridState075, besselGridState078, besselGridState080, besselStateSubset, linearInterval, widenInterval,
    rationalErrorInterval, rationalIntervalSubset, orderedInterval, Finset.sum_range_succ,
    IntervalRat.add, IntervalRat.mul, IntervalRat.scale, IntervalRat.singleton]

theorem compactCertificate232_states : ∀ j,
    BesselStateValid (compactCertificate232.point j) (compactCertificate232.state j) :=
  compactCertificate232.statesValid_of_checks3 compactCertificate232_stateChecks0
    compactCertificate232_stateChecks1 compactCertificate232_stateChecks2
    compactCertificate232_stateChecks3 compactCertificate232_stateChecks4
    compactCertificate232_stateChecks5 compactCertificate232_stateChecks6
    compactCertificate232_stateChecks7 compactCertificate232_stateChecks8

theorem compactCertificate232_chunkChecks0_0 :
    compactCertificate232.chunkChecks (0 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 0) <| besselDerivativeNearFromState (219 / 2) 0 (IntervalRat.scale (219 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-24600528434 / 1000000000000) (-24600528433 / 1000000000000), orderedInterval (-72059280444 / 1000000000000) (-72059280443 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 0) <| besselDerivativeNearFromState (322628817590319 / 4000000000000) 0 (IntervalRat.scale (219 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-21148507674 / 1000000000000) (-21148507416 / 1000000000000), orderedInterval (86420038270 / 1000000000000) (86420038527 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 0) <| besselDerivativeNearFromState (104331530781327 / 800000000000) 0 (IntervalRat.scale (219 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-47524090904 / 1000000000000) (-47524044675 / 1000000000000), orderedInterval (51397208670 / 1000000000000) (51397254899 / 1000000000000)))) (orderedInterval (-12736619180 / 1000000000000) (-12736616456 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 0) <| besselDerivativeNearFromState (94142284325133 / 4000000000000) 0 (IntervalRat.scale (219 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-119907264057 / 1000000000000) (-119907163752 / 1000000000000), orderedInterval (115112293764 / 1000000000000) (115112394069 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 0) <| besselDerivativeNearFromState (252879417905001 / 4000000000000) 0 (IntervalRat.scale (219 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (92450616445 / 1000000000000) (92450616446 / 1000000000000), orderedInterval (38289345013 / 1000000000000) (38289345014 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 0) <| besselDerivativeNearFromState (686616811664517 / 4000000000000) 0 (IntervalRat.scale (219 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (20809150977 / 1000000000000) (20809151553 / 1000000000000), orderedInterval (-57294565204 / 1000000000000) (-57294564628 / 1000000000000)))) (orderedInterval (3197126017 / 1000000000000) (3197127161 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 0) <| besselDerivativeNearFromState (505758835810221 / 4000000000000) 0 (IntervalRat.scale (219 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (70953399060 / 1000000000000) (70953399094 / 1000000000000), orderedInterval (456230202 / 1000000000000) (456230236 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 0) <| besselDerivativeNearFromState (866626385544033 / 4000000000000) 0 (IntervalRat.scale (219 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-33726379039 / 1000000000000) (-33726379038 / 1000000000000), orderedInterval (-42359353187 / 1000000000000) (-42359353186 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 0) <| besselDerivativeNearFromState (638353073197347 / 4000000000000) 0 (IntervalRat.scale (219 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-9541956092 / 1000000000000) (-9541956091 / 1000000000000), orderedInterval (-62404940208 / 1000000000000) (-62404940207 / 1000000000000)))) (orderedInterval (809646213 / 1000000000000) (809646220 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate232_chunkChecks0_1 :
    compactCertificate232.chunkChecks (0 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 0) <| besselDerivativeNearFromState (979397774144781 / 4000000000000) 0 (IntervalRat.scale (219 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (28373592606 / 1000000000000) (28373592607 / 1000000000000), orderedInterval (42309347755 / 1000000000000) (42309347756 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 0) <| besselDerivativeNearFromState (565455568546149 / 4000000000000) 0 (IntervalRat.scale (219 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-47039213094 / 1000000000000) (-47039213093 / 1000000000000), orderedInterval (-47695138289 / 1000000000000) (-47695138288 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 0) <| besselDerivativeNearFromState (1003410829182441 / 4000000000000) 0 (IntervalRat.scale (219 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (15377214730 / 1000000000000) (15377214731 / 1000000000000), orderedInterval (47941929667 / 1000000000000) (47941929668 / 1000000000000)))) (orderedInterval (-6340901774 / 1000000000000) (-6340901729 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 0) <| besselDerivativeNearFromState (937516555651629 / 4000000000000) 0 (IntervalRat.scale (219 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (22924335164 / 1000000000000) (22924336580 / 1000000000000), orderedInterval (-46853552143 / 1000000000000) (-46853550727 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 0) <| besselDerivativeNearFromState (669056051463357 / 4000000000000) 0 (IntervalRat.scale (219 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-61671544899 / 1000000000000) (-61671544863 / 1000000000000), orderedInterval (-1453002584 / 1000000000000) (-1453002548 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 0) <| besselDerivativeNearFromState (758638253715003 / 4000000000000) 0 (IntervalRat.scale (219 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (53847540956 / 1000000000000) (53847547407 / 1000000000000), orderedInterval (-21521347921 / 1000000000000) (-21521341469 / 1000000000000)))) (orderedInterval (-6518192669 / 1000000000000) (-6518192594 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 0) <| besselDerivativeNearFromState (632473483933707 / 4000000000000) 0 (IntervalRat.scale (219 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (61439558917 / 1000000000000) (61439560293 / 1000000000000), orderedInterval (-16049425888 / 1000000000000) (-16049424512 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 0) <| besselDerivativeNearFromState (558809504051847 / 4000000000000) 0 (IntervalRat.scale (219 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (52234204595 / 1000000000000) (52234294385 / 1000000000000), orderedInterval (-42948523826 / 1000000000000) (-42948434036 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 0) <| besselDerivativeNearFromState (161964774920853 / 800000000000) 0 (IntervalRat.scale (219 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (46025653023 / 1000000000000) (46025713383 / 1000000000000), orderedInterval (-32146775266 / 1000000000000) (-32146714906 / 1000000000000)))) (orderedInterval (-1101272829 / 1000000000000) (-1101266118 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate232_chunkChecks0_2 :
    compactCertificate232.chunkChecks (0 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 0) <| besselDerivativeNearFromState (448003091170191 / 4000000000000) 0 (IntervalRat.scale (219 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-23162776901 / 1000000000000) (-23162776370 / 1000000000000), orderedInterval (71850162482 / 1000000000000) (71850163013 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 0) <| besselDerivativeNearFromState (379777181883351 / 4000000000000) 0 (IntervalRat.scale (219 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (81551798085 / 1000000000000) (81551798093 / 1000000000000), orderedInterval (6946529327 / 1000000000000) (6946529335 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 0) <| besselDerivativeNearFromState (237646926802653 / 4000000000000) 0 (IntervalRat.scale (219 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-50059299454 / 1000000000000) (-50059299453 / 1000000000000), orderedInterval (-90185894264 / 1000000000000) (-90185894263 / 1000000000000)))) (orderedInterval (-2541969380 / 1000000000000) (-2541969267 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 0) <| besselDerivativeNearFromState (127807307612451 / 4000000000000) 0 (IntervalRat.scale (219 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (136637398711 / 1000000000000) (136637398712 / 1000000000000), orderedInterval (33252372761 / 1000000000000) (33252372762 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 0) <| besselDerivativeNearFromState (347021702230353 / 4000000000000) 0 (IntervalRat.scale (219 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-35336707984 / 1000000000000) (-35336705656 / 1000000000000), orderedInterval (78238865684 / 1000000000000) (78238868012 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 0) <| besselDerivativeNearFromState (473828466597681 / 4000000000000) 0 (IntervalRat.scale (219 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-10161619865 / 1000000000000) (-10161619817 / 1000000000000), orderedInterval (72644895770 / 1000000000000) (72644895818 / 1000000000000)))) (orderedInterval (-942571536 / 1000000000000) (-942571465 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 0) <| besselDerivativeNearFromState (200353073197347 / 4000000000000) 0 (IntervalRat.scale (219 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (64183623449 / 1000000000000) (64183623450 / 1000000000000), orderedInterval (92045079241 / 1000000000000) (92045079242 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 0) <| besselDerivativeNearFromState (814424119277187 / 4000000000000) 0 (IntervalRat.scale (219 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-10411668173 / 1000000000000) (-10411668172 / 1000000000000), orderedInterval (-54913757692 / 1000000000000) (-54913757691 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 0) <| besselDerivativeNearFromState (543997567953933 / 4000000000000) 0 (IntervalRat.scale (219 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-67887625123 / 1000000000000) (-67887624877 / 1000000000000), orderedInterval (8751841855 / 1000000000000) (8751842101 / 1000000000000)))) (orderedInterval (13971967492 / 1000000000000) (13971967569 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate232_chunkChecks0 :
    compactCertificate232.chunkChecks (0 : Fin 5) 0 9 = true :=
  compactCertificate232.chunkChecks_nine_of_three (0 : Fin 5) compactCertificate232_chunkChecks0_0
    compactCertificate232_chunkChecks0_1 compactCertificate232_chunkChecks0_2

theorem compactCertificate232_chunkChecks1_0 :
    compactCertificate232.chunkChecks (1 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 1) <| besselDerivativeNearFromState (219 / 2) 1 (IntervalRat.scale (219 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-24600528434 / 1000000000000) (-24600528433 / 1000000000000), orderedInterval (-72059280444 / 1000000000000) (-72059280443 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 1) <| besselDerivativeNearFromState (322628817590319 / 4000000000000) 1 (IntervalRat.scale (219 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-21148507674 / 1000000000000) (-21148507416 / 1000000000000), orderedInterval (86420038270 / 1000000000000) (86420038527 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 1) <| besselDerivativeNearFromState (104331530781327 / 800000000000) 1 (IntervalRat.scale (219 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-47524090904 / 1000000000000) (-47524044675 / 1000000000000), orderedInterval (51397208670 / 1000000000000) (51397254899 / 1000000000000)))) (orderedInterval (-24376510738 / 1000000000000) (-24376507496 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 1) <| besselDerivativeNearFromState (94142284325133 / 4000000000000) 1 (IntervalRat.scale (219 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-119907264057 / 1000000000000) (-119907163752 / 1000000000000), orderedInterval (115112293764 / 1000000000000) (115112394069 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 1) <| besselDerivativeNearFromState (252879417905001 / 4000000000000) 1 (IntervalRat.scale (219 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (92450616445 / 1000000000000) (92450616446 / 1000000000000), orderedInterval (38289345013 / 1000000000000) (38289345014 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 1) <| besselDerivativeNearFromState (686616811664517 / 4000000000000) 1 (IntervalRat.scale (219 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (20809150977 / 1000000000000) (20809151553 / 1000000000000), orderedInterval (-57294565204 / 1000000000000) (-57294564628 / 1000000000000)))) (orderedInterval (6923697794 / 1000000000000) (6923698107 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 1) <| besselDerivativeNearFromState (505758835810221 / 4000000000000) 1 (IntervalRat.scale (219 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (70953399060 / 1000000000000) (70953399094 / 1000000000000), orderedInterval (456230202 / 1000000000000) (456230236 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 1) <| besselDerivativeNearFromState (866626385544033 / 4000000000000) 1 (IntervalRat.scale (219 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-33726379039 / 1000000000000) (-33726379038 / 1000000000000), orderedInterval (-42359353187 / 1000000000000) (-42359353186 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 1) <| besselDerivativeNearFromState (638353073197347 / 4000000000000) 1 (IntervalRat.scale (219 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-9541956092 / 1000000000000) (-9541956091 / 1000000000000), orderedInterval (-62404940208 / 1000000000000) (-62404940207 / 1000000000000)))) (orderedInterval (387005037 / 1000000000000) (387005049 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate232_chunkChecks1_1 :
    compactCertificate232.chunkChecks (1 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 1) <| besselDerivativeNearFromState (979397774144781 / 4000000000000) 1 (IntervalRat.scale (219 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (28373592606 / 1000000000000) (28373592607 / 1000000000000), orderedInterval (42309347755 / 1000000000000) (42309347756 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 1) <| besselDerivativeNearFromState (565455568546149 / 4000000000000) 1 (IntervalRat.scale (219 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-47039213094 / 1000000000000) (-47039213093 / 1000000000000), orderedInterval (-47695138289 / 1000000000000) (-47695138288 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 1) <| besselDerivativeNearFromState (1003410829182441 / 4000000000000) 1 (IntervalRat.scale (219 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (15377214730 / 1000000000000) (15377214731 / 1000000000000), orderedInterval (47941929667 / 1000000000000) (47941929668 / 1000000000000)))) (orderedInterval (-5759632225 / 1000000000000) (-5759632133 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 1) <| besselDerivativeNearFromState (937516555651629 / 4000000000000) 1 (IntervalRat.scale (219 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (22924335164 / 1000000000000) (22924336580 / 1000000000000), orderedInterval (-46853552143 / 1000000000000) (-46853550727 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 1) <| besselDerivativeNearFromState (669056051463357 / 4000000000000) 1 (IntervalRat.scale (219 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-61671544899 / 1000000000000) (-61671544863 / 1000000000000), orderedInterval (-1453002584 / 1000000000000) (-1453002548 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 1) <| besselDerivativeNearFromState (758638253715003 / 4000000000000) 1 (IntervalRat.scale (219 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (53847540956 / 1000000000000) (53847547407 / 1000000000000), orderedInterval (-21521347921 / 1000000000000) (-21521341469 / 1000000000000)))) (orderedInterval (1789257314 / 1000000000000) (1789257452 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 1) <| besselDerivativeNearFromState (632473483933707 / 4000000000000) 1 (IntervalRat.scale (219 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (61439558917 / 1000000000000) (61439560293 / 1000000000000), orderedInterval (-16049425888 / 1000000000000) (-16049424512 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 1) <| besselDerivativeNearFromState (558809504051847 / 4000000000000) 1 (IntervalRat.scale (219 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (52234204595 / 1000000000000) (52234294385 / 1000000000000), orderedInterval (-42948523826 / 1000000000000) (-42948434036 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 1) <| besselDerivativeNearFromState (161964774920853 / 800000000000) 1 (IntervalRat.scale (219 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (46025653023 / 1000000000000) (46025713383 / 1000000000000), orderedInterval (-32146775266 / 1000000000000) (-32146714906 / 1000000000000)))) (orderedInterval (1346273798 / 1000000000000) (1346283250 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate232_chunkChecks1_2 :
    compactCertificate232.chunkChecks (1 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 1) <| besselDerivativeNearFromState (448003091170191 / 4000000000000) 1 (IntervalRat.scale (219 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-23162776901 / 1000000000000) (-23162776370 / 1000000000000), orderedInterval (71850162482 / 1000000000000) (71850163013 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 1) <| besselDerivativeNearFromState (379777181883351 / 4000000000000) 1 (IntervalRat.scale (219 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (81551798085 / 1000000000000) (81551798093 / 1000000000000), orderedInterval (6946529327 / 1000000000000) (6946529335 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 1) <| besselDerivativeNearFromState (237646926802653 / 4000000000000) 1 (IntervalRat.scale (219 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-50059299454 / 1000000000000) (-50059299453 / 1000000000000), orderedInterval (-90185894264 / 1000000000000) (-90185894263 / 1000000000000)))) (orderedInterval (-13684586468 / 1000000000000) (-13684586354 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 1) <| besselDerivativeNearFromState (127807307612451 / 4000000000000) 1 (IntervalRat.scale (219 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (136637398711 / 1000000000000) (136637398712 / 1000000000000), orderedInterval (33252372761 / 1000000000000) (33252372762 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 1) <| besselDerivativeNearFromState (347021702230353 / 4000000000000) 1 (IntervalRat.scale (219 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-35336707984 / 1000000000000) (-35336705656 / 1000000000000), orderedInterval (78238865684 / 1000000000000) (78238868012 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 1) <| besselDerivativeNearFromState (473828466597681 / 4000000000000) 1 (IntervalRat.scale (219 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-10161619865 / 1000000000000) (-10161619817 / 1000000000000), orderedInterval (72644895770 / 1000000000000) (72644895818 / 1000000000000)))) (orderedInterval (-7608310014 / 1000000000000) (-7608309956 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 1) <| besselDerivativeNearFromState (200353073197347 / 4000000000000) 1 (IntervalRat.scale (219 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (64183623449 / 1000000000000) (64183623450 / 1000000000000), orderedInterval (92045079241 / 1000000000000) (92045079242 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 1) <| besselDerivativeNearFromState (814424119277187 / 4000000000000) 1 (IntervalRat.scale (219 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-10411668173 / 1000000000000) (-10411668172 / 1000000000000), orderedInterval (-54913757692 / 1000000000000) (-54913757691 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 1) <| besselDerivativeNearFromState (543997567953933 / 4000000000000) 1 (IntervalRat.scale (219 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-67887625123 / 1000000000000) (-67887624877 / 1000000000000), orderedInterval (8751841855 / 1000000000000) (8751842101 / 1000000000000)))) (orderedInterval (6526082396 / 1000000000000) (6526082497 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate232_chunkChecks1 :
    compactCertificate232.chunkChecks (1 : Fin 5) 0 9 = true :=
  compactCertificate232.chunkChecks_nine_of_three (1 : Fin 5) compactCertificate232_chunkChecks1_0
    compactCertificate232_chunkChecks1_1 compactCertificate232_chunkChecks1_2

theorem compactCertificate232_chunkChecks2_0 :
    compactCertificate232.chunkChecks (2 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 2) <| besselDerivativeNearFromState (219 / 2) 2 (IntervalRat.scale (219 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-24600528434 / 1000000000000) (-24600528433 / 1000000000000), orderedInterval (-72059280444 / 1000000000000) (-72059280443 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 2) <| besselDerivativeNearFromState (322628817590319 / 4000000000000) 2 (IntervalRat.scale (219 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-21148507674 / 1000000000000) (-21148507416 / 1000000000000), orderedInterval (86420038270 / 1000000000000) (86420038527 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 2) <| besselDerivativeNearFromState (104331530781327 / 800000000000) 2 (IntervalRat.scale (219 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-47524090904 / 1000000000000) (-47524044675 / 1000000000000), orderedInterval (51397208670 / 1000000000000) (51397254899 / 1000000000000)))) (orderedInterval (14036130942 / 1000000000000) (14036134832 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 2) <| besselDerivativeNearFromState (94142284325133 / 4000000000000) 2 (IntervalRat.scale (219 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-119907264057 / 1000000000000) (-119907163752 / 1000000000000), orderedInterval (115112293764 / 1000000000000) (115112394069 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 2) <| besselDerivativeNearFromState (252879417905001 / 4000000000000) 2 (IntervalRat.scale (219 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (92450616445 / 1000000000000) (92450616446 / 1000000000000), orderedInterval (38289345013 / 1000000000000) (38289345014 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 2) <| besselDerivativeNearFromState (686616811664517 / 4000000000000) 2 (IntervalRat.scale (219 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (20809150977 / 1000000000000) (20809151553 / 1000000000000), orderedInterval (-57294565204 / 1000000000000) (-57294564628 / 1000000000000)))) (orderedInterval (2386801904 / 1000000000000) (2386802079 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 2) <| besselDerivativeNearFromState (505758835810221 / 4000000000000) 2 (IntervalRat.scale (219 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (70953399060 / 1000000000000) (70953399094 / 1000000000000), orderedInterval (456230202 / 1000000000000) (456230236 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 2) <| besselDerivativeNearFromState (866626385544033 / 4000000000000) 2 (IntervalRat.scale (219 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-33726379039 / 1000000000000) (-33726379038 / 1000000000000), orderedInterval (-42359353187 / 1000000000000) (-42359353186 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 2) <| besselDerivativeNearFromState (638353073197347 / 4000000000000) 2 (IntervalRat.scale (219 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-9541956092 / 1000000000000) (-9541956091 / 1000000000000), orderedInterval (-62404940208 / 1000000000000) (-62404940207 / 1000000000000)))) (orderedInterval (-3586148923 / 1000000000000) (-3586148903 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate232_chunkChecks2_1 :
    compactCertificate232.chunkChecks (2 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 2) <| besselDerivativeNearFromState (979397774144781 / 4000000000000) 2 (IntervalRat.scale (219 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (28373592606 / 1000000000000) (28373592607 / 1000000000000), orderedInterval (42309347755 / 1000000000000) (42309347756 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 2) <| besselDerivativeNearFromState (565455568546149 / 4000000000000) 2 (IntervalRat.scale (219 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-47039213094 / 1000000000000) (-47039213093 / 1000000000000), orderedInterval (-47695138289 / 1000000000000) (-47695138288 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 2) <| besselDerivativeNearFromState (1003410829182441 / 4000000000000) 2 (IntervalRat.scale (219 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (15377214730 / 1000000000000) (15377214731 / 1000000000000), orderedInterval (47941929667 / 1000000000000) (47941929668 / 1000000000000)))) (orderedInterval (19597184221 / 1000000000000) (19597184417 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 2) <| besselDerivativeNearFromState (937516555651629 / 4000000000000) 2 (IntervalRat.scale (219 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (22924335164 / 1000000000000) (22924336580 / 1000000000000), orderedInterval (-46853552143 / 1000000000000) (-46853550727 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 2) <| besselDerivativeNearFromState (669056051463357 / 4000000000000) 2 (IntervalRat.scale (219 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-61671544899 / 1000000000000) (-61671544863 / 1000000000000), orderedInterval (-1453002584 / 1000000000000) (-1453002548 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 2) <| besselDerivativeNearFromState (758638253715003 / 4000000000000) 2 (IntervalRat.scale (219 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (53847540956 / 1000000000000) (53847547407 / 1000000000000), orderedInterval (-21521347921 / 1000000000000) (-21521341469 / 1000000000000)))) (orderedInterval (16304865827 / 1000000000000) (16304866087 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 2) <| besselDerivativeNearFromState (632473483933707 / 4000000000000) 2 (IntervalRat.scale (219 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (61439558917 / 1000000000000) (61439560293 / 1000000000000), orderedInterval (-16049425888 / 1000000000000) (-16049424512 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 2) <| besselDerivativeNearFromState (558809504051847 / 4000000000000) 2 (IntervalRat.scale (219 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (52234204595 / 1000000000000) (52234294385 / 1000000000000), orderedInterval (-42948523826 / 1000000000000) (-42948434036 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 2) <| besselDerivativeNearFromState (161964774920853 / 800000000000) 2 (IntervalRat.scale (219 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (46025653023 / 1000000000000) (46025713383 / 1000000000000), orderedInterval (-32146775266 / 1000000000000) (-32146714906 / 1000000000000)))) (orderedInterval (-654584356 / 1000000000000) (-654570566 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate232_chunkChecks2_2 :
    compactCertificate232.chunkChecks (2 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 2) <| besselDerivativeNearFromState (448003091170191 / 4000000000000) 2 (IntervalRat.scale (219 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-23162776901 / 1000000000000) (-23162776370 / 1000000000000), orderedInterval (71850162482 / 1000000000000) (71850163013 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 2) <| besselDerivativeNearFromState (379777181883351 / 4000000000000) 2 (IntervalRat.scale (219 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (81551798085 / 1000000000000) (81551798093 / 1000000000000), orderedInterval (6946529327 / 1000000000000) (6946529335 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 2) <| besselDerivativeNearFromState (237646926802653 / 4000000000000) 2 (IntervalRat.scale (219 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-50059299454 / 1000000000000) (-50059299453 / 1000000000000), orderedInterval (-90185894264 / 1000000000000) (-90185894263 / 1000000000000)))) (orderedInterval (200319584 / 1000000000000) (200319699 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 2) <| besselDerivativeNearFromState (127807307612451 / 4000000000000) 2 (IntervalRat.scale (219 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (136637398711 / 1000000000000) (136637398712 / 1000000000000), orderedInterval (33252372761 / 1000000000000) (33252372762 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 2) <| besselDerivativeNearFromState (347021702230353 / 4000000000000) 2 (IntervalRat.scale (219 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-35336707984 / 1000000000000) (-35336705656 / 1000000000000), orderedInterval (78238865684 / 1000000000000) (78238868012 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 2) <| besselDerivativeNearFromState (473828466597681 / 4000000000000) 2 (IntervalRat.scale (219 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-10161619865 / 1000000000000) (-10161619817 / 1000000000000), orderedInterval (72644895770 / 1000000000000) (72644895818 / 1000000000000)))) (orderedInterval (-1130315517 / 1000000000000) (-1130315466 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 2) <| besselDerivativeNearFromState (200353073197347 / 4000000000000) 2 (IntervalRat.scale (219 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (64183623449 / 1000000000000) (64183623450 / 1000000000000), orderedInterval (92045079241 / 1000000000000) (92045079242 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 2) <| besselDerivativeNearFromState (814424119277187 / 4000000000000) 2 (IntervalRat.scale (219 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-10411668173 / 1000000000000) (-10411668172 / 1000000000000), orderedInterval (-54913757692 / 1000000000000) (-54913757691 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 2) <| besselDerivativeNearFromState (543997567953933 / 4000000000000) 2 (IntervalRat.scale (219 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-67887625123 / 1000000000000) (-67887624877 / 1000000000000), orderedInterval (8751841855 / 1000000000000) (8751842101 / 1000000000000)))) (orderedInterval (-22719377232 / 1000000000000) (-22719377097 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate232_chunkChecks2 :
    compactCertificate232.chunkChecks (2 : Fin 5) 0 9 = true :=
  compactCertificate232.chunkChecks_nine_of_three (2 : Fin 5) compactCertificate232_chunkChecks2_0
    compactCertificate232_chunkChecks2_1 compactCertificate232_chunkChecks2_2

theorem compactCertificate232_chunkChecks3_0 :
    compactCertificate232.chunkChecks (3 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 3) <| besselDerivativeNearFromState (219 / 2) 3 (IntervalRat.scale (219 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-24600528434 / 1000000000000) (-24600528433 / 1000000000000), orderedInterval (-72059280444 / 1000000000000) (-72059280443 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 3) <| besselDerivativeNearFromState (322628817590319 / 4000000000000) 3 (IntervalRat.scale (219 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-21148507674 / 1000000000000) (-21148507416 / 1000000000000), orderedInterval (86420038270 / 1000000000000) (86420038527 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 3) <| besselDerivativeNearFromState (104331530781327 / 800000000000) 3 (IntervalRat.scale (219 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-47524090904 / 1000000000000) (-47524044675 / 1000000000000), orderedInterval (51397208670 / 1000000000000) (51397254899 / 1000000000000)))) (orderedInterval (23014392164 / 1000000000000) (23014396795 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 3) <| besselDerivativeNearFromState (94142284325133 / 4000000000000) 3 (IntervalRat.scale (219 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-119907264057 / 1000000000000) (-119907163752 / 1000000000000), orderedInterval (115112293764 / 1000000000000) (115112394069 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 3) <| besselDerivativeNearFromState (252879417905001 / 4000000000000) 3 (IntervalRat.scale (219 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (92450616445 / 1000000000000) (92450616446 / 1000000000000), orderedInterval (38289345013 / 1000000000000) (38289345014 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 3) <| besselDerivativeNearFromState (686616811664517 / 4000000000000) 3 (IntervalRat.scale (219 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (20809150977 / 1000000000000) (20809151553 / 1000000000000), orderedInterval (-57294565204 / 1000000000000) (-57294564628 / 1000000000000)))) (orderedInterval (-15968508302 / 1000000000000) (-15968508100 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 3) <| besselDerivativeNearFromState (505758835810221 / 4000000000000) 3 (IntervalRat.scale (219 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (70953399060 / 1000000000000) (70953399094 / 1000000000000), orderedInterval (456230202 / 1000000000000) (456230236 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 3) <| besselDerivativeNearFromState (866626385544033 / 4000000000000) 3 (IntervalRat.scale (219 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-33726379039 / 1000000000000) (-33726379038 / 1000000000000), orderedInterval (-42359353187 / 1000000000000) (-42359353186 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 3) <| besselDerivativeNearFromState (638353073197347 / 4000000000000) 3 (IntervalRat.scale (219 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-9541956092 / 1000000000000) (-9541956091 / 1000000000000), orderedInterval (-62404940208 / 1000000000000) (-62404940207 / 1000000000000)))) (orderedInterval (-5418552435 / 1000000000000) (-5418552399 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate232_chunkChecks3_1 :
    compactCertificate232.chunkChecks (3 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 3) <| besselDerivativeNearFromState (979397774144781 / 4000000000000) 3 (IntervalRat.scale (219 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (28373592606 / 1000000000000) (28373592607 / 1000000000000), orderedInterval (42309347755 / 1000000000000) (42309347756 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 3) <| besselDerivativeNearFromState (565455568546149 / 4000000000000) 3 (IntervalRat.scale (219 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-47039213094 / 1000000000000) (-47039213093 / 1000000000000), orderedInterval (-47695138289 / 1000000000000) (-47695138288 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 3) <| besselDerivativeNearFromState (1003410829182441 / 4000000000000) 3 (IntervalRat.scale (219 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (15377214730 / 1000000000000) (15377214731 / 1000000000000), orderedInterval (47941929667 / 1000000000000) (47941929668 / 1000000000000)))) (orderedInterval (9536641866 / 1000000000000) (9536642293 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 3) <| besselDerivativeNearFromState (937516555651629 / 4000000000000) 3 (IntervalRat.scale (219 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (22924335164 / 1000000000000) (22924336580 / 1000000000000), orderedInterval (-46853552143 / 1000000000000) (-46853550727 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 3) <| besselDerivativeNearFromState (669056051463357 / 4000000000000) 3 (IntervalRat.scale (219 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-61671544899 / 1000000000000) (-61671544863 / 1000000000000), orderedInterval (-1453002584 / 1000000000000) (-1453002548 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 3) <| besselDerivativeNearFromState (758638253715003 / 4000000000000) 3 (IntervalRat.scale (219 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (53847540956 / 1000000000000) (53847547407 / 1000000000000), orderedInterval (-21521347921 / 1000000000000) (-21521341469 / 1000000000000)))) (orderedInterval (-8519792810 / 1000000000000) (-8519792315 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 3) <| besselDerivativeNearFromState (632473483933707 / 4000000000000) 3 (IntervalRat.scale (219 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (61439558917 / 1000000000000) (61439560293 / 1000000000000), orderedInterval (-16049425888 / 1000000000000) (-16049424512 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 3) <| besselDerivativeNearFromState (558809504051847 / 4000000000000) 3 (IntervalRat.scale (219 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (52234204595 / 1000000000000) (52234294385 / 1000000000000), orderedInterval (-42948523826 / 1000000000000) (-42948434036 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 3) <| besselDerivativeNearFromState (161964774920853 / 800000000000) 3 (IntervalRat.scale (219 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (46025653023 / 1000000000000) (46025713383 / 1000000000000), orderedInterval (-32146775266 / 1000000000000) (-32146714906 / 1000000000000)))) (orderedInterval (662331967 / 1000000000000) (662352612 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate232_chunkChecks3_2 :
    compactCertificate232.chunkChecks (3 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 3) <| besselDerivativeNearFromState (448003091170191 / 4000000000000) 3 (IntervalRat.scale (219 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-23162776901 / 1000000000000) (-23162776370 / 1000000000000), orderedInterval (71850162482 / 1000000000000) (71850163013 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 3) <| besselDerivativeNearFromState (379777181883351 / 4000000000000) 3 (IntervalRat.scale (219 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (81551798085 / 1000000000000) (81551798093 / 1000000000000), orderedInterval (6946529327 / 1000000000000) (6946529335 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 3) <| besselDerivativeNearFromState (237646926802653 / 4000000000000) 3 (IntervalRat.scale (219 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-50059299454 / 1000000000000) (-50059299453 / 1000000000000), orderedInterval (-90185894264 / 1000000000000) (-90185894263 / 1000000000000)))) (orderedInterval (13015811248 / 1000000000000) (13015811364 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 3) <| besselDerivativeNearFromState (127807307612451 / 4000000000000) 3 (IntervalRat.scale (219 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (136637398711 / 1000000000000) (136637398712 / 1000000000000), orderedInterval (33252372761 / 1000000000000) (33252372762 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 3) <| besselDerivativeNearFromState (347021702230353 / 4000000000000) 3 (IntervalRat.scale (219 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-35336707984 / 1000000000000) (-35336705656 / 1000000000000), orderedInterval (78238865684 / 1000000000000) (78238868012 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 3) <| besselDerivativeNearFromState (473828466597681 / 4000000000000) 3 (IntervalRat.scale (219 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-10161619865 / 1000000000000) (-10161619817 / 1000000000000), orderedInterval (72644895770 / 1000000000000) (72644895818 / 1000000000000)))) (orderedInterval (7956184501 / 1000000000000) (7956184545 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 3) <| besselDerivativeNearFromState (200353073197347 / 4000000000000) 3 (IntervalRat.scale (219 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (64183623449 / 1000000000000) (64183623450 / 1000000000000), orderedInterval (92045079241 / 1000000000000) (92045079242 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 3) <| besselDerivativeNearFromState (814424119277187 / 4000000000000) 3 (IntervalRat.scale (219 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-10411668173 / 1000000000000) (-10411668172 / 1000000000000), orderedInterval (-54913757692 / 1000000000000) (-54913757691 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 3) <| besselDerivativeNearFromState (543997567953933 / 4000000000000) 3 (IntervalRat.scale (219 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-67887625123 / 1000000000000) (-67887624877 / 1000000000000), orderedInterval (8751841855 / 1000000000000) (8751842101 / 1000000000000)))) (orderedInterval (-25436265467 / 1000000000000) (-25436265279 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate232_chunkChecks3 :
    compactCertificate232.chunkChecks (3 : Fin 5) 0 9 = true :=
  compactCertificate232.chunkChecks_nine_of_three (3 : Fin 5) compactCertificate232_chunkChecks3_0
    compactCertificate232_chunkChecks3_1 compactCertificate232_chunkChecks3_2

theorem compactCertificate232_chunkChecks4_0 :
    compactCertificate232.chunkChecks (4 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 4) <| besselDerivativeNearFromState (219 / 2) 4 (IntervalRat.scale (219 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-24600528434 / 1000000000000) (-24600528433 / 1000000000000), orderedInterval (-72059280444 / 1000000000000) (-72059280443 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 4) <| besselDerivativeNearFromState (322628817590319 / 4000000000000) 4 (IntervalRat.scale (219 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-21148507674 / 1000000000000) (-21148507416 / 1000000000000), orderedInterval (86420038270 / 1000000000000) (86420038527 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 4) <| besselDerivativeNearFromState (104331530781327 / 800000000000) 4 (IntervalRat.scale (219 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-47524090904 / 1000000000000) (-47524044675 / 1000000000000), orderedInterval (51397208670 / 1000000000000) (51397254899 / 1000000000000)))) (orderedInterval (-15839198215 / 1000000000000) (-15839192659 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 4) <| besselDerivativeNearFromState (94142284325133 / 4000000000000) 4 (IntervalRat.scale (219 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-119907264057 / 1000000000000) (-119907163752 / 1000000000000), orderedInterval (115112293764 / 1000000000000) (115112394069 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 4) <| besselDerivativeNearFromState (252879417905001 / 4000000000000) 4 (IntervalRat.scale (219 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (92450616445 / 1000000000000) (92450616446 / 1000000000000), orderedInterval (38289345013 / 1000000000000) (38289345014 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 4) <| besselDerivativeNearFromState (686616811664517 / 4000000000000) 4 (IntervalRat.scale (219 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (20809150977 / 1000000000000) (20809151553 / 1000000000000), orderedInterval (-57294565204 / 1000000000000) (-57294564628 / 1000000000000)))) (orderedInterval (-8263815304 / 1000000000000) (-8263815003 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 4) <| besselDerivativeNearFromState (505758835810221 / 4000000000000) 4 (IntervalRat.scale (219 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (70953399060 / 1000000000000) (70953399094 / 1000000000000), orderedInterval (456230202 / 1000000000000) (456230236 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 4) <| besselDerivativeNearFromState (866626385544033 / 4000000000000) 4 (IntervalRat.scale (219 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-33726379039 / 1000000000000) (-33726379038 / 1000000000000), orderedInterval (-42359353187 / 1000000000000) (-42359353186 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 4) <| besselDerivativeNearFromState (638353073197347 / 4000000000000) 4 (IntervalRat.scale (219 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-9541956092 / 1000000000000) (-9541956091 / 1000000000000), orderedInterval (-62404940208 / 1000000000000) (-62404940207 / 1000000000000)))) (orderedInterval (15001265685 / 1000000000000) (15001265750 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate232_chunkChecks4_1 :
    compactCertificate232.chunkChecks (4 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 4) <| besselDerivativeNearFromState (979397774144781 / 4000000000000) 4 (IntervalRat.scale (219 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (28373592606 / 1000000000000) (28373592607 / 1000000000000), orderedInterval (42309347755 / 1000000000000) (42309347756 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 4) <| besselDerivativeNearFromState (565455568546149 / 4000000000000) 4 (IntervalRat.scale (219 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-47039213094 / 1000000000000) (-47039213093 / 1000000000000), orderedInterval (-47695138289 / 1000000000000) (-47695138288 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 4) <| besselDerivativeNearFromState (1003410829182441 / 4000000000000) 4 (IntervalRat.scale (219 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (15377214730 / 1000000000000) (15377214731 / 1000000000000), orderedInterval (47941929667 / 1000000000000) (47941929668 / 1000000000000)))) (orderedInterval (-75685854853 / 1000000000000) (-75685853905 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 4) <| besselDerivativeNearFromState (937516555651629 / 4000000000000) 4 (IntervalRat.scale (219 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (22924335164 / 1000000000000) (22924336580 / 1000000000000), orderedInterval (-46853552143 / 1000000000000) (-46853550727 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 4) <| besselDerivativeNearFromState (669056051463357 / 4000000000000) 4 (IntervalRat.scale (219 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-61671544899 / 1000000000000) (-61671544863 / 1000000000000), orderedInterval (-1453002584 / 1000000000000) (-1453002548 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 4) <| besselDerivativeNearFromState (758638253715003 / 4000000000000) 4 (IntervalRat.scale (219 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (53847540956 / 1000000000000) (53847547407 / 1000000000000), orderedInterval (-21521347921 / 1000000000000) (-21521341469 / 1000000000000)))) (orderedInterval (-42733598502 / 1000000000000) (-42733597541 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 4) <| besselDerivativeNearFromState (632473483933707 / 4000000000000) 4 (IntervalRat.scale (219 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (61439558917 / 1000000000000) (61439560293 / 1000000000000), orderedInterval (-16049425888 / 1000000000000) (-16049424512 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 4) <| besselDerivativeNearFromState (558809504051847 / 4000000000000) 4 (IntervalRat.scale (219 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (52234204595 / 1000000000000) (52234294385 / 1000000000000), orderedInterval (-42948523826 / 1000000000000) (-42948434036 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 4) <| besselDerivativeNearFromState (161964774920853 / 800000000000) 4 (IntervalRat.scale (219 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (46025653023 / 1000000000000) (46025713383 / 1000000000000), orderedInterval (-32146775266 / 1000000000000) (-32146714906 / 1000000000000)))) (orderedInterval (8924018319 / 1000000000000) (8924050489 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate232_chunkChecks4_2 :
    compactCertificate232.chunkChecks (4 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 4) <| besselDerivativeNearFromState (448003091170191 / 4000000000000) 4 (IntervalRat.scale (219 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-23162776901 / 1000000000000) (-23162776370 / 1000000000000), orderedInterval (71850162482 / 1000000000000) (71850163013 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 4) <| besselDerivativeNearFromState (379777181883351 / 4000000000000) 4 (IntervalRat.scale (219 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (81551798085 / 1000000000000) (81551798093 / 1000000000000), orderedInterval (6946529327 / 1000000000000) (6946529335 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 4) <| besselDerivativeNearFromState (237646926802653 / 4000000000000) 4 (IntervalRat.scale (219 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-50059299454 / 1000000000000) (-50059299453 / 1000000000000), orderedInterval (-90185894264 / 1000000000000) (-90185894263 / 1000000000000)))) (orderedInterval (1065743290 / 1000000000000) (1065743408 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 4) <| besselDerivativeNearFromState (127807307612451 / 4000000000000) 4 (IntervalRat.scale (219 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (136637398711 / 1000000000000) (136637398712 / 1000000000000), orderedInterval (33252372761 / 1000000000000) (33252372762 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 4) <| besselDerivativeNearFromState (347021702230353 / 4000000000000) 4 (IntervalRat.scale (219 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-35336707984 / 1000000000000) (-35336705656 / 1000000000000), orderedInterval (78238865684 / 1000000000000) (78238868012 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 4) <| besselDerivativeNearFromState (473828466597681 / 4000000000000) 4 (IntervalRat.scale (219 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-10161619865 / 1000000000000) (-10161619817 / 1000000000000), orderedInterval (72644895770 / 1000000000000) (72644895818 / 1000000000000)))) (orderedInterval (1218784373 / 1000000000000) (1218784413 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 4) <| besselDerivativeNearFromState (200353073197347 / 4000000000000) 4 (IntervalRat.scale (219 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (64183623449 / 1000000000000) (64183623450 / 1000000000000), orderedInterval (92045079241 / 1000000000000) (92045079242 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 4) <| besselDerivativeNearFromState (814424119277187 / 4000000000000) 4 (IntervalRat.scale (219 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-10411668173 / 1000000000000) (-10411668172 / 1000000000000), orderedInterval (-54913757692 / 1000000000000) (-54913757691 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 4) <| besselDerivativeNearFromState (543997567953933 / 4000000000000) 4 (IntervalRat.scale (219 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-67887625123 / 1000000000000) (-67887624877 / 1000000000000), orderedInterval (8751841855 / 1000000000000) (8751842101 / 1000000000000)))) (orderedInterval (40920138442 / 1000000000000) (40920138711 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate232_chunkChecks4 :
    compactCertificate232.chunkChecks (4 : Fin 5) 0 9 = true :=
  compactCertificate232.chunkChecks_nine_of_three (4 : Fin 5) compactCertificate232_chunkChecks4_0
    compactCertificate232_chunkChecks4_1 compactCertificate232_chunkChecks4_2

theorem compactCertificate232_chunks :
    ∀ r : Fin 5, ∀ b, compactCertificate232.chunkCheck r b = true :=
  compactCertificate232.chunkChecks_all (by
    intro r
    fin_cases r
    · exact compactCertificate232_chunkChecks0
    · exact compactCertificate232_chunkChecks1
    · exact compactCertificate232_chunkChecks2
    · exact compactCertificate232_chunkChecks3
    · exact compactCertificate232_chunkChecks4)

theorem compactCertificate232_coefficient0 :
    compactCertificate232.coefficientCheck (0 : Fin 5) = true := by
  norm_num [CompactCertificate.coefficientCheck, intervalFinSumHull,
    compactCertificate232, rationalIntervalSubset, orderedInterval, Fin.sum_univ_succ]

theorem compactCertificate232_coefficient1 :
    compactCertificate232.coefficientCheck (1 : Fin 5) = true := by
  norm_num [CompactCertificate.coefficientCheck, intervalFinSumHull,
    compactCertificate232, rationalIntervalSubset, orderedInterval, Fin.sum_univ_succ]

theorem compactCertificate232_coefficient2 :
    compactCertificate232.coefficientCheck (2 : Fin 5) = true := by
  norm_num [CompactCertificate.coefficientCheck, intervalFinSumHull,
    compactCertificate232, rationalIntervalSubset, orderedInterval, Fin.sum_univ_succ]

theorem compactCertificate232_coefficient3 :
    compactCertificate232.coefficientCheck (3 : Fin 5) = true := by
  norm_num [CompactCertificate.coefficientCheck, intervalFinSumHull,
    compactCertificate232, rationalIntervalSubset, orderedInterval, Fin.sum_univ_succ]

theorem compactCertificate232_coefficient4 :
    compactCertificate232.coefficientCheck (4 : Fin 5) = true := by
  norm_num [CompactCertificate.coefficientCheck, intervalFinSumHull,
    compactCertificate232, rationalIntervalSubset, orderedInterval, Fin.sum_univ_succ]

theorem compactCertificate232_coefficients : ∀ r : Fin 5,
    compactCertificate232.coefficientCheck r = true := by
  intro r
  fin_cases r
  · exact compactCertificate232_coefficient0
  · exact compactCertificate232_coefficient1
  · exact compactCertificate232_coefficient2
  · exact compactCertificate232_coefficient3
  · exact compactCertificate232_coefficient4

theorem compactCertificate232_lower : (1 : ℚ) ≤ compactCertificate232.output.lo := by
  norm_num [CompactCertificate.output, CompactCertificate.interval,
    CompactCertificate.coefficientTargetNat, compactCertificate232, dualConstant,
    intervalTaylorSum, intervalPow, intervalSub, intervalMaxAbs, widenInterval,
    rationalErrorInterval, orderedInterval, IntervalRat.add, IntervalRat.mul, IntervalRat.scale,
    IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4]

theorem compactCertificate232_proves {t : ℝ} (ht : t ∈ compactCertificate232.interval) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t :=
  compactCertificate232.proves compactCertificate232_states compactCertificate232_chunks
    compactCertificate232_coefficients compactCertificate232_lower ht

end Erdos232
