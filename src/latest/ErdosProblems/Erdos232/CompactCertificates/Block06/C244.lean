/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, OpenAI Codex
-/
import ErdosProblems.Erdos232.CompactBase

open LeanCert.Core
namespace Erdos232

def compactCertificate244 : CompactCertificate where
  left := 119
  right := 120
  center := 239 / 2
  grid := fun i =>
    match i.val with
    | 0 => 38
    | 1 => 28
    | 2 => 45
    | 3 => 8
    | 4 => 22
    | 5 => 60
    | 6 => 44
    | 7 => 75
    | 8 => 55
    | 9 => 85
    | 10 => 49
    | 11 => 87
    | 12 => 81
    | 13 => 58
    | 14 => 66
    | 15 => 55
    | 16 => 49
    | 17 => 70
    | 18 => 39
    | 19 => 33
    | 20 => 21
    | 21 => 11
    | 22 => 30
    | 23 => 41
    | 24 => 17
    | 25 => 71
    | _ => 47
  point := fun i =>
    match i.val with
    | 0 => 239 / 2
    | 1 => 352092636548339 / 4000000000000
    | 2 => 113859524459987 / 800000000000
    | 3 => 102739753213273 / 4000000000000
    | 4 => 275973428672581 / 4000000000000
    | 5 => 749321543323377 / 4000000000000
    | 6 => 551946857345401 / 4000000000000
    | 7 => 945770347694173 / 4000000000000
    | 8 => 696650157507607 / 4000000000000
    | 9 => 1068840493244761 / 4000000000000
    | 10 => 617095346495569 / 4000000000000
    | 11 => 1095046521345221 / 4000000000000
    | 12 => 1023134505939449 / 4000000000000
    | 13 => 730157060729417 / 4000000000000
    | 14 => 827920286017743 / 4000000000000
    | 15 => 690233619452767 / 4000000000000
    | 16 => 609842335472107 / 4000000000000
    | 17 => 176756078566593 / 800000000000
    | 18 => 488916615477971 / 4000000000000
    | 19 => 414460029543931 / 4000000000000
    | 20 => 259349842492393 / 4000000000000
    | 21 => 139479207851031 / 4000000000000
    | 22 => 378713181886093 / 4000000000000
    | 23 => 517100472679661 / 4000000000000
    | 24 => 218650157507607 / 4000000000000
    | 25 => 888800751174647 / 4000000000000
    | _ => 593677711146073 / 4000000000000
  state := fun i =>
    match i.val with
    | 0 => (orderedInterval (57347235040 / 1000000000000) (57347235041 / 1000000000000), orderedInterval (44911423080 / 1000000000000) (44911423081 / 1000000000000))
    | 1 => (orderedInterval (63470757745 / 1000000000000) (63470757746 / 1000000000000), orderedInterval (56242143531 / 1000000000000) (56242143532 / 1000000000000))
    | 2 => (orderedInterval (-65955974271 / 1000000000000) (-65955973830 / 1000000000000), orderedInterval (11313332022 / 1000000000000) (11313332463 / 1000000000000))
    | 3 => (orderedInterval (152980129364 / 1000000000000) (152980129365 / 1000000000000), orderedInterval (34153151836 / 1000000000000) (34153151837 / 1000000000000))
    | 4 => (orderedInterval (59038878557 / 1000000000000) (59038878558 / 1000000000000), orderedInterval (75346379827 / 1000000000000) (75346379828 / 1000000000000))
    | 5 => (orderedInterval (-21646954194 / 1000000000000) (-21646953423 / 1000000000000), orderedInterval (54185383425 / 1000000000000) (54185384197 / 1000000000000))
    | 6 => (orderedInterval (34987714451 / 1000000000000) (34987714452 / 1000000000000), orderedInterval (58092677681 / 1000000000000) (58092677682 / 1000000000000))
    | 7 => (orderedInterval (-51853249783 / 1000000000000) (-51853249634 / 1000000000000), orderedInterval (2040062989 / 1000000000000) (2040063139 / 1000000000000))
    | 8 => (orderedInterval (-50277363460 / 1000000000000) (-50277318466 / 1000000000000), orderedInterval (33722625377 / 1000000000000) (33722670372 / 1000000000000))
    | 9 => (orderedInterval (-39976134849 / 1000000000000) (-39976134848 / 1000000000000), orderedInterval (-27931910625 / 1000000000000) (-27931910624 / 1000000000000))
    | 10 => (orderedInterval (-57831512491 / 1000000000000) (-57831512490 / 1000000000000), orderedInterval (-27777900096 / 1000000000000) (-27777900095 / 1000000000000))
    | 11 => (orderedInterval (-45417404450 / 1000000000000) (-45417404448 / 1000000000000), orderedInterval (-16125357797 / 1000000000000) (-16125357796 / 1000000000000))
    | 12 => (orderedInterval (-43076326606 / 1000000000000) (-43076288616 / 1000000000000), orderedInterval (25250212416 / 1000000000000) (25250250407 / 1000000000000))
    | 13 => (orderedInterval (52938094687 / 1000000000000) (52938094688 / 1000000000000), orderedInterval (26029933850 / 1000000000000) (26029933851 / 1000000000000))
    | 14 => (orderedInterval (22601520419 / 1000000000000) (22601520420 / 1000000000000), orderedInterval (50590552005 / 1000000000000) (50590552006 / 1000000000000))
    | 15 => (orderedInterval (-32031178069 / 1000000000000) (-32031178068 / 1000000000000), orderedInterval (-51514462796 / 1000000000000) (-51514462795 / 1000000000000))
    | 16 => (orderedInterval (41275624461 / 1000000000000) (41275649817 / 1000000000000), orderedInterval (-49854195078 / 1000000000000) (-49854169722 / 1000000000000))
    | 17 => (orderedInterval (52040482928 / 1000000000000) (52040484798 / 1000000000000), orderedInterval (-13275647815 / 1000000000000) (-13275645945 / 1000000000000))
    | 18 => (orderedInterval (-34054738735 / 1000000000000) (-34054738734 / 1000000000000), orderedInterval (-63490175822 / 1000000000000) (-63490175821 / 1000000000000))
    | 19 => (orderedInterval (-52075308464 / 1000000000000) (-52075308463 / 1000000000000), orderedInterval (-58334199001 / 1000000000000) (-58334199000 / 1000000000000))
    | 20 => (orderedInterval (34210974102 / 1000000000000) (34210975246 / 1000000000000), orderedInterval (-93261303332 / 1000000000000) (-93261302189 / 1000000000000))
    | 21 => (orderedInterval (-120048736229 / 1000000000000) (-120048736228 / 1000000000000), orderedInterval (-60281124518 / 1000000000000) (-60281124517 / 1000000000000))
    | 22 => (orderedInterval (76852322953 / 1000000000000) (76852322954 / 1000000000000), orderedInterval (28189260451 / 1000000000000) (28189260452 / 1000000000000))
    | 23 => (orderedInterval (-66688227257 / 1000000000000) (-66688227256 / 1000000000000), orderedInterval (-21586639242 / 1000000000000) (-21586639241 / 1000000000000))
    | 24 => (orderedInterval (-96322815620 / 1000000000000) (-96322807459 / 1000000000000), orderedInterval (49542986546 / 1000000000000) (49542994706 / 1000000000000))
    | 25 => (orderedInterval (3639921639 / 1000000000000) (3639921647 / 1000000000000), orderedInterval (-53410730037 / 1000000000000) (-53410730030 / 1000000000000))
    | _ => (orderedInterval (-65477411266 / 1000000000000) (-65477411232 / 1000000000000), orderedInterval (-1198367915 / 1000000000000) (-1198367881 / 1000000000000))
  chunkTarget := fun r b =>
    match r.val with
    | 0 =>
      match b.val with
      | 0 => orderedInterval (19451488980 / 1000000000000) (19451489015 / 1000000000000)
      | 1 => orderedInterval (2034760737 / 1000000000000) (2034760807 / 1000000000000)
      | 2 => orderedInterval (384257002 / 1000000000000) (384258102 / 1000000000000)
      | 3 => orderedInterval (-3637914355 / 1000000000000) (-3637914307 / 1000000000000)
      | 4 => orderedInterval (5669261178 / 1000000000000) (5669261879 / 1000000000000)
      | 5 => orderedInterval (-1399511837 / 1000000000000) (-1399510326 / 1000000000000)
      | 6 => orderedInterval (9506303023 / 1000000000000) (9506303091 / 1000000000000)
      | 7 => orderedInterval (5584086287 / 1000000000000) (5584086302 / 1000000000000)
      | _ => orderedInterval (11408337633 / 1000000000000) (11408337723 / 1000000000000)
    | 1 =>
      match b.val with
      | 0 => orderedInterval (18978021389 / 1000000000000) (18978021430 / 1000000000000)
      | 1 => orderedInterval (-4529831675 / 1000000000000) (-4529831572 / 1000000000000)
      | 2 => orderedInterval (1063315879 / 1000000000000) (1063317485 / 1000000000000)
      | 3 => orderedInterval (3189510969 / 1000000000000) (3189511069 / 1000000000000)
      | 4 => orderedInterval (2340802338 / 1000000000000) (2340803830 / 1000000000000)
      | 5 => orderedInterval (2152442576 / 1000000000000) (2152444533 / 1000000000000)
      | 6 => orderedInterval (11598931805 / 1000000000000) (11598931854 / 1000000000000)
      | 7 => orderedInterval (1607815015 / 1000000000000) (1607815029 / 1000000000000)
      | _ => orderedInterval (8500109579 / 1000000000000) (8500109657 / 1000000000000)
    | 2 =>
      match b.val with
      | 0 => orderedInterval (-17720097642 / 1000000000000) (-17720097593 / 1000000000000)
      | 1 => orderedInterval (-4385626486 / 1000000000000) (-4385626328 / 1000000000000)
      | 2 => orderedInterval (-3689171941 / 1000000000000) (-3689169578 / 1000000000000)
      | 3 => orderedInterval (5482469901 / 1000000000000) (5482470115 / 1000000000000)
      | 4 => orderedInterval (-14919941837 / 1000000000000) (-14919938643 / 1000000000000)
      | 5 => orderedInterval (43108277 / 1000000000000) (43110844 / 1000000000000)
      | 6 => orderedInterval (-8337517153 / 1000000000000) (-8337517114 / 1000000000000)
      | 7 => orderedInterval (-5089002307 / 1000000000000) (-5089002293 / 1000000000000)
      | _ => orderedInterval (-17876179970 / 1000000000000) (-17876179878 / 1000000000000)
    | 3 =>
      match b.val with
      | 0 => orderedInterval (-18982711354 / 1000000000000) (-18982711296 / 1000000000000)
      | 1 => orderedInterval (14349790449 / 1000000000000) (14349790696 / 1000000000000)
      | 2 => orderedInterval (-2004688807 / 1000000000000) (-2004685347 / 1000000000000)
      | 3 => orderedInterval (-23546578586 / 1000000000000) (-23546578120 / 1000000000000)
      | 4 => orderedInterval (-2847653360 / 1000000000000) (-2847646542 / 1000000000000)
      | 5 => orderedInterval (-1985430514 / 1000000000000) (-1985427139 / 1000000000000)
      | 6 => orderedInterval (-12459906318 / 1000000000000) (-12459906285 / 1000000000000)
      | 7 => orderedInterval (-1761374663 / 1000000000000) (-1761374649 / 1000000000000)
      | _ => orderedInterval (-28259828607 / 1000000000000) (-28259828480 / 1000000000000)
    | _ =>
      match b.val with
      | 0 => orderedInterval (15433484088 / 1000000000000) (15433484157 / 1000000000000)
      | 1 => orderedInterval (9288682853 / 1000000000000) (9288683241 / 1000000000000)
      | 2 => orderedInterval (19062964844 / 1000000000000) (19062969947 / 1000000000000)
      | 3 => orderedInterval (-11756296467 / 1000000000000) (-11756295429 / 1000000000000)
      | 4 => orderedInterval (42595333214 / 1000000000000) (42595347836 / 1000000000000)
      | 5 => orderedInterval (7737721465 / 1000000000000) (7737725985 / 1000000000000)
      | 6 => orderedInterval (7930252206 / 1000000000000) (7930252236 / 1000000000000)
      | 7 => orderedInterval (6357997600 / 1000000000000) (6357997615 / 1000000000000)
      | _ => orderedInterval (26137675897 / 1000000000000) (26137676094 / 1000000000000)
  coefficientTarget := fun i =>
    match i.val with
    | 0 => orderedInterval (49001068648 / 1000000000000) (49001072286 / 1000000000000)
    | 1 => orderedInterval (44901117875 / 1000000000000) (44901123315 / 1000000000000)
    | 2 => orderedInterval (-66491959158 / 1000000000000) (-66491950468 / 1000000000000)
    | 3 => orderedInterval (-77498381760 / 1000000000000) (-77498367162 / 1000000000000)
    | _ => orderedInterval (122787815700 / 1000000000000) (122787841682 / 1000000000000)

theorem compactCertificate244_stateChecks0 :
    compactCertificate244.stateChecks 0 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 38 12 (239 / 2)) (orderedInterval (57347235040 / 1000000000000) (57347235041 / 1000000000000), orderedInterval (44911423080 / 1000000000000) (44911423081 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 28 12 (352092636548339 / 4000000000000)) (orderedInterval (63470757745 / 1000000000000) (63470757746 / 1000000000000), orderedInterval (56242143531 / 1000000000000) (56242143532 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 45 12 (113859524459987 / 800000000000)) (orderedInterval (-65955974271 / 1000000000000) (-65955973830 / 1000000000000), orderedInterval (11313332022 / 1000000000000) (11313332463 / 1000000000000))) = true
  norm_num [besselStateAtRationalPoint, besselIntervalStepZero,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, besselZeroTransition,
    besselInitial, besselGridStateAt, besselGridStateBlock00, besselGridStateBlock01,
    besselGridStateBlock02, besselGridStateBlock03, besselGridStateBlock04,
    besselGridStateBlock05, besselGridStateBlock06, besselGridStateBlock07,
    besselGridStateBlock08, besselGridStateBlock09, besselGridStateBlock10,
    besselGridStateBlock11, besselGridStateBlock12, besselGridStateBlock13,
    besselGridStateBlock14, besselGridState008, besselGridState011, besselGridState017, besselGridState021, besselGridState022, besselGridState028, besselGridState030, besselGridState033, besselGridState038, besselGridState039, besselGridState041, besselGridState044, besselGridState045, besselGridState047, besselGridState049, besselGridState055, besselGridState058, besselGridState060, besselGridState066, besselGridState070, besselGridState071, besselGridState075, besselGridState081, besselGridState085, besselGridState087, besselStateSubset, linearInterval, widenInterval,
    rationalErrorInterval, rationalIntervalSubset, orderedInterval, Finset.sum_range_succ,
    IntervalRat.add, IntervalRat.mul, IntervalRat.scale, IntervalRat.singleton]

theorem compactCertificate244_stateChecks1 :
    compactCertificate244.stateChecks 3 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 8 12 (102739753213273 / 4000000000000)) (orderedInterval (152980129364 / 1000000000000) (152980129365 / 1000000000000), orderedInterval (34153151836 / 1000000000000) (34153151837 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 22 12 (275973428672581 / 4000000000000)) (orderedInterval (59038878557 / 1000000000000) (59038878558 / 1000000000000), orderedInterval (75346379827 / 1000000000000) (75346379828 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 60 12 (749321543323377 / 4000000000000)) (orderedInterval (-21646954194 / 1000000000000) (-21646953423 / 1000000000000), orderedInterval (54185383425 / 1000000000000) (54185384197 / 1000000000000))) = true
  norm_num [besselStateAtRationalPoint, besselIntervalStepZero,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, besselZeroTransition,
    besselInitial, besselGridStateAt, besselGridStateBlock00, besselGridStateBlock01,
    besselGridStateBlock02, besselGridStateBlock03, besselGridStateBlock04,
    besselGridStateBlock05, besselGridStateBlock06, besselGridStateBlock07,
    besselGridStateBlock08, besselGridStateBlock09, besselGridStateBlock10,
    besselGridStateBlock11, besselGridStateBlock12, besselGridStateBlock13,
    besselGridStateBlock14, besselGridState008, besselGridState011, besselGridState017, besselGridState021, besselGridState022, besselGridState028, besselGridState030, besselGridState033, besselGridState038, besselGridState039, besselGridState041, besselGridState044, besselGridState045, besselGridState047, besselGridState049, besselGridState055, besselGridState058, besselGridState060, besselGridState066, besselGridState070, besselGridState071, besselGridState075, besselGridState081, besselGridState085, besselGridState087, besselStateSubset, linearInterval, widenInterval,
    rationalErrorInterval, rationalIntervalSubset, orderedInterval, Finset.sum_range_succ,
    IntervalRat.add, IntervalRat.mul, IntervalRat.scale, IntervalRat.singleton]

theorem compactCertificate244_stateChecks2 :
    compactCertificate244.stateChecks 6 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 44 12 (551946857345401 / 4000000000000)) (orderedInterval (34987714451 / 1000000000000) (34987714452 / 1000000000000), orderedInterval (58092677681 / 1000000000000) (58092677682 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 75 12 (945770347694173 / 4000000000000)) (orderedInterval (-51853249783 / 1000000000000) (-51853249634 / 1000000000000), orderedInterval (2040062989 / 1000000000000) (2040063139 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 55 12 (696650157507607 / 4000000000000)) (orderedInterval (-50277363460 / 1000000000000) (-50277318466 / 1000000000000), orderedInterval (33722625377 / 1000000000000) (33722670372 / 1000000000000))) = true
  norm_num [besselStateAtRationalPoint, besselIntervalStepZero,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, besselZeroTransition,
    besselInitial, besselGridStateAt, besselGridStateBlock00, besselGridStateBlock01,
    besselGridStateBlock02, besselGridStateBlock03, besselGridStateBlock04,
    besselGridStateBlock05, besselGridStateBlock06, besselGridStateBlock07,
    besselGridStateBlock08, besselGridStateBlock09, besselGridStateBlock10,
    besselGridStateBlock11, besselGridStateBlock12, besselGridStateBlock13,
    besselGridStateBlock14, besselGridState008, besselGridState011, besselGridState017, besselGridState021, besselGridState022, besselGridState028, besselGridState030, besselGridState033, besselGridState038, besselGridState039, besselGridState041, besselGridState044, besselGridState045, besselGridState047, besselGridState049, besselGridState055, besselGridState058, besselGridState060, besselGridState066, besselGridState070, besselGridState071, besselGridState075, besselGridState081, besselGridState085, besselGridState087, besselStateSubset, linearInterval, widenInterval,
    rationalErrorInterval, rationalIntervalSubset, orderedInterval, Finset.sum_range_succ,
    IntervalRat.add, IntervalRat.mul, IntervalRat.scale, IntervalRat.singleton]

theorem compactCertificate244_stateChecks3 :
    compactCertificate244.stateChecks 9 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 85 12 (1068840493244761 / 4000000000000)) (orderedInterval (-39976134849 / 1000000000000) (-39976134848 / 1000000000000), orderedInterval (-27931910625 / 1000000000000) (-27931910624 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 49 12 (617095346495569 / 4000000000000)) (orderedInterval (-57831512491 / 1000000000000) (-57831512490 / 1000000000000), orderedInterval (-27777900096 / 1000000000000) (-27777900095 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 87 12 (1095046521345221 / 4000000000000)) (orderedInterval (-45417404450 / 1000000000000) (-45417404448 / 1000000000000), orderedInterval (-16125357797 / 1000000000000) (-16125357796 / 1000000000000))) = true
  norm_num [besselStateAtRationalPoint, besselIntervalStepZero,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, besselZeroTransition,
    besselInitial, besselGridStateAt, besselGridStateBlock00, besselGridStateBlock01,
    besselGridStateBlock02, besselGridStateBlock03, besselGridStateBlock04,
    besselGridStateBlock05, besselGridStateBlock06, besselGridStateBlock07,
    besselGridStateBlock08, besselGridStateBlock09, besselGridStateBlock10,
    besselGridStateBlock11, besselGridStateBlock12, besselGridStateBlock13,
    besselGridStateBlock14, besselGridState008, besselGridState011, besselGridState017, besselGridState021, besselGridState022, besselGridState028, besselGridState030, besselGridState033, besselGridState038, besselGridState039, besselGridState041, besselGridState044, besselGridState045, besselGridState047, besselGridState049, besselGridState055, besselGridState058, besselGridState060, besselGridState066, besselGridState070, besselGridState071, besselGridState075, besselGridState081, besselGridState085, besselGridState087, besselStateSubset, linearInterval, widenInterval,
    rationalErrorInterval, rationalIntervalSubset, orderedInterval, Finset.sum_range_succ,
    IntervalRat.add, IntervalRat.mul, IntervalRat.scale, IntervalRat.singleton]

theorem compactCertificate244_stateChecks4 :
    compactCertificate244.stateChecks 12 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 81 12 (1023134505939449 / 4000000000000)) (orderedInterval (-43076326606 / 1000000000000) (-43076288616 / 1000000000000), orderedInterval (25250212416 / 1000000000000) (25250250407 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 58 12 (730157060729417 / 4000000000000)) (orderedInterval (52938094687 / 1000000000000) (52938094688 / 1000000000000), orderedInterval (26029933850 / 1000000000000) (26029933851 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 66 12 (827920286017743 / 4000000000000)) (orderedInterval (22601520419 / 1000000000000) (22601520420 / 1000000000000), orderedInterval (50590552005 / 1000000000000) (50590552006 / 1000000000000))) = true
  norm_num [besselStateAtRationalPoint, besselIntervalStepZero,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, besselZeroTransition,
    besselInitial, besselGridStateAt, besselGridStateBlock00, besselGridStateBlock01,
    besselGridStateBlock02, besselGridStateBlock03, besselGridStateBlock04,
    besselGridStateBlock05, besselGridStateBlock06, besselGridStateBlock07,
    besselGridStateBlock08, besselGridStateBlock09, besselGridStateBlock10,
    besselGridStateBlock11, besselGridStateBlock12, besselGridStateBlock13,
    besselGridStateBlock14, besselGridState008, besselGridState011, besselGridState017, besselGridState021, besselGridState022, besselGridState028, besselGridState030, besselGridState033, besselGridState038, besselGridState039, besselGridState041, besselGridState044, besselGridState045, besselGridState047, besselGridState049, besselGridState055, besselGridState058, besselGridState060, besselGridState066, besselGridState070, besselGridState071, besselGridState075, besselGridState081, besselGridState085, besselGridState087, besselStateSubset, linearInterval, widenInterval,
    rationalErrorInterval, rationalIntervalSubset, orderedInterval, Finset.sum_range_succ,
    IntervalRat.add, IntervalRat.mul, IntervalRat.scale, IntervalRat.singleton]

theorem compactCertificate244_stateChecks5 :
    compactCertificate244.stateChecks 15 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 55 12 (690233619452767 / 4000000000000)) (orderedInterval (-32031178069 / 1000000000000) (-32031178068 / 1000000000000), orderedInterval (-51514462796 / 1000000000000) (-51514462795 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 49 12 (609842335472107 / 4000000000000)) (orderedInterval (41275624461 / 1000000000000) (41275649817 / 1000000000000), orderedInterval (-49854195078 / 1000000000000) (-49854169722 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 70 12 (176756078566593 / 800000000000)) (orderedInterval (52040482928 / 1000000000000) (52040484798 / 1000000000000), orderedInterval (-13275647815 / 1000000000000) (-13275645945 / 1000000000000))) = true
  norm_num [besselStateAtRationalPoint, besselIntervalStepZero,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, besselZeroTransition,
    besselInitial, besselGridStateAt, besselGridStateBlock00, besselGridStateBlock01,
    besselGridStateBlock02, besselGridStateBlock03, besselGridStateBlock04,
    besselGridStateBlock05, besselGridStateBlock06, besselGridStateBlock07,
    besselGridStateBlock08, besselGridStateBlock09, besselGridStateBlock10,
    besselGridStateBlock11, besselGridStateBlock12, besselGridStateBlock13,
    besselGridStateBlock14, besselGridState008, besselGridState011, besselGridState017, besselGridState021, besselGridState022, besselGridState028, besselGridState030, besselGridState033, besselGridState038, besselGridState039, besselGridState041, besselGridState044, besselGridState045, besselGridState047, besselGridState049, besselGridState055, besselGridState058, besselGridState060, besselGridState066, besselGridState070, besselGridState071, besselGridState075, besselGridState081, besselGridState085, besselGridState087, besselStateSubset, linearInterval, widenInterval,
    rationalErrorInterval, rationalIntervalSubset, orderedInterval, Finset.sum_range_succ,
    IntervalRat.add, IntervalRat.mul, IntervalRat.scale, IntervalRat.singleton]

theorem compactCertificate244_stateChecks6 :
    compactCertificate244.stateChecks 18 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 39 12 (488916615477971 / 4000000000000)) (orderedInterval (-34054738735 / 1000000000000) (-34054738734 / 1000000000000), orderedInterval (-63490175822 / 1000000000000) (-63490175821 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 33 12 (414460029543931 / 4000000000000)) (orderedInterval (-52075308464 / 1000000000000) (-52075308463 / 1000000000000), orderedInterval (-58334199001 / 1000000000000) (-58334199000 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 21 12 (259349842492393 / 4000000000000)) (orderedInterval (34210974102 / 1000000000000) (34210975246 / 1000000000000), orderedInterval (-93261303332 / 1000000000000) (-93261302189 / 1000000000000))) = true
  norm_num [besselStateAtRationalPoint, besselIntervalStepZero,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, besselZeroTransition,
    besselInitial, besselGridStateAt, besselGridStateBlock00, besselGridStateBlock01,
    besselGridStateBlock02, besselGridStateBlock03, besselGridStateBlock04,
    besselGridStateBlock05, besselGridStateBlock06, besselGridStateBlock07,
    besselGridStateBlock08, besselGridStateBlock09, besselGridStateBlock10,
    besselGridStateBlock11, besselGridStateBlock12, besselGridStateBlock13,
    besselGridStateBlock14, besselGridState008, besselGridState011, besselGridState017, besselGridState021, besselGridState022, besselGridState028, besselGridState030, besselGridState033, besselGridState038, besselGridState039, besselGridState041, besselGridState044, besselGridState045, besselGridState047, besselGridState049, besselGridState055, besselGridState058, besselGridState060, besselGridState066, besselGridState070, besselGridState071, besselGridState075, besselGridState081, besselGridState085, besselGridState087, besselStateSubset, linearInterval, widenInterval,
    rationalErrorInterval, rationalIntervalSubset, orderedInterval, Finset.sum_range_succ,
    IntervalRat.add, IntervalRat.mul, IntervalRat.scale, IntervalRat.singleton]

theorem compactCertificate244_stateChecks7 :
    compactCertificate244.stateChecks 21 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 11 12 (139479207851031 / 4000000000000)) (orderedInterval (-120048736229 / 1000000000000) (-120048736228 / 1000000000000), orderedInterval (-60281124518 / 1000000000000) (-60281124517 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 30 12 (378713181886093 / 4000000000000)) (orderedInterval (76852322953 / 1000000000000) (76852322954 / 1000000000000), orderedInterval (28189260451 / 1000000000000) (28189260452 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 41 12 (517100472679661 / 4000000000000)) (orderedInterval (-66688227257 / 1000000000000) (-66688227256 / 1000000000000), orderedInterval (-21586639242 / 1000000000000) (-21586639241 / 1000000000000))) = true
  norm_num [besselStateAtRationalPoint, besselIntervalStepZero,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, besselZeroTransition,
    besselInitial, besselGridStateAt, besselGridStateBlock00, besselGridStateBlock01,
    besselGridStateBlock02, besselGridStateBlock03, besselGridStateBlock04,
    besselGridStateBlock05, besselGridStateBlock06, besselGridStateBlock07,
    besselGridStateBlock08, besselGridStateBlock09, besselGridStateBlock10,
    besselGridStateBlock11, besselGridStateBlock12, besselGridStateBlock13,
    besselGridStateBlock14, besselGridState008, besselGridState011, besselGridState017, besselGridState021, besselGridState022, besselGridState028, besselGridState030, besselGridState033, besselGridState038, besselGridState039, besselGridState041, besselGridState044, besselGridState045, besselGridState047, besselGridState049, besselGridState055, besselGridState058, besselGridState060, besselGridState066, besselGridState070, besselGridState071, besselGridState075, besselGridState081, besselGridState085, besselGridState087, besselStateSubset, linearInterval, widenInterval,
    rationalErrorInterval, rationalIntervalSubset, orderedInterval, Finset.sum_range_succ,
    IntervalRat.add, IntervalRat.mul, IntervalRat.scale, IntervalRat.singleton]

theorem compactCertificate244_stateChecks8 :
    compactCertificate244.stateChecks 24 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 17 12 (218650157507607 / 4000000000000)) (orderedInterval (-96322815620 / 1000000000000) (-96322807459 / 1000000000000), orderedInterval (49542986546 / 1000000000000) (49542994706 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 71 12 (888800751174647 / 4000000000000)) (orderedInterval (3639921639 / 1000000000000) (3639921647 / 1000000000000), orderedInterval (-53410730037 / 1000000000000) (-53410730030 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 47 12 (593677711146073 / 4000000000000)) (orderedInterval (-65477411266 / 1000000000000) (-65477411232 / 1000000000000), orderedInterval (-1198367915 / 1000000000000) (-1198367881 / 1000000000000))) = true
  norm_num [besselStateAtRationalPoint, besselIntervalStepZero,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, besselZeroTransition,
    besselInitial, besselGridStateAt, besselGridStateBlock00, besselGridStateBlock01,
    besselGridStateBlock02, besselGridStateBlock03, besselGridStateBlock04,
    besselGridStateBlock05, besselGridStateBlock06, besselGridStateBlock07,
    besselGridStateBlock08, besselGridStateBlock09, besselGridStateBlock10,
    besselGridStateBlock11, besselGridStateBlock12, besselGridStateBlock13,
    besselGridStateBlock14, besselGridState008, besselGridState011, besselGridState017, besselGridState021, besselGridState022, besselGridState028, besselGridState030, besselGridState033, besselGridState038, besselGridState039, besselGridState041, besselGridState044, besselGridState045, besselGridState047, besselGridState049, besselGridState055, besselGridState058, besselGridState060, besselGridState066, besselGridState070, besselGridState071, besselGridState075, besselGridState081, besselGridState085, besselGridState087, besselStateSubset, linearInterval, widenInterval,
    rationalErrorInterval, rationalIntervalSubset, orderedInterval, Finset.sum_range_succ,
    IntervalRat.add, IntervalRat.mul, IntervalRat.scale, IntervalRat.singleton]

theorem compactCertificate244_states : ∀ j,
    BesselStateValid (compactCertificate244.point j) (compactCertificate244.state j) :=
  compactCertificate244.statesValid_of_checks3 compactCertificate244_stateChecks0
    compactCertificate244_stateChecks1 compactCertificate244_stateChecks2
    compactCertificate244_stateChecks3 compactCertificate244_stateChecks4
    compactCertificate244_stateChecks5 compactCertificate244_stateChecks6
    compactCertificate244_stateChecks7 compactCertificate244_stateChecks8

theorem compactCertificate244_chunkChecks0_0 :
    compactCertificate244.chunkChecks (0 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 0) <| besselDerivativeNearFromState (239 / 2) 0 (IntervalRat.scale (239 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (57347235040 / 1000000000000) (57347235041 / 1000000000000), orderedInterval (44911423080 / 1000000000000) (44911423081 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 0) <| besselDerivativeNearFromState (352092636548339 / 4000000000000) 0 (IntervalRat.scale (239 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (63470757745 / 1000000000000) (63470757746 / 1000000000000), orderedInterval (56242143531 / 1000000000000) (56242143532 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 0) <| besselDerivativeNearFromState (113859524459987 / 800000000000) 0 (IntervalRat.scale (239 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-65955974271 / 1000000000000) (-65955973830 / 1000000000000), orderedInterval (11313332022 / 1000000000000) (11313332463 / 1000000000000)))) (orderedInterval (19451488980 / 1000000000000) (19451489015 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 0) <| besselDerivativeNearFromState (102739753213273 / 4000000000000) 0 (IntervalRat.scale (239 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (152980129364 / 1000000000000) (152980129365 / 1000000000000), orderedInterval (34153151836 / 1000000000000) (34153151837 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 0) <| besselDerivativeNearFromState (275973428672581 / 4000000000000) 0 (IntervalRat.scale (239 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (59038878557 / 1000000000000) (59038878558 / 1000000000000), orderedInterval (75346379827 / 1000000000000) (75346379828 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 0) <| besselDerivativeNearFromState (749321543323377 / 4000000000000) 0 (IntervalRat.scale (239 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-21646954194 / 1000000000000) (-21646953423 / 1000000000000), orderedInterval (54185383425 / 1000000000000) (54185384197 / 1000000000000)))) (orderedInterval (2034760737 / 1000000000000) (2034760807 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 0) <| besselDerivativeNearFromState (551946857345401 / 4000000000000) 0 (IntervalRat.scale (239 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (34987714451 / 1000000000000) (34987714452 / 1000000000000), orderedInterval (58092677681 / 1000000000000) (58092677682 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 0) <| besselDerivativeNearFromState (945770347694173 / 4000000000000) 0 (IntervalRat.scale (239 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-51853249783 / 1000000000000) (-51853249634 / 1000000000000), orderedInterval (2040062989 / 1000000000000) (2040063139 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 0) <| besselDerivativeNearFromState (696650157507607 / 4000000000000) 0 (IntervalRat.scale (239 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-50277363460 / 1000000000000) (-50277318466 / 1000000000000), orderedInterval (33722625377 / 1000000000000) (33722670372 / 1000000000000)))) (orderedInterval (384257002 / 1000000000000) (384258102 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate244_chunkChecks0_1 :
    compactCertificate244.chunkChecks (0 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 0) <| besselDerivativeNearFromState (1068840493244761 / 4000000000000) 0 (IntervalRat.scale (239 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-39976134849 / 1000000000000) (-39976134848 / 1000000000000), orderedInterval (-27931910625 / 1000000000000) (-27931910624 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 0) <| besselDerivativeNearFromState (617095346495569 / 4000000000000) 0 (IntervalRat.scale (239 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-57831512491 / 1000000000000) (-57831512490 / 1000000000000), orderedInterval (-27777900096 / 1000000000000) (-27777900095 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 0) <| besselDerivativeNearFromState (1095046521345221 / 4000000000000) 0 (IntervalRat.scale (239 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-45417404450 / 1000000000000) (-45417404448 / 1000000000000), orderedInterval (-16125357797 / 1000000000000) (-16125357796 / 1000000000000)))) (orderedInterval (-3637914355 / 1000000000000) (-3637914307 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 0) <| besselDerivativeNearFromState (1023134505939449 / 4000000000000) 0 (IntervalRat.scale (239 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-43076326606 / 1000000000000) (-43076288616 / 1000000000000), orderedInterval (25250212416 / 1000000000000) (25250250407 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 0) <| besselDerivativeNearFromState (730157060729417 / 4000000000000) 0 (IntervalRat.scale (239 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (52938094687 / 1000000000000) (52938094688 / 1000000000000), orderedInterval (26029933850 / 1000000000000) (26029933851 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 0) <| besselDerivativeNearFromState (827920286017743 / 4000000000000) 0 (IntervalRat.scale (239 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (22601520419 / 1000000000000) (22601520420 / 1000000000000), orderedInterval (50590552005 / 1000000000000) (50590552006 / 1000000000000)))) (orderedInterval (5669261178 / 1000000000000) (5669261879 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 0) <| besselDerivativeNearFromState (690233619452767 / 4000000000000) 0 (IntervalRat.scale (239 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-32031178069 / 1000000000000) (-32031178068 / 1000000000000), orderedInterval (-51514462796 / 1000000000000) (-51514462795 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 0) <| besselDerivativeNearFromState (609842335472107 / 4000000000000) 0 (IntervalRat.scale (239 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (41275624461 / 1000000000000) (41275649817 / 1000000000000), orderedInterval (-49854195078 / 1000000000000) (-49854169722 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 0) <| besselDerivativeNearFromState (176756078566593 / 800000000000) 0 (IntervalRat.scale (239 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (52040482928 / 1000000000000) (52040484798 / 1000000000000), orderedInterval (-13275647815 / 1000000000000) (-13275645945 / 1000000000000)))) (orderedInterval (-1399511837 / 1000000000000) (-1399510326 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate244_chunkChecks0_2 :
    compactCertificate244.chunkChecks (0 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 0) <| besselDerivativeNearFromState (488916615477971 / 4000000000000) 0 (IntervalRat.scale (239 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-34054738735 / 1000000000000) (-34054738734 / 1000000000000), orderedInterval (-63490175822 / 1000000000000) (-63490175821 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 0) <| besselDerivativeNearFromState (414460029543931 / 4000000000000) 0 (IntervalRat.scale (239 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-52075308464 / 1000000000000) (-52075308463 / 1000000000000), orderedInterval (-58334199001 / 1000000000000) (-58334199000 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 0) <| besselDerivativeNearFromState (259349842492393 / 4000000000000) 0 (IntervalRat.scale (239 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (34210974102 / 1000000000000) (34210975246 / 1000000000000), orderedInterval (-93261303332 / 1000000000000) (-93261302189 / 1000000000000)))) (orderedInterval (9506303023 / 1000000000000) (9506303091 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 0) <| besselDerivativeNearFromState (139479207851031 / 4000000000000) 0 (IntervalRat.scale (239 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-120048736229 / 1000000000000) (-120048736228 / 1000000000000), orderedInterval (-60281124518 / 1000000000000) (-60281124517 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 0) <| besselDerivativeNearFromState (378713181886093 / 4000000000000) 0 (IntervalRat.scale (239 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (76852322953 / 1000000000000) (76852322954 / 1000000000000), orderedInterval (28189260451 / 1000000000000) (28189260452 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 0) <| besselDerivativeNearFromState (517100472679661 / 4000000000000) 0 (IntervalRat.scale (239 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-66688227257 / 1000000000000) (-66688227256 / 1000000000000), orderedInterval (-21586639242 / 1000000000000) (-21586639241 / 1000000000000)))) (orderedInterval (5584086287 / 1000000000000) (5584086302 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 0) <| besselDerivativeNearFromState (218650157507607 / 4000000000000) 0 (IntervalRat.scale (239 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-96322815620 / 1000000000000) (-96322807459 / 1000000000000), orderedInterval (49542986546 / 1000000000000) (49542994706 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 0) <| besselDerivativeNearFromState (888800751174647 / 4000000000000) 0 (IntervalRat.scale (239 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (3639921639 / 1000000000000) (3639921647 / 1000000000000), orderedInterval (-53410730037 / 1000000000000) (-53410730030 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 0) <| besselDerivativeNearFromState (593677711146073 / 4000000000000) 0 (IntervalRat.scale (239 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-65477411266 / 1000000000000) (-65477411232 / 1000000000000), orderedInterval (-1198367915 / 1000000000000) (-1198367881 / 1000000000000)))) (orderedInterval (11408337633 / 1000000000000) (11408337723 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate244_chunkChecks0 :
    compactCertificate244.chunkChecks (0 : Fin 5) 0 9 = true :=
  compactCertificate244.chunkChecks_nine_of_three (0 : Fin 5) compactCertificate244_chunkChecks0_0
    compactCertificate244_chunkChecks0_1 compactCertificate244_chunkChecks0_2

theorem compactCertificate244_chunkChecks1_0 :
    compactCertificate244.chunkChecks (1 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 1) <| besselDerivativeNearFromState (239 / 2) 1 (IntervalRat.scale (239 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (57347235040 / 1000000000000) (57347235041 / 1000000000000), orderedInterval (44911423080 / 1000000000000) (44911423081 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 1) <| besselDerivativeNearFromState (352092636548339 / 4000000000000) 1 (IntervalRat.scale (239 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (63470757745 / 1000000000000) (63470757746 / 1000000000000), orderedInterval (56242143531 / 1000000000000) (56242143532 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 1) <| besselDerivativeNearFromState (113859524459987 / 800000000000) 1 (IntervalRat.scale (239 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-65955974271 / 1000000000000) (-65955973830 / 1000000000000), orderedInterval (11313332022 / 1000000000000) (11313332463 / 1000000000000)))) (orderedInterval (18978021389 / 1000000000000) (18978021430 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 1) <| besselDerivativeNearFromState (102739753213273 / 4000000000000) 1 (IntervalRat.scale (239 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (152980129364 / 1000000000000) (152980129365 / 1000000000000), orderedInterval (34153151836 / 1000000000000) (34153151837 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 1) <| besselDerivativeNearFromState (275973428672581 / 4000000000000) 1 (IntervalRat.scale (239 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (59038878557 / 1000000000000) (59038878558 / 1000000000000), orderedInterval (75346379827 / 1000000000000) (75346379828 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 1) <| besselDerivativeNearFromState (749321543323377 / 4000000000000) 1 (IntervalRat.scale (239 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-21646954194 / 1000000000000) (-21646953423 / 1000000000000), orderedInterval (54185383425 / 1000000000000) (54185384197 / 1000000000000)))) (orderedInterval (-4529831675 / 1000000000000) (-4529831572 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 1) <| besselDerivativeNearFromState (551946857345401 / 4000000000000) 1 (IntervalRat.scale (239 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (34987714451 / 1000000000000) (34987714452 / 1000000000000), orderedInterval (58092677681 / 1000000000000) (58092677682 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 1) <| besselDerivativeNearFromState (945770347694173 / 4000000000000) 1 (IntervalRat.scale (239 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-51853249783 / 1000000000000) (-51853249634 / 1000000000000), orderedInterval (2040062989 / 1000000000000) (2040063139 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 1) <| besselDerivativeNearFromState (696650157507607 / 4000000000000) 1 (IntervalRat.scale (239 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-50277363460 / 1000000000000) (-50277318466 / 1000000000000), orderedInterval (33722625377 / 1000000000000) (33722670372 / 1000000000000)))) (orderedInterval (1063315879 / 1000000000000) (1063317485 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate244_chunkChecks1_1 :
    compactCertificate244.chunkChecks (1 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 1) <| besselDerivativeNearFromState (1068840493244761 / 4000000000000) 1 (IntervalRat.scale (239 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-39976134849 / 1000000000000) (-39976134848 / 1000000000000), orderedInterval (-27931910625 / 1000000000000) (-27931910624 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 1) <| besselDerivativeNearFromState (617095346495569 / 4000000000000) 1 (IntervalRat.scale (239 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-57831512491 / 1000000000000) (-57831512490 / 1000000000000), orderedInterval (-27777900096 / 1000000000000) (-27777900095 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 1) <| besselDerivativeNearFromState (1095046521345221 / 4000000000000) 1 (IntervalRat.scale (239 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-45417404450 / 1000000000000) (-45417404448 / 1000000000000), orderedInterval (-16125357797 / 1000000000000) (-16125357796 / 1000000000000)))) (orderedInterval (3189510969 / 1000000000000) (3189511069 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 1) <| besselDerivativeNearFromState (1023134505939449 / 4000000000000) 1 (IntervalRat.scale (239 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-43076326606 / 1000000000000) (-43076288616 / 1000000000000), orderedInterval (25250212416 / 1000000000000) (25250250407 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 1) <| besselDerivativeNearFromState (730157060729417 / 4000000000000) 1 (IntervalRat.scale (239 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (52938094687 / 1000000000000) (52938094688 / 1000000000000), orderedInterval (26029933850 / 1000000000000) (26029933851 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 1) <| besselDerivativeNearFromState (827920286017743 / 4000000000000) 1 (IntervalRat.scale (239 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (22601520419 / 1000000000000) (22601520420 / 1000000000000), orderedInterval (50590552005 / 1000000000000) (50590552006 / 1000000000000)))) (orderedInterval (2340802338 / 1000000000000) (2340803830 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 1) <| besselDerivativeNearFromState (690233619452767 / 4000000000000) 1 (IntervalRat.scale (239 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-32031178069 / 1000000000000) (-32031178068 / 1000000000000), orderedInterval (-51514462796 / 1000000000000) (-51514462795 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 1) <| besselDerivativeNearFromState (609842335472107 / 4000000000000) 1 (IntervalRat.scale (239 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (41275624461 / 1000000000000) (41275649817 / 1000000000000), orderedInterval (-49854195078 / 1000000000000) (-49854169722 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 1) <| besselDerivativeNearFromState (176756078566593 / 800000000000) 1 (IntervalRat.scale (239 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (52040482928 / 1000000000000) (52040484798 / 1000000000000), orderedInterval (-13275647815 / 1000000000000) (-13275645945 / 1000000000000)))) (orderedInterval (2152442576 / 1000000000000) (2152444533 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate244_chunkChecks1_2 :
    compactCertificate244.chunkChecks (1 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 1) <| besselDerivativeNearFromState (488916615477971 / 4000000000000) 1 (IntervalRat.scale (239 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-34054738735 / 1000000000000) (-34054738734 / 1000000000000), orderedInterval (-63490175822 / 1000000000000) (-63490175821 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 1) <| besselDerivativeNearFromState (414460029543931 / 4000000000000) 1 (IntervalRat.scale (239 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-52075308464 / 1000000000000) (-52075308463 / 1000000000000), orderedInterval (-58334199001 / 1000000000000) (-58334199000 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 1) <| besselDerivativeNearFromState (259349842492393 / 4000000000000) 1 (IntervalRat.scale (239 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (34210974102 / 1000000000000) (34210975246 / 1000000000000), orderedInterval (-93261303332 / 1000000000000) (-93261302189 / 1000000000000)))) (orderedInterval (11598931805 / 1000000000000) (11598931854 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 1) <| besselDerivativeNearFromState (139479207851031 / 4000000000000) 1 (IntervalRat.scale (239 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-120048736229 / 1000000000000) (-120048736228 / 1000000000000), orderedInterval (-60281124518 / 1000000000000) (-60281124517 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 1) <| besselDerivativeNearFromState (378713181886093 / 4000000000000) 1 (IntervalRat.scale (239 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (76852322953 / 1000000000000) (76852322954 / 1000000000000), orderedInterval (28189260451 / 1000000000000) (28189260452 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 1) <| besselDerivativeNearFromState (517100472679661 / 4000000000000) 1 (IntervalRat.scale (239 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-66688227257 / 1000000000000) (-66688227256 / 1000000000000), orderedInterval (-21586639242 / 1000000000000) (-21586639241 / 1000000000000)))) (orderedInterval (1607815015 / 1000000000000) (1607815029 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 1) <| besselDerivativeNearFromState (218650157507607 / 4000000000000) 1 (IntervalRat.scale (239 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-96322815620 / 1000000000000) (-96322807459 / 1000000000000), orderedInterval (49542986546 / 1000000000000) (49542994706 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 1) <| besselDerivativeNearFromState (888800751174647 / 4000000000000) 1 (IntervalRat.scale (239 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (3639921639 / 1000000000000) (3639921647 / 1000000000000), orderedInterval (-53410730037 / 1000000000000) (-53410730030 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 1) <| besselDerivativeNearFromState (593677711146073 / 4000000000000) 1 (IntervalRat.scale (239 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-65477411266 / 1000000000000) (-65477411232 / 1000000000000), orderedInterval (-1198367915 / 1000000000000) (-1198367881 / 1000000000000)))) (orderedInterval (8500109579 / 1000000000000) (8500109657 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate244_chunkChecks1 :
    compactCertificate244.chunkChecks (1 : Fin 5) 0 9 = true :=
  compactCertificate244.chunkChecks_nine_of_three (1 : Fin 5) compactCertificate244_chunkChecks1_0
    compactCertificate244_chunkChecks1_1 compactCertificate244_chunkChecks1_2

theorem compactCertificate244_chunkChecks2_0 :
    compactCertificate244.chunkChecks (2 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 2) <| besselDerivativeNearFromState (239 / 2) 2 (IntervalRat.scale (239 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (57347235040 / 1000000000000) (57347235041 / 1000000000000), orderedInterval (44911423080 / 1000000000000) (44911423081 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 2) <| besselDerivativeNearFromState (352092636548339 / 4000000000000) 2 (IntervalRat.scale (239 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (63470757745 / 1000000000000) (63470757746 / 1000000000000), orderedInterval (56242143531 / 1000000000000) (56242143532 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 2) <| besselDerivativeNearFromState (113859524459987 / 800000000000) 2 (IntervalRat.scale (239 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-65955974271 / 1000000000000) (-65955973830 / 1000000000000), orderedInterval (11313332022 / 1000000000000) (11313332463 / 1000000000000)))) (orderedInterval (-17720097642 / 1000000000000) (-17720097593 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 2) <| besselDerivativeNearFromState (102739753213273 / 4000000000000) 2 (IntervalRat.scale (239 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (152980129364 / 1000000000000) (152980129365 / 1000000000000), orderedInterval (34153151836 / 1000000000000) (34153151837 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 2) <| besselDerivativeNearFromState (275973428672581 / 4000000000000) 2 (IntervalRat.scale (239 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (59038878557 / 1000000000000) (59038878558 / 1000000000000), orderedInterval (75346379827 / 1000000000000) (75346379828 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 2) <| besselDerivativeNearFromState (749321543323377 / 4000000000000) 2 (IntervalRat.scale (239 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-21646954194 / 1000000000000) (-21646953423 / 1000000000000), orderedInterval (54185383425 / 1000000000000) (54185384197 / 1000000000000)))) (orderedInterval (-4385626486 / 1000000000000) (-4385626328 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 2) <| besselDerivativeNearFromState (551946857345401 / 4000000000000) 2 (IntervalRat.scale (239 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (34987714451 / 1000000000000) (34987714452 / 1000000000000), orderedInterval (58092677681 / 1000000000000) (58092677682 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 2) <| besselDerivativeNearFromState (945770347694173 / 4000000000000) 2 (IntervalRat.scale (239 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-51853249783 / 1000000000000) (-51853249634 / 1000000000000), orderedInterval (2040062989 / 1000000000000) (2040063139 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 2) <| besselDerivativeNearFromState (696650157507607 / 4000000000000) 2 (IntervalRat.scale (239 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-50277363460 / 1000000000000) (-50277318466 / 1000000000000), orderedInterval (33722625377 / 1000000000000) (33722670372 / 1000000000000)))) (orderedInterval (-3689171941 / 1000000000000) (-3689169578 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate244_chunkChecks2_1 :
    compactCertificate244.chunkChecks (2 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 2) <| besselDerivativeNearFromState (1068840493244761 / 4000000000000) 2 (IntervalRat.scale (239 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-39976134849 / 1000000000000) (-39976134848 / 1000000000000), orderedInterval (-27931910625 / 1000000000000) (-27931910624 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 2) <| besselDerivativeNearFromState (617095346495569 / 4000000000000) 2 (IntervalRat.scale (239 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-57831512491 / 1000000000000) (-57831512490 / 1000000000000), orderedInterval (-27777900096 / 1000000000000) (-27777900095 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 2) <| besselDerivativeNearFromState (1095046521345221 / 4000000000000) 2 (IntervalRat.scale (239 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-45417404450 / 1000000000000) (-45417404448 / 1000000000000), orderedInterval (-16125357797 / 1000000000000) (-16125357796 / 1000000000000)))) (orderedInterval (5482469901 / 1000000000000) (5482470115 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 2) <| besselDerivativeNearFromState (1023134505939449 / 4000000000000) 2 (IntervalRat.scale (239 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-43076326606 / 1000000000000) (-43076288616 / 1000000000000), orderedInterval (25250212416 / 1000000000000) (25250250407 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 2) <| besselDerivativeNearFromState (730157060729417 / 4000000000000) 2 (IntervalRat.scale (239 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (52938094687 / 1000000000000) (52938094688 / 1000000000000), orderedInterval (26029933850 / 1000000000000) (26029933851 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 2) <| besselDerivativeNearFromState (827920286017743 / 4000000000000) 2 (IntervalRat.scale (239 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (22601520419 / 1000000000000) (22601520420 / 1000000000000), orderedInterval (50590552005 / 1000000000000) (50590552006 / 1000000000000)))) (orderedInterval (-14919941837 / 1000000000000) (-14919938643 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 2) <| besselDerivativeNearFromState (690233619452767 / 4000000000000) 2 (IntervalRat.scale (239 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-32031178069 / 1000000000000) (-32031178068 / 1000000000000), orderedInterval (-51514462796 / 1000000000000) (-51514462795 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 2) <| besselDerivativeNearFromState (609842335472107 / 4000000000000) 2 (IntervalRat.scale (239 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (41275624461 / 1000000000000) (41275649817 / 1000000000000), orderedInterval (-49854195078 / 1000000000000) (-49854169722 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 2) <| besselDerivativeNearFromState (176756078566593 / 800000000000) 2 (IntervalRat.scale (239 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (52040482928 / 1000000000000) (52040484798 / 1000000000000), orderedInterval (-13275647815 / 1000000000000) (-13275645945 / 1000000000000)))) (orderedInterval (43108277 / 1000000000000) (43110844 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate244_chunkChecks2_2 :
    compactCertificate244.chunkChecks (2 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 2) <| besselDerivativeNearFromState (488916615477971 / 4000000000000) 2 (IntervalRat.scale (239 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-34054738735 / 1000000000000) (-34054738734 / 1000000000000), orderedInterval (-63490175822 / 1000000000000) (-63490175821 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 2) <| besselDerivativeNearFromState (414460029543931 / 4000000000000) 2 (IntervalRat.scale (239 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-52075308464 / 1000000000000) (-52075308463 / 1000000000000), orderedInterval (-58334199001 / 1000000000000) (-58334199000 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 2) <| besselDerivativeNearFromState (259349842492393 / 4000000000000) 2 (IntervalRat.scale (239 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (34210974102 / 1000000000000) (34210975246 / 1000000000000), orderedInterval (-93261303332 / 1000000000000) (-93261302189 / 1000000000000)))) (orderedInterval (-8337517153 / 1000000000000) (-8337517114 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 2) <| besselDerivativeNearFromState (139479207851031 / 4000000000000) 2 (IntervalRat.scale (239 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-120048736229 / 1000000000000) (-120048736228 / 1000000000000), orderedInterval (-60281124518 / 1000000000000) (-60281124517 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 2) <| besselDerivativeNearFromState (378713181886093 / 4000000000000) 2 (IntervalRat.scale (239 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (76852322953 / 1000000000000) (76852322954 / 1000000000000), orderedInterval (28189260451 / 1000000000000) (28189260452 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 2) <| besselDerivativeNearFromState (517100472679661 / 4000000000000) 2 (IntervalRat.scale (239 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-66688227257 / 1000000000000) (-66688227256 / 1000000000000), orderedInterval (-21586639242 / 1000000000000) (-21586639241 / 1000000000000)))) (orderedInterval (-5089002307 / 1000000000000) (-5089002293 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 2) <| besselDerivativeNearFromState (218650157507607 / 4000000000000) 2 (IntervalRat.scale (239 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-96322815620 / 1000000000000) (-96322807459 / 1000000000000), orderedInterval (49542986546 / 1000000000000) (49542994706 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 2) <| besselDerivativeNearFromState (888800751174647 / 4000000000000) 2 (IntervalRat.scale (239 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (3639921639 / 1000000000000) (3639921647 / 1000000000000), orderedInterval (-53410730037 / 1000000000000) (-53410730030 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 2) <| besselDerivativeNearFromState (593677711146073 / 4000000000000) 2 (IntervalRat.scale (239 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-65477411266 / 1000000000000) (-65477411232 / 1000000000000), orderedInterval (-1198367915 / 1000000000000) (-1198367881 / 1000000000000)))) (orderedInterval (-17876179970 / 1000000000000) (-17876179878 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate244_chunkChecks2 :
    compactCertificate244.chunkChecks (2 : Fin 5) 0 9 = true :=
  compactCertificate244.chunkChecks_nine_of_three (2 : Fin 5) compactCertificate244_chunkChecks2_0
    compactCertificate244_chunkChecks2_1 compactCertificate244_chunkChecks2_2

theorem compactCertificate244_chunkChecks3_0 :
    compactCertificate244.chunkChecks (3 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 3) <| besselDerivativeNearFromState (239 / 2) 3 (IntervalRat.scale (239 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (57347235040 / 1000000000000) (57347235041 / 1000000000000), orderedInterval (44911423080 / 1000000000000) (44911423081 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 3) <| besselDerivativeNearFromState (352092636548339 / 4000000000000) 3 (IntervalRat.scale (239 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (63470757745 / 1000000000000) (63470757746 / 1000000000000), orderedInterval (56242143531 / 1000000000000) (56242143532 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 3) <| besselDerivativeNearFromState (113859524459987 / 800000000000) 3 (IntervalRat.scale (239 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-65955974271 / 1000000000000) (-65955973830 / 1000000000000), orderedInterval (11313332022 / 1000000000000) (11313332463 / 1000000000000)))) (orderedInterval (-18982711354 / 1000000000000) (-18982711296 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 3) <| besselDerivativeNearFromState (102739753213273 / 4000000000000) 3 (IntervalRat.scale (239 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (152980129364 / 1000000000000) (152980129365 / 1000000000000), orderedInterval (34153151836 / 1000000000000) (34153151837 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 3) <| besselDerivativeNearFromState (275973428672581 / 4000000000000) 3 (IntervalRat.scale (239 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (59038878557 / 1000000000000) (59038878558 / 1000000000000), orderedInterval (75346379827 / 1000000000000) (75346379828 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 3) <| besselDerivativeNearFromState (749321543323377 / 4000000000000) 3 (IntervalRat.scale (239 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-21646954194 / 1000000000000) (-21646953423 / 1000000000000), orderedInterval (54185383425 / 1000000000000) (54185384197 / 1000000000000)))) (orderedInterval (14349790449 / 1000000000000) (14349790696 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 3) <| besselDerivativeNearFromState (551946857345401 / 4000000000000) 3 (IntervalRat.scale (239 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (34987714451 / 1000000000000) (34987714452 / 1000000000000), orderedInterval (58092677681 / 1000000000000) (58092677682 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 3) <| besselDerivativeNearFromState (945770347694173 / 4000000000000) 3 (IntervalRat.scale (239 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-51853249783 / 1000000000000) (-51853249634 / 1000000000000), orderedInterval (2040062989 / 1000000000000) (2040063139 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 3) <| besselDerivativeNearFromState (696650157507607 / 4000000000000) 3 (IntervalRat.scale (239 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-50277363460 / 1000000000000) (-50277318466 / 1000000000000), orderedInterval (33722625377 / 1000000000000) (33722670372 / 1000000000000)))) (orderedInterval (-2004688807 / 1000000000000) (-2004685347 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate244_chunkChecks3_1 :
    compactCertificate244.chunkChecks (3 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 3) <| besselDerivativeNearFromState (1068840493244761 / 4000000000000) 3 (IntervalRat.scale (239 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-39976134849 / 1000000000000) (-39976134848 / 1000000000000), orderedInterval (-27931910625 / 1000000000000) (-27931910624 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 3) <| besselDerivativeNearFromState (617095346495569 / 4000000000000) 3 (IntervalRat.scale (239 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-57831512491 / 1000000000000) (-57831512490 / 1000000000000), orderedInterval (-27777900096 / 1000000000000) (-27777900095 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 3) <| besselDerivativeNearFromState (1095046521345221 / 4000000000000) 3 (IntervalRat.scale (239 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-45417404450 / 1000000000000) (-45417404448 / 1000000000000), orderedInterval (-16125357797 / 1000000000000) (-16125357796 / 1000000000000)))) (orderedInterval (-23546578586 / 1000000000000) (-23546578120 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 3) <| besselDerivativeNearFromState (1023134505939449 / 4000000000000) 3 (IntervalRat.scale (239 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-43076326606 / 1000000000000) (-43076288616 / 1000000000000), orderedInterval (25250212416 / 1000000000000) (25250250407 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 3) <| besselDerivativeNearFromState (730157060729417 / 4000000000000) 3 (IntervalRat.scale (239 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (52938094687 / 1000000000000) (52938094688 / 1000000000000), orderedInterval (26029933850 / 1000000000000) (26029933851 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 3) <| besselDerivativeNearFromState (827920286017743 / 4000000000000) 3 (IntervalRat.scale (239 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (22601520419 / 1000000000000) (22601520420 / 1000000000000), orderedInterval (50590552005 / 1000000000000) (50590552006 / 1000000000000)))) (orderedInterval (-2847653360 / 1000000000000) (-2847646542 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 3) <| besselDerivativeNearFromState (690233619452767 / 4000000000000) 3 (IntervalRat.scale (239 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-32031178069 / 1000000000000) (-32031178068 / 1000000000000), orderedInterval (-51514462796 / 1000000000000) (-51514462795 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 3) <| besselDerivativeNearFromState (609842335472107 / 4000000000000) 3 (IntervalRat.scale (239 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (41275624461 / 1000000000000) (41275649817 / 1000000000000), orderedInterval (-49854195078 / 1000000000000) (-49854169722 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 3) <| besselDerivativeNearFromState (176756078566593 / 800000000000) 3 (IntervalRat.scale (239 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (52040482928 / 1000000000000) (52040484798 / 1000000000000), orderedInterval (-13275647815 / 1000000000000) (-13275645945 / 1000000000000)))) (orderedInterval (-1985430514 / 1000000000000) (-1985427139 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate244_chunkChecks3_2 :
    compactCertificate244.chunkChecks (3 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 3) <| besselDerivativeNearFromState (488916615477971 / 4000000000000) 3 (IntervalRat.scale (239 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-34054738735 / 1000000000000) (-34054738734 / 1000000000000), orderedInterval (-63490175822 / 1000000000000) (-63490175821 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 3) <| besselDerivativeNearFromState (414460029543931 / 4000000000000) 3 (IntervalRat.scale (239 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-52075308464 / 1000000000000) (-52075308463 / 1000000000000), orderedInterval (-58334199001 / 1000000000000) (-58334199000 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 3) <| besselDerivativeNearFromState (259349842492393 / 4000000000000) 3 (IntervalRat.scale (239 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (34210974102 / 1000000000000) (34210975246 / 1000000000000), orderedInterval (-93261303332 / 1000000000000) (-93261302189 / 1000000000000)))) (orderedInterval (-12459906318 / 1000000000000) (-12459906285 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 3) <| besselDerivativeNearFromState (139479207851031 / 4000000000000) 3 (IntervalRat.scale (239 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-120048736229 / 1000000000000) (-120048736228 / 1000000000000), orderedInterval (-60281124518 / 1000000000000) (-60281124517 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 3) <| besselDerivativeNearFromState (378713181886093 / 4000000000000) 3 (IntervalRat.scale (239 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (76852322953 / 1000000000000) (76852322954 / 1000000000000), orderedInterval (28189260451 / 1000000000000) (28189260452 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 3) <| besselDerivativeNearFromState (517100472679661 / 4000000000000) 3 (IntervalRat.scale (239 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-66688227257 / 1000000000000) (-66688227256 / 1000000000000), orderedInterval (-21586639242 / 1000000000000) (-21586639241 / 1000000000000)))) (orderedInterval (-1761374663 / 1000000000000) (-1761374649 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 3) <| besselDerivativeNearFromState (218650157507607 / 4000000000000) 3 (IntervalRat.scale (239 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-96322815620 / 1000000000000) (-96322807459 / 1000000000000), orderedInterval (49542986546 / 1000000000000) (49542994706 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 3) <| besselDerivativeNearFromState (888800751174647 / 4000000000000) 3 (IntervalRat.scale (239 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (3639921639 / 1000000000000) (3639921647 / 1000000000000), orderedInterval (-53410730037 / 1000000000000) (-53410730030 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 3) <| besselDerivativeNearFromState (593677711146073 / 4000000000000) 3 (IntervalRat.scale (239 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-65477411266 / 1000000000000) (-65477411232 / 1000000000000), orderedInterval (-1198367915 / 1000000000000) (-1198367881 / 1000000000000)))) (orderedInterval (-28259828607 / 1000000000000) (-28259828480 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate244_chunkChecks3 :
    compactCertificate244.chunkChecks (3 : Fin 5) 0 9 = true :=
  compactCertificate244.chunkChecks_nine_of_three (3 : Fin 5) compactCertificate244_chunkChecks3_0
    compactCertificate244_chunkChecks3_1 compactCertificate244_chunkChecks3_2

theorem compactCertificate244_chunkChecks4_0 :
    compactCertificate244.chunkChecks (4 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 4) <| besselDerivativeNearFromState (239 / 2) 4 (IntervalRat.scale (239 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (57347235040 / 1000000000000) (57347235041 / 1000000000000), orderedInterval (44911423080 / 1000000000000) (44911423081 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 4) <| besselDerivativeNearFromState (352092636548339 / 4000000000000) 4 (IntervalRat.scale (239 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (63470757745 / 1000000000000) (63470757746 / 1000000000000), orderedInterval (56242143531 / 1000000000000) (56242143532 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 4) <| besselDerivativeNearFromState (113859524459987 / 800000000000) 4 (IntervalRat.scale (239 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-65955974271 / 1000000000000) (-65955973830 / 1000000000000), orderedInterval (11313332022 / 1000000000000) (11313332463 / 1000000000000)))) (orderedInterval (15433484088 / 1000000000000) (15433484157 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 4) <| besselDerivativeNearFromState (102739753213273 / 4000000000000) 4 (IntervalRat.scale (239 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (152980129364 / 1000000000000) (152980129365 / 1000000000000), orderedInterval (34153151836 / 1000000000000) (34153151837 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 4) <| besselDerivativeNearFromState (275973428672581 / 4000000000000) 4 (IntervalRat.scale (239 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (59038878557 / 1000000000000) (59038878558 / 1000000000000), orderedInterval (75346379827 / 1000000000000) (75346379828 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 4) <| besselDerivativeNearFromState (749321543323377 / 4000000000000) 4 (IntervalRat.scale (239 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-21646954194 / 1000000000000) (-21646953423 / 1000000000000), orderedInterval (54185383425 / 1000000000000) (54185384197 / 1000000000000)))) (orderedInterval (9288682853 / 1000000000000) (9288683241 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 4) <| besselDerivativeNearFromState (551946857345401 / 4000000000000) 4 (IntervalRat.scale (239 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (34987714451 / 1000000000000) (34987714452 / 1000000000000), orderedInterval (58092677681 / 1000000000000) (58092677682 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 4) <| besselDerivativeNearFromState (945770347694173 / 4000000000000) 4 (IntervalRat.scale (239 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-51853249783 / 1000000000000) (-51853249634 / 1000000000000), orderedInterval (2040062989 / 1000000000000) (2040063139 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 4) <| besselDerivativeNearFromState (696650157507607 / 4000000000000) 4 (IntervalRat.scale (239 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-50277363460 / 1000000000000) (-50277318466 / 1000000000000), orderedInterval (33722625377 / 1000000000000) (33722670372 / 1000000000000)))) (orderedInterval (19062964844 / 1000000000000) (19062969947 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate244_chunkChecks4_1 :
    compactCertificate244.chunkChecks (4 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 4) <| besselDerivativeNearFromState (1068840493244761 / 4000000000000) 4 (IntervalRat.scale (239 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-39976134849 / 1000000000000) (-39976134848 / 1000000000000), orderedInterval (-27931910625 / 1000000000000) (-27931910624 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 4) <| besselDerivativeNearFromState (617095346495569 / 4000000000000) 4 (IntervalRat.scale (239 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-57831512491 / 1000000000000) (-57831512490 / 1000000000000), orderedInterval (-27777900096 / 1000000000000) (-27777900095 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 4) <| besselDerivativeNearFromState (1095046521345221 / 4000000000000) 4 (IntervalRat.scale (239 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-45417404450 / 1000000000000) (-45417404448 / 1000000000000), orderedInterval (-16125357797 / 1000000000000) (-16125357796 / 1000000000000)))) (orderedInterval (-11756296467 / 1000000000000) (-11756295429 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 4) <| besselDerivativeNearFromState (1023134505939449 / 4000000000000) 4 (IntervalRat.scale (239 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-43076326606 / 1000000000000) (-43076288616 / 1000000000000), orderedInterval (25250212416 / 1000000000000) (25250250407 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 4) <| besselDerivativeNearFromState (730157060729417 / 4000000000000) 4 (IntervalRat.scale (239 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (52938094687 / 1000000000000) (52938094688 / 1000000000000), orderedInterval (26029933850 / 1000000000000) (26029933851 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 4) <| besselDerivativeNearFromState (827920286017743 / 4000000000000) 4 (IntervalRat.scale (239 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (22601520419 / 1000000000000) (22601520420 / 1000000000000), orderedInterval (50590552005 / 1000000000000) (50590552006 / 1000000000000)))) (orderedInterval (42595333214 / 1000000000000) (42595347836 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 4) <| besselDerivativeNearFromState (690233619452767 / 4000000000000) 4 (IntervalRat.scale (239 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-32031178069 / 1000000000000) (-32031178068 / 1000000000000), orderedInterval (-51514462796 / 1000000000000) (-51514462795 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 4) <| besselDerivativeNearFromState (609842335472107 / 4000000000000) 4 (IntervalRat.scale (239 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (41275624461 / 1000000000000) (41275649817 / 1000000000000), orderedInterval (-49854195078 / 1000000000000) (-49854169722 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 4) <| besselDerivativeNearFromState (176756078566593 / 800000000000) 4 (IntervalRat.scale (239 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (52040482928 / 1000000000000) (52040484798 / 1000000000000), orderedInterval (-13275647815 / 1000000000000) (-13275645945 / 1000000000000)))) (orderedInterval (7737721465 / 1000000000000) (7737725985 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate244_chunkChecks4_2 :
    compactCertificate244.chunkChecks (4 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 4) <| besselDerivativeNearFromState (488916615477971 / 4000000000000) 4 (IntervalRat.scale (239 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-34054738735 / 1000000000000) (-34054738734 / 1000000000000), orderedInterval (-63490175822 / 1000000000000) (-63490175821 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 4) <| besselDerivativeNearFromState (414460029543931 / 4000000000000) 4 (IntervalRat.scale (239 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-52075308464 / 1000000000000) (-52075308463 / 1000000000000), orderedInterval (-58334199001 / 1000000000000) (-58334199000 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 4) <| besselDerivativeNearFromState (259349842492393 / 4000000000000) 4 (IntervalRat.scale (239 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (34210974102 / 1000000000000) (34210975246 / 1000000000000), orderedInterval (-93261303332 / 1000000000000) (-93261302189 / 1000000000000)))) (orderedInterval (7930252206 / 1000000000000) (7930252236 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 4) <| besselDerivativeNearFromState (139479207851031 / 4000000000000) 4 (IntervalRat.scale (239 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-120048736229 / 1000000000000) (-120048736228 / 1000000000000), orderedInterval (-60281124518 / 1000000000000) (-60281124517 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 4) <| besselDerivativeNearFromState (378713181886093 / 4000000000000) 4 (IntervalRat.scale (239 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (76852322953 / 1000000000000) (76852322954 / 1000000000000), orderedInterval (28189260451 / 1000000000000) (28189260452 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 4) <| besselDerivativeNearFromState (517100472679661 / 4000000000000) 4 (IntervalRat.scale (239 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-66688227257 / 1000000000000) (-66688227256 / 1000000000000), orderedInterval (-21586639242 / 1000000000000) (-21586639241 / 1000000000000)))) (orderedInterval (6357997600 / 1000000000000) (6357997615 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 4) <| besselDerivativeNearFromState (218650157507607 / 4000000000000) 4 (IntervalRat.scale (239 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-96322815620 / 1000000000000) (-96322807459 / 1000000000000), orderedInterval (49542986546 / 1000000000000) (49542994706 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 4) <| besselDerivativeNearFromState (888800751174647 / 4000000000000) 4 (IntervalRat.scale (239 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (3639921639 / 1000000000000) (3639921647 / 1000000000000), orderedInterval (-53410730037 / 1000000000000) (-53410730030 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 4) <| besselDerivativeNearFromState (593677711146073 / 4000000000000) 4 (IntervalRat.scale (239 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-65477411266 / 1000000000000) (-65477411232 / 1000000000000), orderedInterval (-1198367915 / 1000000000000) (-1198367881 / 1000000000000)))) (orderedInterval (26137675897 / 1000000000000) (26137676094 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate244_chunkChecks4 :
    compactCertificate244.chunkChecks (4 : Fin 5) 0 9 = true :=
  compactCertificate244.chunkChecks_nine_of_three (4 : Fin 5) compactCertificate244_chunkChecks4_0
    compactCertificate244_chunkChecks4_1 compactCertificate244_chunkChecks4_2

theorem compactCertificate244_chunks :
    ∀ r : Fin 5, ∀ b, compactCertificate244.chunkCheck r b = true :=
  compactCertificate244.chunkChecks_all (by
    intro r
    fin_cases r
    · exact compactCertificate244_chunkChecks0
    · exact compactCertificate244_chunkChecks1
    · exact compactCertificate244_chunkChecks2
    · exact compactCertificate244_chunkChecks3
    · exact compactCertificate244_chunkChecks4)

theorem compactCertificate244_coefficient0 :
    compactCertificate244.coefficientCheck (0 : Fin 5) = true := by
  norm_num [CompactCertificate.coefficientCheck, intervalFinSumHull,
    compactCertificate244, rationalIntervalSubset, orderedInterval, Fin.sum_univ_succ]

theorem compactCertificate244_coefficient1 :
    compactCertificate244.coefficientCheck (1 : Fin 5) = true := by
  norm_num [CompactCertificate.coefficientCheck, intervalFinSumHull,
    compactCertificate244, rationalIntervalSubset, orderedInterval, Fin.sum_univ_succ]

theorem compactCertificate244_coefficient2 :
    compactCertificate244.coefficientCheck (2 : Fin 5) = true := by
  norm_num [CompactCertificate.coefficientCheck, intervalFinSumHull,
    compactCertificate244, rationalIntervalSubset, orderedInterval, Fin.sum_univ_succ]

theorem compactCertificate244_coefficient3 :
    compactCertificate244.coefficientCheck (3 : Fin 5) = true := by
  norm_num [CompactCertificate.coefficientCheck, intervalFinSumHull,
    compactCertificate244, rationalIntervalSubset, orderedInterval, Fin.sum_univ_succ]

theorem compactCertificate244_coefficient4 :
    compactCertificate244.coefficientCheck (4 : Fin 5) = true := by
  norm_num [CompactCertificate.coefficientCheck, intervalFinSumHull,
    compactCertificate244, rationalIntervalSubset, orderedInterval, Fin.sum_univ_succ]

theorem compactCertificate244_coefficients : ∀ r : Fin 5,
    compactCertificate244.coefficientCheck r = true := by
  intro r
  fin_cases r
  · exact compactCertificate244_coefficient0
  · exact compactCertificate244_coefficient1
  · exact compactCertificate244_coefficient2
  · exact compactCertificate244_coefficient3
  · exact compactCertificate244_coefficient4

theorem compactCertificate244_lower : (1 : ℚ) ≤ compactCertificate244.output.lo := by
  norm_num [CompactCertificate.output, CompactCertificate.interval,
    CompactCertificate.coefficientTargetNat, compactCertificate244, dualConstant,
    intervalTaylorSum, intervalPow, intervalSub, intervalMaxAbs, widenInterval,
    rationalErrorInterval, orderedInterval, IntervalRat.add, IntervalRat.mul, IntervalRat.scale,
    IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4]

theorem compactCertificate244_proves {t : ℝ} (ht : t ∈ compactCertificate244.interval) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t :=
  compactCertificate244.proves compactCertificate244_states compactCertificate244_chunks
    compactCertificate244_coefficients compactCertificate244_lower ht

end Erdos232
