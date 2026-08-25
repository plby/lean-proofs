/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, OpenAI Codex
-/
import ErdosProblems.Erdos232.CompactBase

open LeanCert.Core
namespace Erdos232

def compactCertificate230 : CompactCertificate where
  left := 107
  right := 108
  center := 215 / 2
  grid := fun i =>
    match i.val with
    | 0 => 34
    | 1 => 25
    | 2 => 41
    | 3 => 7
    | 4 => 20
    | 5 => 54
    | 6 => 40
    | 7 => 68
    | 8 => 50
    | 9 => 77
    | 10 => 44
    | 11 => 78
    | 12 => 73
    | 13 => 52
    | 14 => 59
    | 15 => 49
    | 16 => 44
    | 17 => 63
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
    | 0 => 215 / 2
    | 1 => 63347210759743 / 800000000000
    | 2 => 20485186409119 / 160000000000
    | 3 => 18484558109501 / 800000000000
    | 4 => 49652123150297 / 800000000000
    | 5 => 134815173066549 / 800000000000
    | 6 => 99304246300637 / 800000000000
    | 7 => 170159518622801 / 800000000000
    | 8 => 125338731267059 / 800000000000
    | 9 => 192301846064957 / 800000000000
    | 10 => 111025522591253 / 800000000000
    | 11 => 197016738149977 / 800000000000
    | 12 => 184078593118813 / 800000000000
    | 13 => 131367169922029 / 800000000000
    | 14 => 148956369450891 / 800000000000
    | 15 => 124184291365979 / 800000000000
    | 16 => 109720587553559 / 800000000000
    | 17 => 31801302838341 / 160000000000
    | 18 => 87964077261727 / 800000000000
    | 19 => 74568122470247 / 800000000000
    | 20 => 46661268732941 / 800000000000
    | 21 => 25094585512947 / 800000000000
    | 22 => 68136681259841 / 800000000000
    | 23 => 93034813076257 / 800000000000
    | 24 => 39338731267059 / 800000000000
    | 25 => 159909758579539 / 800000000000
    | _ => 106812307863101 / 800000000000
  state := fun i =>
    match i.val with
    | 0 => (orderedInterval (76564470193 / 1000000000000) (76564470200 / 1000000000000), orderedInterval (7381047438 / 1000000000000) (7381047445 / 1000000000000))
    | 1 => (orderedInterval (-88751375686 / 1000000000000) (-88751375683 / 1000000000000), orderedInterval (-12198561207 / 1000000000000) (-12198561204 / 1000000000000))
    | 2 => (orderedInterval (-813588062 / 1000000000000) (-813588057 / 1000000000000), orderedInterval (-70507167709 / 1000000000000) (-70507167704 / 1000000000000))
    | 3 => (orderedInterval (-157347998143 / 1000000000000) (-157347996645 / 1000000000000), orderedInterval (56214171804 / 1000000000000) (56214173302 / 1000000000000))
    | 4 => (orderedInterval (1689750877 / 1000000000000) (1689750884 / 1000000000000), orderedInterval (101252172342 / 1000000000000) (101252172349 / 1000000000000))
    | 5 => (orderedInterval (-20635043988 / 1000000000000) (-20635043445 / 1000000000000), orderedInterval (57957178088 / 1000000000000) (57957178631 / 1000000000000))
    | 6 => (orderedInterval (-48763011405 / 1000000000000) (-48762963465 / 1000000000000), orderedInterval (52644601357 / 1000000000000) (52644649298 / 1000000000000))
    | 7 => (orderedInterval (-7855817024 / 1000000000000) (-7855816998 / 1000000000000), orderedInterval (54160348102 / 1000000000000) (54160348128 / 1000000000000))
    | 8 => (orderedInterval (23548235955 / 1000000000000) (23548235956 / 1000000000000), orderedInterval (59160405981 / 1000000000000) (59160405982 / 1000000000000))
    | 9 => (orderedInterval (34717730774 / 1000000000000) (34717756912 / 1000000000000), orderedInterval (-38060350692 / 1000000000000) (-38060324553 / 1000000000000))
    | 10 => (orderedInterval (65875367097 / 1000000000000) (65875367099 / 1000000000000), orderedInterval (15498148527 / 1000000000000) (15498148529 / 1000000000000))
    | 11 => (orderedInterval (45983357106 / 1000000000000) (45983373137 / 1000000000000), orderedInterval (-21785877755 / 1000000000000) (-21785861724 / 1000000000000))
    | 12 => (orderedInterval (-52584553240 / 1000000000000) (-52584553179 / 1000000000000), orderedInterval (-1146100769 / 1000000000000) (-1146100709 / 1000000000000))
    | 13 => (orderedInterval (62152530685 / 1000000000000) (62152530809 / 1000000000000), orderedInterval (-3921964145 / 1000000000000) (-3921964021 / 1000000000000))
    | 14 => (orderedInterval (-58383121593 / 1000000000000) (-58383121457 / 1000000000000), orderedInterval (3396036221 / 1000000000000) (3396036357 / 1000000000000))
    | 15 => (orderedInterval (-56011328530 / 1000000000000) (-56011309227 / 1000000000000), orderedInterval (31226335147 / 1000000000000) (31226354451 / 1000000000000))
    | 16 => (orderedInterval (-19798741539 / 1000000000000) (-19798741176 / 1000000000000), orderedInterval (65262575926 / 1000000000000) (65262576289 / 1000000000000))
    | 17 => (orderedInterval (-56519000755 / 1000000000000) (-56519000614 / 1000000000000), orderedInterval (3071276008 / 1000000000000) (3071276149 / 1000000000000))
    | 18 => (orderedInterval (-53708048654 / 1000000000000) (-53708048653 / 1000000000000), orderedInterval (-53656257239 / 1000000000000) (-53656257238 / 1000000000000))
    | 19 => (orderedInterval (-20731849100 / 1000000000000) (-20731848818 / 1000000000000), orderedInterval (80112560194 / 1000000000000) (80112560477 / 1000000000000))
    | 20 => (orderedInterval (57289624526 / 1000000000000) (57289638057 / 1000000000000), orderedInterval (-87856990765 / 1000000000000) (-87856977234 / 1000000000000))
    | 21 => (orderedInterval (95390982148 / 1000000000000) (95390982149 / 1000000000000), orderedInterval (104290440415 / 1000000000000) (104290440416 / 1000000000000))
    | 22 => (orderedInterval (-78256639128 / 1000000000000) (-78256639127 / 1000000000000), orderedInterval (-36288891029 / 1000000000000) (-36288891028 / 1000000000000))
    | 23 => (orderedInterval (-55040743071 / 1000000000000) (-55040743070 / 1000000000000), orderedInterval (-49207884229 / 1000000000000) (-49207884228 / 1000000000000))
    | 24 => (orderedInterval (-34623961687 / 1000000000000) (-34623960944 / 1000000000000), orderedInterval (108740898441 / 1000000000000) (108740899185 / 1000000000000))
    | 25 => (orderedInterval (-21453701448 / 1000000000000) (-21453700646 / 1000000000000), orderedInterval (52251757274 / 1000000000000) (52251758076 / 1000000000000))
    | _ => (orderedInterval (48984623724 / 1000000000000) (48984688780 / 1000000000000), orderedInterval (-48852156688 / 1000000000000) (-48852091632 / 1000000000000))
  chunkTarget := fun r b =>
    match r.val with
    | 0 =>
      match b.val with
      | 0 => orderedInterval (29472742769 / 1000000000000) (29472742781 / 1000000000000)
      | 1 => orderedInterval (3235747782 / 1000000000000) (3235747851 / 1000000000000)
      | 2 => orderedInterval (811419226 / 1000000000000) (811419234 / 1000000000000)
      | 3 => orderedInterval (5248701517 / 1000000000000) (5248708484 / 1000000000000)
      | 4 => orderedInterval (7122087108 / 1000000000000) (7122087135 / 1000000000000)
      | 5 => orderedInterval (-960893847 / 1000000000000) (-960893588 / 1000000000000)
      | 6 => orderedInterval (11626012023 / 1000000000000) (11626012508 / 1000000000000)
      | 7 => orderedInterval (4232252272 / 1000000000000) (4232252286 / 1000000000000)
      | _ => orderedInterval (-7653182289 / 1000000000000) (-7653169983 / 1000000000000)
    | 1 =>
      match b.val with
      | 0 => orderedInterval (-2085826668 / 1000000000000) (-2085826656 / 1000000000000)
      | 1 => orderedInterval (-4455514322 / 1000000000000) (-4455514242 / 1000000000000)
      | 2 => orderedInterval (-1221477796 / 1000000000000) (-1221477783 / 1000000000000)
      | 3 => orderedInterval (9509772261 / 1000000000000) (9509787956 / 1000000000000)
      | 4 => orderedInterval (-551996174 / 1000000000000) (-551996131 / 1000000000000)
      | 5 => orderedInterval (-4098797105 / 1000000000000) (-4098796734 / 1000000000000)
      | 6 => orderedInterval (3291672617 / 1000000000000) (3291672895 / 1000000000000)
      | 7 => orderedInterval (4170074519 / 1000000000000) (4170074532 / 1000000000000)
      | _ => orderedInterval (3775182794 / 1000000000000) (3775198121 / 1000000000000)
    | 2 =>
      match b.val with
      | 0 => orderedInterval (-29811648536 / 1000000000000) (-29811648523 / 1000000000000)
      | 1 => orderedInterval (-3662876415 / 1000000000000) (-3662876298 / 1000000000000)
      | 2 => orderedInterval (-2146077863 / 1000000000000) (-2146077840 / 1000000000000)
      | 3 => orderedInterval (-11684951051 / 1000000000000) (-11684915533 / 1000000000000)
      | 4 => orderedInterval (-18944271323 / 1000000000000) (-18944271254 / 1000000000000)
      | 5 => orderedInterval (4489483429 / 1000000000000) (4489483966 / 1000000000000)
      | 6 => orderedInterval (-10446100556 / 1000000000000) (-10446100388 / 1000000000000)
      | 7 => orderedInterval (-5939859873 / 1000000000000) (-5939859861 / 1000000000000)
      | _ => orderedInterval (8148112120 / 1000000000000) (8148131380 / 1000000000000)
    | 3 =>
      match b.val with
      | 0 => orderedInterval (4386799951 / 1000000000000) (4386799966 / 1000000000000)
      | 1 => orderedInterval (15200380805 / 1000000000000) (15200380986 / 1000000000000)
      | 2 => orderedInterval (8533378962 / 1000000000000) (8533379003 / 1000000000000)
      | 3 => orderedInterval (-40737129185 / 1000000000000) (-40737049117 / 1000000000000)
      | 4 => orderedInterval (1384447418 / 1000000000000) (1384447534 / 1000000000000)
      | 5 => orderedInterval (6131027094 / 1000000000000) (6131027871 / 1000000000000)
      | 6 => orderedInterval (-5670410227 / 1000000000000) (-5670410121 / 1000000000000)
      | 7 => orderedInterval (-5080451284 / 1000000000000) (-5080451271 / 1000000000000)
      | _ => orderedInterval (9645042609 / 1000000000000) (9645066686 / 1000000000000)
    | _ =>
      match b.val with
      | 0 => orderedInterval (29923767437 / 1000000000000) (29923767455 / 1000000000000)
      | 1 => orderedInterval (8586148548 / 1000000000000) (8586148832 / 1000000000000)
      | 2 => orderedInterval (6122354498 / 1000000000000) (6122354574 / 1000000000000)
      | 3 => orderedInterval (40137877520 / 1000000000000) (40138058788 / 1000000000000)
      | 4 => orderedInterval (54556830169 / 1000000000000) (54556830366 / 1000000000000)
      | 5 => orderedInterval (-16834886354 / 1000000000000) (-16834885219 / 1000000000000)
      | 6 => orderedInterval (10328752973 / 1000000000000) (10328753046 / 1000000000000)
      | 7 => orderedInterval (6558048986 / 1000000000000) (6558049000 / 1000000000000)
      | _ => orderedInterval (-1181984497 / 1000000000000) (-1181954079 / 1000000000000)
  coefficientTarget := fun i =>
    match i.val with
    | 0 => orderedInterval (53134886561 / 1000000000000) (53134906708 / 1000000000000)
    | 1 => orderedInterval (8333090126 / 1000000000000) (8333121958 / 1000000000000)
    | 2 => orderedInterval (-69998190068 / 1000000000000) (-69998134351 / 1000000000000)
    | 3 => orderedInterval (-6206913857 / 1000000000000) (-6206808463 / 1000000000000)
    | _ => orderedInterval (138196909280 / 1000000000000) (138197122763 / 1000000000000)

theorem compactCertificate230_stateChecks0 :
    compactCertificate230.stateChecks 0 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 34 12 (215 / 2)) (orderedInterval (76564470193 / 1000000000000) (76564470200 / 1000000000000), orderedInterval (7381047438 / 1000000000000) (7381047445 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 25 12 (63347210759743 / 800000000000)) (orderedInterval (-88751375686 / 1000000000000) (-88751375683 / 1000000000000), orderedInterval (-12198561207 / 1000000000000) (-12198561204 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 41 12 (20485186409119 / 160000000000)) (orderedInterval (-813588062 / 1000000000000) (-813588057 / 1000000000000), orderedInterval (-70507167709 / 1000000000000) (-70507167704 / 1000000000000))) = true
  norm_num [besselStateAtRationalPoint, besselIntervalStepZero,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, besselZeroTransition,
    besselInitial, besselGridStateAt, besselGridStateBlock00, besselGridStateBlock01,
    besselGridStateBlock02, besselGridStateBlock03, besselGridStateBlock04,
    besselGridStateBlock05, besselGridStateBlock06, besselGridStateBlock07,
    besselGridStateBlock08, besselGridStateBlock09, besselGridStateBlock10,
    besselGridStateBlock11, besselGridStateBlock12, besselGridStateBlock13,
    besselGridStateBlock14, besselGridState007, besselGridState010, besselGridState016, besselGridState019, besselGridState020, besselGridState025, besselGridState027, besselGridState030, besselGridState034, besselGridState035, besselGridState037, besselGridState040, besselGridState041, besselGridState043, besselGridState044, besselGridState049, besselGridState050, besselGridState052, besselGridState054, besselGridState059, besselGridState063, besselGridState064, besselGridState068, besselGridState073, besselGridState077, besselGridState078, besselStateSubset, linearInterval, widenInterval,
    rationalErrorInterval, rationalIntervalSubset, orderedInterval, Finset.sum_range_succ,
    IntervalRat.add, IntervalRat.mul, IntervalRat.scale, IntervalRat.singleton]

theorem compactCertificate230_stateChecks1 :
    compactCertificate230.stateChecks 3 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 7 12 (18484558109501 / 800000000000)) (orderedInterval (-157347998143 / 1000000000000) (-157347996645 / 1000000000000), orderedInterval (56214171804 / 1000000000000) (56214173302 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 20 12 (49652123150297 / 800000000000)) (orderedInterval (1689750877 / 1000000000000) (1689750884 / 1000000000000), orderedInterval (101252172342 / 1000000000000) (101252172349 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 54 12 (134815173066549 / 800000000000)) (orderedInterval (-20635043988 / 1000000000000) (-20635043445 / 1000000000000), orderedInterval (57957178088 / 1000000000000) (57957178631 / 1000000000000))) = true
  norm_num [besselStateAtRationalPoint, besselIntervalStepZero,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, besselZeroTransition,
    besselInitial, besselGridStateAt, besselGridStateBlock00, besselGridStateBlock01,
    besselGridStateBlock02, besselGridStateBlock03, besselGridStateBlock04,
    besselGridStateBlock05, besselGridStateBlock06, besselGridStateBlock07,
    besselGridStateBlock08, besselGridStateBlock09, besselGridStateBlock10,
    besselGridStateBlock11, besselGridStateBlock12, besselGridStateBlock13,
    besselGridStateBlock14, besselGridState007, besselGridState010, besselGridState016, besselGridState019, besselGridState020, besselGridState025, besselGridState027, besselGridState030, besselGridState034, besselGridState035, besselGridState037, besselGridState040, besselGridState041, besselGridState043, besselGridState044, besselGridState049, besselGridState050, besselGridState052, besselGridState054, besselGridState059, besselGridState063, besselGridState064, besselGridState068, besselGridState073, besselGridState077, besselGridState078, besselStateSubset, linearInterval, widenInterval,
    rationalErrorInterval, rationalIntervalSubset, orderedInterval, Finset.sum_range_succ,
    IntervalRat.add, IntervalRat.mul, IntervalRat.scale, IntervalRat.singleton]

theorem compactCertificate230_stateChecks2 :
    compactCertificate230.stateChecks 6 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 40 12 (99304246300637 / 800000000000)) (orderedInterval (-48763011405 / 1000000000000) (-48762963465 / 1000000000000), orderedInterval (52644601357 / 1000000000000) (52644649298 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 68 12 (170159518622801 / 800000000000)) (orderedInterval (-7855817024 / 1000000000000) (-7855816998 / 1000000000000), orderedInterval (54160348102 / 1000000000000) (54160348128 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 50 12 (125338731267059 / 800000000000)) (orderedInterval (23548235955 / 1000000000000) (23548235956 / 1000000000000), orderedInterval (59160405981 / 1000000000000) (59160405982 / 1000000000000))) = true
  norm_num [besselStateAtRationalPoint, besselIntervalStepZero,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, besselZeroTransition,
    besselInitial, besselGridStateAt, besselGridStateBlock00, besselGridStateBlock01,
    besselGridStateBlock02, besselGridStateBlock03, besselGridStateBlock04,
    besselGridStateBlock05, besselGridStateBlock06, besselGridStateBlock07,
    besselGridStateBlock08, besselGridStateBlock09, besselGridStateBlock10,
    besselGridStateBlock11, besselGridStateBlock12, besselGridStateBlock13,
    besselGridStateBlock14, besselGridState007, besselGridState010, besselGridState016, besselGridState019, besselGridState020, besselGridState025, besselGridState027, besselGridState030, besselGridState034, besselGridState035, besselGridState037, besselGridState040, besselGridState041, besselGridState043, besselGridState044, besselGridState049, besselGridState050, besselGridState052, besselGridState054, besselGridState059, besselGridState063, besselGridState064, besselGridState068, besselGridState073, besselGridState077, besselGridState078, besselStateSubset, linearInterval, widenInterval,
    rationalErrorInterval, rationalIntervalSubset, orderedInterval, Finset.sum_range_succ,
    IntervalRat.add, IntervalRat.mul, IntervalRat.scale, IntervalRat.singleton]

theorem compactCertificate230_stateChecks3 :
    compactCertificate230.stateChecks 9 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 77 12 (192301846064957 / 800000000000)) (orderedInterval (34717730774 / 1000000000000) (34717756912 / 1000000000000), orderedInterval (-38060350692 / 1000000000000) (-38060324553 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 44 12 (111025522591253 / 800000000000)) (orderedInterval (65875367097 / 1000000000000) (65875367099 / 1000000000000), orderedInterval (15498148527 / 1000000000000) (15498148529 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 78 12 (197016738149977 / 800000000000)) (orderedInterval (45983357106 / 1000000000000) (45983373137 / 1000000000000), orderedInterval (-21785877755 / 1000000000000) (-21785861724 / 1000000000000))) = true
  norm_num [besselStateAtRationalPoint, besselIntervalStepZero,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, besselZeroTransition,
    besselInitial, besselGridStateAt, besselGridStateBlock00, besselGridStateBlock01,
    besselGridStateBlock02, besselGridStateBlock03, besselGridStateBlock04,
    besselGridStateBlock05, besselGridStateBlock06, besselGridStateBlock07,
    besselGridStateBlock08, besselGridStateBlock09, besselGridStateBlock10,
    besselGridStateBlock11, besselGridStateBlock12, besselGridStateBlock13,
    besselGridStateBlock14, besselGridState007, besselGridState010, besselGridState016, besselGridState019, besselGridState020, besselGridState025, besselGridState027, besselGridState030, besselGridState034, besselGridState035, besselGridState037, besselGridState040, besselGridState041, besselGridState043, besselGridState044, besselGridState049, besselGridState050, besselGridState052, besselGridState054, besselGridState059, besselGridState063, besselGridState064, besselGridState068, besselGridState073, besselGridState077, besselGridState078, besselStateSubset, linearInterval, widenInterval,
    rationalErrorInterval, rationalIntervalSubset, orderedInterval, Finset.sum_range_succ,
    IntervalRat.add, IntervalRat.mul, IntervalRat.scale, IntervalRat.singleton]

theorem compactCertificate230_stateChecks4 :
    compactCertificate230.stateChecks 12 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 73 12 (184078593118813 / 800000000000)) (orderedInterval (-52584553240 / 1000000000000) (-52584553179 / 1000000000000), orderedInterval (-1146100769 / 1000000000000) (-1146100709 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 52 12 (131367169922029 / 800000000000)) (orderedInterval (62152530685 / 1000000000000) (62152530809 / 1000000000000), orderedInterval (-3921964145 / 1000000000000) (-3921964021 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 59 12 (148956369450891 / 800000000000)) (orderedInterval (-58383121593 / 1000000000000) (-58383121457 / 1000000000000), orderedInterval (3396036221 / 1000000000000) (3396036357 / 1000000000000))) = true
  norm_num [besselStateAtRationalPoint, besselIntervalStepZero,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, besselZeroTransition,
    besselInitial, besselGridStateAt, besselGridStateBlock00, besselGridStateBlock01,
    besselGridStateBlock02, besselGridStateBlock03, besselGridStateBlock04,
    besselGridStateBlock05, besselGridStateBlock06, besselGridStateBlock07,
    besselGridStateBlock08, besselGridStateBlock09, besselGridStateBlock10,
    besselGridStateBlock11, besselGridStateBlock12, besselGridStateBlock13,
    besselGridStateBlock14, besselGridState007, besselGridState010, besselGridState016, besselGridState019, besselGridState020, besselGridState025, besselGridState027, besselGridState030, besselGridState034, besselGridState035, besselGridState037, besselGridState040, besselGridState041, besselGridState043, besselGridState044, besselGridState049, besselGridState050, besselGridState052, besselGridState054, besselGridState059, besselGridState063, besselGridState064, besselGridState068, besselGridState073, besselGridState077, besselGridState078, besselStateSubset, linearInterval, widenInterval,
    rationalErrorInterval, rationalIntervalSubset, orderedInterval, Finset.sum_range_succ,
    IntervalRat.add, IntervalRat.mul, IntervalRat.scale, IntervalRat.singleton]

theorem compactCertificate230_stateChecks5 :
    compactCertificate230.stateChecks 15 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 49 12 (124184291365979 / 800000000000)) (orderedInterval (-56011328530 / 1000000000000) (-56011309227 / 1000000000000), orderedInterval (31226335147 / 1000000000000) (31226354451 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 44 12 (109720587553559 / 800000000000)) (orderedInterval (-19798741539 / 1000000000000) (-19798741176 / 1000000000000), orderedInterval (65262575926 / 1000000000000) (65262576289 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 63 12 (31801302838341 / 160000000000)) (orderedInterval (-56519000755 / 1000000000000) (-56519000614 / 1000000000000), orderedInterval (3071276008 / 1000000000000) (3071276149 / 1000000000000))) = true
  norm_num [besselStateAtRationalPoint, besselIntervalStepZero,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, besselZeroTransition,
    besselInitial, besselGridStateAt, besselGridStateBlock00, besselGridStateBlock01,
    besselGridStateBlock02, besselGridStateBlock03, besselGridStateBlock04,
    besselGridStateBlock05, besselGridStateBlock06, besselGridStateBlock07,
    besselGridStateBlock08, besselGridStateBlock09, besselGridStateBlock10,
    besselGridStateBlock11, besselGridStateBlock12, besselGridStateBlock13,
    besselGridStateBlock14, besselGridState007, besselGridState010, besselGridState016, besselGridState019, besselGridState020, besselGridState025, besselGridState027, besselGridState030, besselGridState034, besselGridState035, besselGridState037, besselGridState040, besselGridState041, besselGridState043, besselGridState044, besselGridState049, besselGridState050, besselGridState052, besselGridState054, besselGridState059, besselGridState063, besselGridState064, besselGridState068, besselGridState073, besselGridState077, besselGridState078, besselStateSubset, linearInterval, widenInterval,
    rationalErrorInterval, rationalIntervalSubset, orderedInterval, Finset.sum_range_succ,
    IntervalRat.add, IntervalRat.mul, IntervalRat.scale, IntervalRat.singleton]

theorem compactCertificate230_stateChecks6 :
    compactCertificate230.stateChecks 18 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 35 12 (87964077261727 / 800000000000)) (orderedInterval (-53708048654 / 1000000000000) (-53708048653 / 1000000000000), orderedInterval (-53656257239 / 1000000000000) (-53656257238 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 30 12 (74568122470247 / 800000000000)) (orderedInterval (-20731849100 / 1000000000000) (-20731848818 / 1000000000000), orderedInterval (80112560194 / 1000000000000) (80112560477 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 19 12 (46661268732941 / 800000000000)) (orderedInterval (57289624526 / 1000000000000) (57289638057 / 1000000000000), orderedInterval (-87856990765 / 1000000000000) (-87856977234 / 1000000000000))) = true
  norm_num [besselStateAtRationalPoint, besselIntervalStepZero,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, besselZeroTransition,
    besselInitial, besselGridStateAt, besselGridStateBlock00, besselGridStateBlock01,
    besselGridStateBlock02, besselGridStateBlock03, besselGridStateBlock04,
    besselGridStateBlock05, besselGridStateBlock06, besselGridStateBlock07,
    besselGridStateBlock08, besselGridStateBlock09, besselGridStateBlock10,
    besselGridStateBlock11, besselGridStateBlock12, besselGridStateBlock13,
    besselGridStateBlock14, besselGridState007, besselGridState010, besselGridState016, besselGridState019, besselGridState020, besselGridState025, besselGridState027, besselGridState030, besselGridState034, besselGridState035, besselGridState037, besselGridState040, besselGridState041, besselGridState043, besselGridState044, besselGridState049, besselGridState050, besselGridState052, besselGridState054, besselGridState059, besselGridState063, besselGridState064, besselGridState068, besselGridState073, besselGridState077, besselGridState078, besselStateSubset, linearInterval, widenInterval,
    rationalErrorInterval, rationalIntervalSubset, orderedInterval, Finset.sum_range_succ,
    IntervalRat.add, IntervalRat.mul, IntervalRat.scale, IntervalRat.singleton]

theorem compactCertificate230_stateChecks7 :
    compactCertificate230.stateChecks 21 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 10 12 (25094585512947 / 800000000000)) (orderedInterval (95390982148 / 1000000000000) (95390982149 / 1000000000000), orderedInterval (104290440415 / 1000000000000) (104290440416 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 27 12 (68136681259841 / 800000000000)) (orderedInterval (-78256639128 / 1000000000000) (-78256639127 / 1000000000000), orderedInterval (-36288891029 / 1000000000000) (-36288891028 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 37 12 (93034813076257 / 800000000000)) (orderedInterval (-55040743071 / 1000000000000) (-55040743070 / 1000000000000), orderedInterval (-49207884229 / 1000000000000) (-49207884228 / 1000000000000))) = true
  norm_num [besselStateAtRationalPoint, besselIntervalStepZero,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, besselZeroTransition,
    besselInitial, besselGridStateAt, besselGridStateBlock00, besselGridStateBlock01,
    besselGridStateBlock02, besselGridStateBlock03, besselGridStateBlock04,
    besselGridStateBlock05, besselGridStateBlock06, besselGridStateBlock07,
    besselGridStateBlock08, besselGridStateBlock09, besselGridStateBlock10,
    besselGridStateBlock11, besselGridStateBlock12, besselGridStateBlock13,
    besselGridStateBlock14, besselGridState007, besselGridState010, besselGridState016, besselGridState019, besselGridState020, besselGridState025, besselGridState027, besselGridState030, besselGridState034, besselGridState035, besselGridState037, besselGridState040, besselGridState041, besselGridState043, besselGridState044, besselGridState049, besselGridState050, besselGridState052, besselGridState054, besselGridState059, besselGridState063, besselGridState064, besselGridState068, besselGridState073, besselGridState077, besselGridState078, besselStateSubset, linearInterval, widenInterval,
    rationalErrorInterval, rationalIntervalSubset, orderedInterval, Finset.sum_range_succ,
    IntervalRat.add, IntervalRat.mul, IntervalRat.scale, IntervalRat.singleton]

theorem compactCertificate230_stateChecks8 :
    compactCertificate230.stateChecks 24 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 16 12 (39338731267059 / 800000000000)) (orderedInterval (-34623961687 / 1000000000000) (-34623960944 / 1000000000000), orderedInterval (108740898441 / 1000000000000) (108740899185 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 64 12 (159909758579539 / 800000000000)) (orderedInterval (-21453701448 / 1000000000000) (-21453700646 / 1000000000000), orderedInterval (52251757274 / 1000000000000) (52251758076 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 43 12 (106812307863101 / 800000000000)) (orderedInterval (48984623724 / 1000000000000) (48984688780 / 1000000000000), orderedInterval (-48852156688 / 1000000000000) (-48852091632 / 1000000000000))) = true
  norm_num [besselStateAtRationalPoint, besselIntervalStepZero,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, besselZeroTransition,
    besselInitial, besselGridStateAt, besselGridStateBlock00, besselGridStateBlock01,
    besselGridStateBlock02, besselGridStateBlock03, besselGridStateBlock04,
    besselGridStateBlock05, besselGridStateBlock06, besselGridStateBlock07,
    besselGridStateBlock08, besselGridStateBlock09, besselGridStateBlock10,
    besselGridStateBlock11, besselGridStateBlock12, besselGridStateBlock13,
    besselGridStateBlock14, besselGridState007, besselGridState010, besselGridState016, besselGridState019, besselGridState020, besselGridState025, besselGridState027, besselGridState030, besselGridState034, besselGridState035, besselGridState037, besselGridState040, besselGridState041, besselGridState043, besselGridState044, besselGridState049, besselGridState050, besselGridState052, besselGridState054, besselGridState059, besselGridState063, besselGridState064, besselGridState068, besselGridState073, besselGridState077, besselGridState078, besselStateSubset, linearInterval, widenInterval,
    rationalErrorInterval, rationalIntervalSubset, orderedInterval, Finset.sum_range_succ,
    IntervalRat.add, IntervalRat.mul, IntervalRat.scale, IntervalRat.singleton]

theorem compactCertificate230_states : ∀ j,
    BesselStateValid (compactCertificate230.point j) (compactCertificate230.state j) :=
  compactCertificate230.statesValid_of_checks3 compactCertificate230_stateChecks0
    compactCertificate230_stateChecks1 compactCertificate230_stateChecks2
    compactCertificate230_stateChecks3 compactCertificate230_stateChecks4
    compactCertificate230_stateChecks5 compactCertificate230_stateChecks6
    compactCertificate230_stateChecks7 compactCertificate230_stateChecks8

theorem compactCertificate230_chunkChecks0_0 :
    compactCertificate230.chunkChecks (0 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 0) <| besselDerivativeNearFromState (215 / 2) 0 (IntervalRat.scale (215 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (76564470193 / 1000000000000) (76564470200 / 1000000000000), orderedInterval (7381047438 / 1000000000000) (7381047445 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 0) <| besselDerivativeNearFromState (63347210759743 / 800000000000) 0 (IntervalRat.scale (215 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-88751375686 / 1000000000000) (-88751375683 / 1000000000000), orderedInterval (-12198561207 / 1000000000000) (-12198561204 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 0) <| besselDerivativeNearFromState (20485186409119 / 160000000000) 0 (IntervalRat.scale (215 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-813588062 / 1000000000000) (-813588057 / 1000000000000), orderedInterval (-70507167709 / 1000000000000) (-70507167704 / 1000000000000)))) (orderedInterval (29472742769 / 1000000000000) (29472742781 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 0) <| besselDerivativeNearFromState (18484558109501 / 800000000000) 0 (IntervalRat.scale (215 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-157347998143 / 1000000000000) (-157347996645 / 1000000000000), orderedInterval (56214171804 / 1000000000000) (56214173302 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 0) <| besselDerivativeNearFromState (49652123150297 / 800000000000) 0 (IntervalRat.scale (215 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (1689750877 / 1000000000000) (1689750884 / 1000000000000), orderedInterval (101252172342 / 1000000000000) (101252172349 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 0) <| besselDerivativeNearFromState (134815173066549 / 800000000000) 0 (IntervalRat.scale (215 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-20635043988 / 1000000000000) (-20635043445 / 1000000000000), orderedInterval (57957178088 / 1000000000000) (57957178631 / 1000000000000)))) (orderedInterval (3235747782 / 1000000000000) (3235747851 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 0) <| besselDerivativeNearFromState (99304246300637 / 800000000000) 0 (IntervalRat.scale (215 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-48763011405 / 1000000000000) (-48762963465 / 1000000000000), orderedInterval (52644601357 / 1000000000000) (52644649298 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 0) <| besselDerivativeNearFromState (170159518622801 / 800000000000) 0 (IntervalRat.scale (215 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-7855817024 / 1000000000000) (-7855816998 / 1000000000000), orderedInterval (54160348102 / 1000000000000) (54160348128 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 0) <| besselDerivativeNearFromState (125338731267059 / 800000000000) 0 (IntervalRat.scale (215 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (23548235955 / 1000000000000) (23548235956 / 1000000000000), orderedInterval (59160405981 / 1000000000000) (59160405982 / 1000000000000)))) (orderedInterval (811419226 / 1000000000000) (811419234 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate230_chunkChecks0_1 :
    compactCertificate230.chunkChecks (0 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 0) <| besselDerivativeNearFromState (192301846064957 / 800000000000) 0 (IntervalRat.scale (215 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (34717730774 / 1000000000000) (34717756912 / 1000000000000), orderedInterval (-38060350692 / 1000000000000) (-38060324553 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 0) <| besselDerivativeNearFromState (111025522591253 / 800000000000) 0 (IntervalRat.scale (215 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (65875367097 / 1000000000000) (65875367099 / 1000000000000), orderedInterval (15498148527 / 1000000000000) (15498148529 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 0) <| besselDerivativeNearFromState (197016738149977 / 800000000000) 0 (IntervalRat.scale (215 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (45983357106 / 1000000000000) (45983373137 / 1000000000000), orderedInterval (-21785877755 / 1000000000000) (-21785861724 / 1000000000000)))) (orderedInterval (5248701517 / 1000000000000) (5248708484 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 0) <| besselDerivativeNearFromState (184078593118813 / 800000000000) 0 (IntervalRat.scale (215 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-52584553240 / 1000000000000) (-52584553179 / 1000000000000), orderedInterval (-1146100769 / 1000000000000) (-1146100709 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 0) <| besselDerivativeNearFromState (131367169922029 / 800000000000) 0 (IntervalRat.scale (215 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (62152530685 / 1000000000000) (62152530809 / 1000000000000), orderedInterval (-3921964145 / 1000000000000) (-3921964021 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 0) <| besselDerivativeNearFromState (148956369450891 / 800000000000) 0 (IntervalRat.scale (215 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-58383121593 / 1000000000000) (-58383121457 / 1000000000000), orderedInterval (3396036221 / 1000000000000) (3396036357 / 1000000000000)))) (orderedInterval (7122087108 / 1000000000000) (7122087135 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 0) <| besselDerivativeNearFromState (124184291365979 / 800000000000) 0 (IntervalRat.scale (215 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-56011328530 / 1000000000000) (-56011309227 / 1000000000000), orderedInterval (31226335147 / 1000000000000) (31226354451 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 0) <| besselDerivativeNearFromState (109720587553559 / 800000000000) 0 (IntervalRat.scale (215 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-19798741539 / 1000000000000) (-19798741176 / 1000000000000), orderedInterval (65262575926 / 1000000000000) (65262576289 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 0) <| besselDerivativeNearFromState (31801302838341 / 160000000000) 0 (IntervalRat.scale (215 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-56519000755 / 1000000000000) (-56519000614 / 1000000000000), orderedInterval (3071276008 / 1000000000000) (3071276149 / 1000000000000)))) (orderedInterval (-960893847 / 1000000000000) (-960893588 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate230_chunkChecks0_2 :
    compactCertificate230.chunkChecks (0 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 0) <| besselDerivativeNearFromState (87964077261727 / 800000000000) 0 (IntervalRat.scale (215 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-53708048654 / 1000000000000) (-53708048653 / 1000000000000), orderedInterval (-53656257239 / 1000000000000) (-53656257238 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 0) <| besselDerivativeNearFromState (74568122470247 / 800000000000) 0 (IntervalRat.scale (215 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-20731849100 / 1000000000000) (-20731848818 / 1000000000000), orderedInterval (80112560194 / 1000000000000) (80112560477 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 0) <| besselDerivativeNearFromState (46661268732941 / 800000000000) 0 (IntervalRat.scale (215 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (57289624526 / 1000000000000) (57289638057 / 1000000000000), orderedInterval (-87856990765 / 1000000000000) (-87856977234 / 1000000000000)))) (orderedInterval (11626012023 / 1000000000000) (11626012508 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 0) <| besselDerivativeNearFromState (25094585512947 / 800000000000) 0 (IntervalRat.scale (215 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (95390982148 / 1000000000000) (95390982149 / 1000000000000), orderedInterval (104290440415 / 1000000000000) (104290440416 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 0) <| besselDerivativeNearFromState (68136681259841 / 800000000000) 0 (IntervalRat.scale (215 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-78256639128 / 1000000000000) (-78256639127 / 1000000000000), orderedInterval (-36288891029 / 1000000000000) (-36288891028 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 0) <| besselDerivativeNearFromState (93034813076257 / 800000000000) 0 (IntervalRat.scale (215 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-55040743071 / 1000000000000) (-55040743070 / 1000000000000), orderedInterval (-49207884229 / 1000000000000) (-49207884228 / 1000000000000)))) (orderedInterval (4232252272 / 1000000000000) (4232252286 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 0) <| besselDerivativeNearFromState (39338731267059 / 800000000000) 0 (IntervalRat.scale (215 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-34623961687 / 1000000000000) (-34623960944 / 1000000000000), orderedInterval (108740898441 / 1000000000000) (108740899185 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 0) <| besselDerivativeNearFromState (159909758579539 / 800000000000) 0 (IntervalRat.scale (215 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-21453701448 / 1000000000000) (-21453700646 / 1000000000000), orderedInterval (52251757274 / 1000000000000) (52251758076 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 0) <| besselDerivativeNearFromState (106812307863101 / 800000000000) 0 (IntervalRat.scale (215 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (48984623724 / 1000000000000) (48984688780 / 1000000000000), orderedInterval (-48852156688 / 1000000000000) (-48852091632 / 1000000000000)))) (orderedInterval (-7653182289 / 1000000000000) (-7653169983 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate230_chunkChecks0 :
    compactCertificate230.chunkChecks (0 : Fin 5) 0 9 = true :=
  compactCertificate230.chunkChecks_nine_of_three (0 : Fin 5) compactCertificate230_chunkChecks0_0
    compactCertificate230_chunkChecks0_1 compactCertificate230_chunkChecks0_2

theorem compactCertificate230_chunkChecks1_0 :
    compactCertificate230.chunkChecks (1 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 1) <| besselDerivativeNearFromState (215 / 2) 1 (IntervalRat.scale (215 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (76564470193 / 1000000000000) (76564470200 / 1000000000000), orderedInterval (7381047438 / 1000000000000) (7381047445 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 1) <| besselDerivativeNearFromState (63347210759743 / 800000000000) 1 (IntervalRat.scale (215 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-88751375686 / 1000000000000) (-88751375683 / 1000000000000), orderedInterval (-12198561207 / 1000000000000) (-12198561204 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 1) <| besselDerivativeNearFromState (20485186409119 / 160000000000) 1 (IntervalRat.scale (215 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-813588062 / 1000000000000) (-813588057 / 1000000000000), orderedInterval (-70507167709 / 1000000000000) (-70507167704 / 1000000000000)))) (orderedInterval (-2085826668 / 1000000000000) (-2085826656 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 1) <| besselDerivativeNearFromState (18484558109501 / 800000000000) 1 (IntervalRat.scale (215 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-157347998143 / 1000000000000) (-157347996645 / 1000000000000), orderedInterval (56214171804 / 1000000000000) (56214173302 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 1) <| besselDerivativeNearFromState (49652123150297 / 800000000000) 1 (IntervalRat.scale (215 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (1689750877 / 1000000000000) (1689750884 / 1000000000000), orderedInterval (101252172342 / 1000000000000) (101252172349 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 1) <| besselDerivativeNearFromState (134815173066549 / 800000000000) 1 (IntervalRat.scale (215 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-20635043988 / 1000000000000) (-20635043445 / 1000000000000), orderedInterval (57957178088 / 1000000000000) (57957178631 / 1000000000000)))) (orderedInterval (-4455514322 / 1000000000000) (-4455514242 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 1) <| besselDerivativeNearFromState (99304246300637 / 800000000000) 1 (IntervalRat.scale (215 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-48763011405 / 1000000000000) (-48762963465 / 1000000000000), orderedInterval (52644601357 / 1000000000000) (52644649298 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 1) <| besselDerivativeNearFromState (170159518622801 / 800000000000) 1 (IntervalRat.scale (215 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-7855817024 / 1000000000000) (-7855816998 / 1000000000000), orderedInterval (54160348102 / 1000000000000) (54160348128 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 1) <| besselDerivativeNearFromState (125338731267059 / 800000000000) 1 (IntervalRat.scale (215 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (23548235955 / 1000000000000) (23548235956 / 1000000000000), orderedInterval (59160405981 / 1000000000000) (59160405982 / 1000000000000)))) (orderedInterval (-1221477796 / 1000000000000) (-1221477783 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate230_chunkChecks1_1 :
    compactCertificate230.chunkChecks (1 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 1) <| besselDerivativeNearFromState (192301846064957 / 800000000000) 1 (IntervalRat.scale (215 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (34717730774 / 1000000000000) (34717756912 / 1000000000000), orderedInterval (-38060350692 / 1000000000000) (-38060324553 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 1) <| besselDerivativeNearFromState (111025522591253 / 800000000000) 1 (IntervalRat.scale (215 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (65875367097 / 1000000000000) (65875367099 / 1000000000000), orderedInterval (15498148527 / 1000000000000) (15498148529 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 1) <| besselDerivativeNearFromState (197016738149977 / 800000000000) 1 (IntervalRat.scale (215 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (45983357106 / 1000000000000) (45983373137 / 1000000000000), orderedInterval (-21785877755 / 1000000000000) (-21785861724 / 1000000000000)))) (orderedInterval (9509772261 / 1000000000000) (9509787956 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 1) <| besselDerivativeNearFromState (184078593118813 / 800000000000) 1 (IntervalRat.scale (215 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-52584553240 / 1000000000000) (-52584553179 / 1000000000000), orderedInterval (-1146100769 / 1000000000000) (-1146100709 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 1) <| besselDerivativeNearFromState (131367169922029 / 800000000000) 1 (IntervalRat.scale (215 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (62152530685 / 1000000000000) (62152530809 / 1000000000000), orderedInterval (-3921964145 / 1000000000000) (-3921964021 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 1) <| besselDerivativeNearFromState (148956369450891 / 800000000000) 1 (IntervalRat.scale (215 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-58383121593 / 1000000000000) (-58383121457 / 1000000000000), orderedInterval (3396036221 / 1000000000000) (3396036357 / 1000000000000)))) (orderedInterval (-551996174 / 1000000000000) (-551996131 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 1) <| besselDerivativeNearFromState (124184291365979 / 800000000000) 1 (IntervalRat.scale (215 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-56011328530 / 1000000000000) (-56011309227 / 1000000000000), orderedInterval (31226335147 / 1000000000000) (31226354451 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 1) <| besselDerivativeNearFromState (109720587553559 / 800000000000) 1 (IntervalRat.scale (215 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-19798741539 / 1000000000000) (-19798741176 / 1000000000000), orderedInterval (65262575926 / 1000000000000) (65262576289 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 1) <| besselDerivativeNearFromState (31801302838341 / 160000000000) 1 (IntervalRat.scale (215 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-56519000755 / 1000000000000) (-56519000614 / 1000000000000), orderedInterval (3071276008 / 1000000000000) (3071276149 / 1000000000000)))) (orderedInterval (-4098797105 / 1000000000000) (-4098796734 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate230_chunkChecks1_2 :
    compactCertificate230.chunkChecks (1 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 1) <| besselDerivativeNearFromState (87964077261727 / 800000000000) 1 (IntervalRat.scale (215 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-53708048654 / 1000000000000) (-53708048653 / 1000000000000), orderedInterval (-53656257239 / 1000000000000) (-53656257238 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 1) <| besselDerivativeNearFromState (74568122470247 / 800000000000) 1 (IntervalRat.scale (215 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-20731849100 / 1000000000000) (-20731848818 / 1000000000000), orderedInterval (80112560194 / 1000000000000) (80112560477 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 1) <| besselDerivativeNearFromState (46661268732941 / 800000000000) 1 (IntervalRat.scale (215 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (57289624526 / 1000000000000) (57289638057 / 1000000000000), orderedInterval (-87856990765 / 1000000000000) (-87856977234 / 1000000000000)))) (orderedInterval (3291672617 / 1000000000000) (3291672895 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 1) <| besselDerivativeNearFromState (25094585512947 / 800000000000) 1 (IntervalRat.scale (215 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (95390982148 / 1000000000000) (95390982149 / 1000000000000), orderedInterval (104290440415 / 1000000000000) (104290440416 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 1) <| besselDerivativeNearFromState (68136681259841 / 800000000000) 1 (IntervalRat.scale (215 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-78256639128 / 1000000000000) (-78256639127 / 1000000000000), orderedInterval (-36288891029 / 1000000000000) (-36288891028 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 1) <| besselDerivativeNearFromState (93034813076257 / 800000000000) 1 (IntervalRat.scale (215 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-55040743071 / 1000000000000) (-55040743070 / 1000000000000), orderedInterval (-49207884229 / 1000000000000) (-49207884228 / 1000000000000)))) (orderedInterval (4170074519 / 1000000000000) (4170074532 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 1) <| besselDerivativeNearFromState (39338731267059 / 800000000000) 1 (IntervalRat.scale (215 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-34623961687 / 1000000000000) (-34623960944 / 1000000000000), orderedInterval (108740898441 / 1000000000000) (108740899185 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 1) <| besselDerivativeNearFromState (159909758579539 / 800000000000) 1 (IntervalRat.scale (215 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-21453701448 / 1000000000000) (-21453700646 / 1000000000000), orderedInterval (52251757274 / 1000000000000) (52251758076 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 1) <| besselDerivativeNearFromState (106812307863101 / 800000000000) 1 (IntervalRat.scale (215 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (48984623724 / 1000000000000) (48984688780 / 1000000000000), orderedInterval (-48852156688 / 1000000000000) (-48852091632 / 1000000000000)))) (orderedInterval (3775182794 / 1000000000000) (3775198121 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate230_chunkChecks1 :
    compactCertificate230.chunkChecks (1 : Fin 5) 0 9 = true :=
  compactCertificate230.chunkChecks_nine_of_three (1 : Fin 5) compactCertificate230_chunkChecks1_0
    compactCertificate230_chunkChecks1_1 compactCertificate230_chunkChecks1_2

theorem compactCertificate230_chunkChecks2_0 :
    compactCertificate230.chunkChecks (2 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 2) <| besselDerivativeNearFromState (215 / 2) 2 (IntervalRat.scale (215 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (76564470193 / 1000000000000) (76564470200 / 1000000000000), orderedInterval (7381047438 / 1000000000000) (7381047445 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 2) <| besselDerivativeNearFromState (63347210759743 / 800000000000) 2 (IntervalRat.scale (215 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-88751375686 / 1000000000000) (-88751375683 / 1000000000000), orderedInterval (-12198561207 / 1000000000000) (-12198561204 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 2) <| besselDerivativeNearFromState (20485186409119 / 160000000000) 2 (IntervalRat.scale (215 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-813588062 / 1000000000000) (-813588057 / 1000000000000), orderedInterval (-70507167709 / 1000000000000) (-70507167704 / 1000000000000)))) (orderedInterval (-29811648536 / 1000000000000) (-29811648523 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 2) <| besselDerivativeNearFromState (18484558109501 / 800000000000) 2 (IntervalRat.scale (215 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-157347998143 / 1000000000000) (-157347996645 / 1000000000000), orderedInterval (56214171804 / 1000000000000) (56214173302 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 2) <| besselDerivativeNearFromState (49652123150297 / 800000000000) 2 (IntervalRat.scale (215 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (1689750877 / 1000000000000) (1689750884 / 1000000000000), orderedInterval (101252172342 / 1000000000000) (101252172349 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 2) <| besselDerivativeNearFromState (134815173066549 / 800000000000) 2 (IntervalRat.scale (215 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-20635043988 / 1000000000000) (-20635043445 / 1000000000000), orderedInterval (57957178088 / 1000000000000) (57957178631 / 1000000000000)))) (orderedInterval (-3662876415 / 1000000000000) (-3662876298 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 2) <| besselDerivativeNearFromState (99304246300637 / 800000000000) 2 (IntervalRat.scale (215 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-48763011405 / 1000000000000) (-48762963465 / 1000000000000), orderedInterval (52644601357 / 1000000000000) (52644649298 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 2) <| besselDerivativeNearFromState (170159518622801 / 800000000000) 2 (IntervalRat.scale (215 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-7855817024 / 1000000000000) (-7855816998 / 1000000000000), orderedInterval (54160348102 / 1000000000000) (54160348128 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 2) <| besselDerivativeNearFromState (125338731267059 / 800000000000) 2 (IntervalRat.scale (215 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (23548235955 / 1000000000000) (23548235956 / 1000000000000), orderedInterval (59160405981 / 1000000000000) (59160405982 / 1000000000000)))) (orderedInterval (-2146077863 / 1000000000000) (-2146077840 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate230_chunkChecks2_1 :
    compactCertificate230.chunkChecks (2 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 2) <| besselDerivativeNearFromState (192301846064957 / 800000000000) 2 (IntervalRat.scale (215 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (34717730774 / 1000000000000) (34717756912 / 1000000000000), orderedInterval (-38060350692 / 1000000000000) (-38060324553 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 2) <| besselDerivativeNearFromState (111025522591253 / 800000000000) 2 (IntervalRat.scale (215 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (65875367097 / 1000000000000) (65875367099 / 1000000000000), orderedInterval (15498148527 / 1000000000000) (15498148529 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 2) <| besselDerivativeNearFromState (197016738149977 / 800000000000) 2 (IntervalRat.scale (215 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (45983357106 / 1000000000000) (45983373137 / 1000000000000), orderedInterval (-21785877755 / 1000000000000) (-21785861724 / 1000000000000)))) (orderedInterval (-11684951051 / 1000000000000) (-11684915533 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 2) <| besselDerivativeNearFromState (184078593118813 / 800000000000) 2 (IntervalRat.scale (215 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-52584553240 / 1000000000000) (-52584553179 / 1000000000000), orderedInterval (-1146100769 / 1000000000000) (-1146100709 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 2) <| besselDerivativeNearFromState (131367169922029 / 800000000000) 2 (IntervalRat.scale (215 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (62152530685 / 1000000000000) (62152530809 / 1000000000000), orderedInterval (-3921964145 / 1000000000000) (-3921964021 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 2) <| besselDerivativeNearFromState (148956369450891 / 800000000000) 2 (IntervalRat.scale (215 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-58383121593 / 1000000000000) (-58383121457 / 1000000000000), orderedInterval (3396036221 / 1000000000000) (3396036357 / 1000000000000)))) (orderedInterval (-18944271323 / 1000000000000) (-18944271254 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 2) <| besselDerivativeNearFromState (124184291365979 / 800000000000) 2 (IntervalRat.scale (215 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-56011328530 / 1000000000000) (-56011309227 / 1000000000000), orderedInterval (31226335147 / 1000000000000) (31226354451 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 2) <| besselDerivativeNearFromState (109720587553559 / 800000000000) 2 (IntervalRat.scale (215 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-19798741539 / 1000000000000) (-19798741176 / 1000000000000), orderedInterval (65262575926 / 1000000000000) (65262576289 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 2) <| besselDerivativeNearFromState (31801302838341 / 160000000000) 2 (IntervalRat.scale (215 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-56519000755 / 1000000000000) (-56519000614 / 1000000000000), orderedInterval (3071276008 / 1000000000000) (3071276149 / 1000000000000)))) (orderedInterval (4489483429 / 1000000000000) (4489483966 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate230_chunkChecks2_2 :
    compactCertificate230.chunkChecks (2 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 2) <| besselDerivativeNearFromState (87964077261727 / 800000000000) 2 (IntervalRat.scale (215 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-53708048654 / 1000000000000) (-53708048653 / 1000000000000), orderedInterval (-53656257239 / 1000000000000) (-53656257238 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 2) <| besselDerivativeNearFromState (74568122470247 / 800000000000) 2 (IntervalRat.scale (215 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-20731849100 / 1000000000000) (-20731848818 / 1000000000000), orderedInterval (80112560194 / 1000000000000) (80112560477 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 2) <| besselDerivativeNearFromState (46661268732941 / 800000000000) 2 (IntervalRat.scale (215 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (57289624526 / 1000000000000) (57289638057 / 1000000000000), orderedInterval (-87856990765 / 1000000000000) (-87856977234 / 1000000000000)))) (orderedInterval (-10446100556 / 1000000000000) (-10446100388 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 2) <| besselDerivativeNearFromState (25094585512947 / 800000000000) 2 (IntervalRat.scale (215 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (95390982148 / 1000000000000) (95390982149 / 1000000000000), orderedInterval (104290440415 / 1000000000000) (104290440416 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 2) <| besselDerivativeNearFromState (68136681259841 / 800000000000) 2 (IntervalRat.scale (215 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-78256639128 / 1000000000000) (-78256639127 / 1000000000000), orderedInterval (-36288891029 / 1000000000000) (-36288891028 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 2) <| besselDerivativeNearFromState (93034813076257 / 800000000000) 2 (IntervalRat.scale (215 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-55040743071 / 1000000000000) (-55040743070 / 1000000000000), orderedInterval (-49207884229 / 1000000000000) (-49207884228 / 1000000000000)))) (orderedInterval (-5939859873 / 1000000000000) (-5939859861 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 2) <| besselDerivativeNearFromState (39338731267059 / 800000000000) 2 (IntervalRat.scale (215 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-34623961687 / 1000000000000) (-34623960944 / 1000000000000), orderedInterval (108740898441 / 1000000000000) (108740899185 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 2) <| besselDerivativeNearFromState (159909758579539 / 800000000000) 2 (IntervalRat.scale (215 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-21453701448 / 1000000000000) (-21453700646 / 1000000000000), orderedInterval (52251757274 / 1000000000000) (52251758076 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 2) <| besselDerivativeNearFromState (106812307863101 / 800000000000) 2 (IntervalRat.scale (215 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (48984623724 / 1000000000000) (48984688780 / 1000000000000), orderedInterval (-48852156688 / 1000000000000) (-48852091632 / 1000000000000)))) (orderedInterval (8148112120 / 1000000000000) (8148131380 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate230_chunkChecks2 :
    compactCertificate230.chunkChecks (2 : Fin 5) 0 9 = true :=
  compactCertificate230.chunkChecks_nine_of_three (2 : Fin 5) compactCertificate230_chunkChecks2_0
    compactCertificate230_chunkChecks2_1 compactCertificate230_chunkChecks2_2

theorem compactCertificate230_chunkChecks3_0 :
    compactCertificate230.chunkChecks (3 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 3) <| besselDerivativeNearFromState (215 / 2) 3 (IntervalRat.scale (215 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (76564470193 / 1000000000000) (76564470200 / 1000000000000), orderedInterval (7381047438 / 1000000000000) (7381047445 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 3) <| besselDerivativeNearFromState (63347210759743 / 800000000000) 3 (IntervalRat.scale (215 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-88751375686 / 1000000000000) (-88751375683 / 1000000000000), orderedInterval (-12198561207 / 1000000000000) (-12198561204 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 3) <| besselDerivativeNearFromState (20485186409119 / 160000000000) 3 (IntervalRat.scale (215 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-813588062 / 1000000000000) (-813588057 / 1000000000000), orderedInterval (-70507167709 / 1000000000000) (-70507167704 / 1000000000000)))) (orderedInterval (4386799951 / 1000000000000) (4386799966 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 3) <| besselDerivativeNearFromState (18484558109501 / 800000000000) 3 (IntervalRat.scale (215 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-157347998143 / 1000000000000) (-157347996645 / 1000000000000), orderedInterval (56214171804 / 1000000000000) (56214173302 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 3) <| besselDerivativeNearFromState (49652123150297 / 800000000000) 3 (IntervalRat.scale (215 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (1689750877 / 1000000000000) (1689750884 / 1000000000000), orderedInterval (101252172342 / 1000000000000) (101252172349 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 3) <| besselDerivativeNearFromState (134815173066549 / 800000000000) 3 (IntervalRat.scale (215 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-20635043988 / 1000000000000) (-20635043445 / 1000000000000), orderedInterval (57957178088 / 1000000000000) (57957178631 / 1000000000000)))) (orderedInterval (15200380805 / 1000000000000) (15200380986 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 3) <| besselDerivativeNearFromState (99304246300637 / 800000000000) 3 (IntervalRat.scale (215 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-48763011405 / 1000000000000) (-48762963465 / 1000000000000), orderedInterval (52644601357 / 1000000000000) (52644649298 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 3) <| besselDerivativeNearFromState (170159518622801 / 800000000000) 3 (IntervalRat.scale (215 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-7855817024 / 1000000000000) (-7855816998 / 1000000000000), orderedInterval (54160348102 / 1000000000000) (54160348128 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 3) <| besselDerivativeNearFromState (125338731267059 / 800000000000) 3 (IntervalRat.scale (215 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (23548235955 / 1000000000000) (23548235956 / 1000000000000), orderedInterval (59160405981 / 1000000000000) (59160405982 / 1000000000000)))) (orderedInterval (8533378962 / 1000000000000) (8533379003 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate230_chunkChecks3_1 :
    compactCertificate230.chunkChecks (3 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 3) <| besselDerivativeNearFromState (192301846064957 / 800000000000) 3 (IntervalRat.scale (215 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (34717730774 / 1000000000000) (34717756912 / 1000000000000), orderedInterval (-38060350692 / 1000000000000) (-38060324553 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 3) <| besselDerivativeNearFromState (111025522591253 / 800000000000) 3 (IntervalRat.scale (215 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (65875367097 / 1000000000000) (65875367099 / 1000000000000), orderedInterval (15498148527 / 1000000000000) (15498148529 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 3) <| besselDerivativeNearFromState (197016738149977 / 800000000000) 3 (IntervalRat.scale (215 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (45983357106 / 1000000000000) (45983373137 / 1000000000000), orderedInterval (-21785877755 / 1000000000000) (-21785861724 / 1000000000000)))) (orderedInterval (-40737129185 / 1000000000000) (-40737049117 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 3) <| besselDerivativeNearFromState (184078593118813 / 800000000000) 3 (IntervalRat.scale (215 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-52584553240 / 1000000000000) (-52584553179 / 1000000000000), orderedInterval (-1146100769 / 1000000000000) (-1146100709 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 3) <| besselDerivativeNearFromState (131367169922029 / 800000000000) 3 (IntervalRat.scale (215 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (62152530685 / 1000000000000) (62152530809 / 1000000000000), orderedInterval (-3921964145 / 1000000000000) (-3921964021 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 3) <| besselDerivativeNearFromState (148956369450891 / 800000000000) 3 (IntervalRat.scale (215 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-58383121593 / 1000000000000) (-58383121457 / 1000000000000), orderedInterval (3396036221 / 1000000000000) (3396036357 / 1000000000000)))) (orderedInterval (1384447418 / 1000000000000) (1384447534 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 3) <| besselDerivativeNearFromState (124184291365979 / 800000000000) 3 (IntervalRat.scale (215 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-56011328530 / 1000000000000) (-56011309227 / 1000000000000), orderedInterval (31226335147 / 1000000000000) (31226354451 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 3) <| besselDerivativeNearFromState (109720587553559 / 800000000000) 3 (IntervalRat.scale (215 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-19798741539 / 1000000000000) (-19798741176 / 1000000000000), orderedInterval (65262575926 / 1000000000000) (65262576289 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 3) <| besselDerivativeNearFromState (31801302838341 / 160000000000) 3 (IntervalRat.scale (215 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-56519000755 / 1000000000000) (-56519000614 / 1000000000000), orderedInterval (3071276008 / 1000000000000) (3071276149 / 1000000000000)))) (orderedInterval (6131027094 / 1000000000000) (6131027871 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate230_chunkChecks3_2 :
    compactCertificate230.chunkChecks (3 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 3) <| besselDerivativeNearFromState (87964077261727 / 800000000000) 3 (IntervalRat.scale (215 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-53708048654 / 1000000000000) (-53708048653 / 1000000000000), orderedInterval (-53656257239 / 1000000000000) (-53656257238 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 3) <| besselDerivativeNearFromState (74568122470247 / 800000000000) 3 (IntervalRat.scale (215 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-20731849100 / 1000000000000) (-20731848818 / 1000000000000), orderedInterval (80112560194 / 1000000000000) (80112560477 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 3) <| besselDerivativeNearFromState (46661268732941 / 800000000000) 3 (IntervalRat.scale (215 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (57289624526 / 1000000000000) (57289638057 / 1000000000000), orderedInterval (-87856990765 / 1000000000000) (-87856977234 / 1000000000000)))) (orderedInterval (-5670410227 / 1000000000000) (-5670410121 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 3) <| besselDerivativeNearFromState (25094585512947 / 800000000000) 3 (IntervalRat.scale (215 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (95390982148 / 1000000000000) (95390982149 / 1000000000000), orderedInterval (104290440415 / 1000000000000) (104290440416 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 3) <| besselDerivativeNearFromState (68136681259841 / 800000000000) 3 (IntervalRat.scale (215 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-78256639128 / 1000000000000) (-78256639127 / 1000000000000), orderedInterval (-36288891029 / 1000000000000) (-36288891028 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 3) <| besselDerivativeNearFromState (93034813076257 / 800000000000) 3 (IntervalRat.scale (215 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-55040743071 / 1000000000000) (-55040743070 / 1000000000000), orderedInterval (-49207884229 / 1000000000000) (-49207884228 / 1000000000000)))) (orderedInterval (-5080451284 / 1000000000000) (-5080451271 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 3) <| besselDerivativeNearFromState (39338731267059 / 800000000000) 3 (IntervalRat.scale (215 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-34623961687 / 1000000000000) (-34623960944 / 1000000000000), orderedInterval (108740898441 / 1000000000000) (108740899185 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 3) <| besselDerivativeNearFromState (159909758579539 / 800000000000) 3 (IntervalRat.scale (215 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-21453701448 / 1000000000000) (-21453700646 / 1000000000000), orderedInterval (52251757274 / 1000000000000) (52251758076 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 3) <| besselDerivativeNearFromState (106812307863101 / 800000000000) 3 (IntervalRat.scale (215 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (48984623724 / 1000000000000) (48984688780 / 1000000000000), orderedInterval (-48852156688 / 1000000000000) (-48852091632 / 1000000000000)))) (orderedInterval (9645042609 / 1000000000000) (9645066686 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate230_chunkChecks3 :
    compactCertificate230.chunkChecks (3 : Fin 5) 0 9 = true :=
  compactCertificate230.chunkChecks_nine_of_three (3 : Fin 5) compactCertificate230_chunkChecks3_0
    compactCertificate230_chunkChecks3_1 compactCertificate230_chunkChecks3_2

theorem compactCertificate230_chunkChecks4_0 :
    compactCertificate230.chunkChecks (4 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 4) <| besselDerivativeNearFromState (215 / 2) 4 (IntervalRat.scale (215 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (76564470193 / 1000000000000) (76564470200 / 1000000000000), orderedInterval (7381047438 / 1000000000000) (7381047445 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 4) <| besselDerivativeNearFromState (63347210759743 / 800000000000) 4 (IntervalRat.scale (215 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-88751375686 / 1000000000000) (-88751375683 / 1000000000000), orderedInterval (-12198561207 / 1000000000000) (-12198561204 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 4) <| besselDerivativeNearFromState (20485186409119 / 160000000000) 4 (IntervalRat.scale (215 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-813588062 / 1000000000000) (-813588057 / 1000000000000), orderedInterval (-70507167709 / 1000000000000) (-70507167704 / 1000000000000)))) (orderedInterval (29923767437 / 1000000000000) (29923767455 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 4) <| besselDerivativeNearFromState (18484558109501 / 800000000000) 4 (IntervalRat.scale (215 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-157347998143 / 1000000000000) (-157347996645 / 1000000000000), orderedInterval (56214171804 / 1000000000000) (56214173302 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 4) <| besselDerivativeNearFromState (49652123150297 / 800000000000) 4 (IntervalRat.scale (215 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (1689750877 / 1000000000000) (1689750884 / 1000000000000), orderedInterval (101252172342 / 1000000000000) (101252172349 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 4) <| besselDerivativeNearFromState (134815173066549 / 800000000000) 4 (IntervalRat.scale (215 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-20635043988 / 1000000000000) (-20635043445 / 1000000000000), orderedInterval (57957178088 / 1000000000000) (57957178631 / 1000000000000)))) (orderedInterval (8586148548 / 1000000000000) (8586148832 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 4) <| besselDerivativeNearFromState (99304246300637 / 800000000000) 4 (IntervalRat.scale (215 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-48763011405 / 1000000000000) (-48762963465 / 1000000000000), orderedInterval (52644601357 / 1000000000000) (52644649298 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 4) <| besselDerivativeNearFromState (170159518622801 / 800000000000) 4 (IntervalRat.scale (215 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-7855817024 / 1000000000000) (-7855816998 / 1000000000000), orderedInterval (54160348102 / 1000000000000) (54160348128 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 4) <| besselDerivativeNearFromState (125338731267059 / 800000000000) 4 (IntervalRat.scale (215 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (23548235955 / 1000000000000) (23548235956 / 1000000000000), orderedInterval (59160405981 / 1000000000000) (59160405982 / 1000000000000)))) (orderedInterval (6122354498 / 1000000000000) (6122354574 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate230_chunkChecks4_1 :
    compactCertificate230.chunkChecks (4 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 4) <| besselDerivativeNearFromState (192301846064957 / 800000000000) 4 (IntervalRat.scale (215 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (34717730774 / 1000000000000) (34717756912 / 1000000000000), orderedInterval (-38060350692 / 1000000000000) (-38060324553 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 4) <| besselDerivativeNearFromState (111025522591253 / 800000000000) 4 (IntervalRat.scale (215 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (65875367097 / 1000000000000) (65875367099 / 1000000000000), orderedInterval (15498148527 / 1000000000000) (15498148529 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 4) <| besselDerivativeNearFromState (197016738149977 / 800000000000) 4 (IntervalRat.scale (215 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (45983357106 / 1000000000000) (45983373137 / 1000000000000), orderedInterval (-21785877755 / 1000000000000) (-21785861724 / 1000000000000)))) (orderedInterval (40137877520 / 1000000000000) (40138058788 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 4) <| besselDerivativeNearFromState (184078593118813 / 800000000000) 4 (IntervalRat.scale (215 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-52584553240 / 1000000000000) (-52584553179 / 1000000000000), orderedInterval (-1146100769 / 1000000000000) (-1146100709 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 4) <| besselDerivativeNearFromState (131367169922029 / 800000000000) 4 (IntervalRat.scale (215 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (62152530685 / 1000000000000) (62152530809 / 1000000000000), orderedInterval (-3921964145 / 1000000000000) (-3921964021 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 4) <| besselDerivativeNearFromState (148956369450891 / 800000000000) 4 (IntervalRat.scale (215 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-58383121593 / 1000000000000) (-58383121457 / 1000000000000), orderedInterval (3396036221 / 1000000000000) (3396036357 / 1000000000000)))) (orderedInterval (54556830169 / 1000000000000) (54556830366 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 4) <| besselDerivativeNearFromState (124184291365979 / 800000000000) 4 (IntervalRat.scale (215 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-56011328530 / 1000000000000) (-56011309227 / 1000000000000), orderedInterval (31226335147 / 1000000000000) (31226354451 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 4) <| besselDerivativeNearFromState (109720587553559 / 800000000000) 4 (IntervalRat.scale (215 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-19798741539 / 1000000000000) (-19798741176 / 1000000000000), orderedInterval (65262575926 / 1000000000000) (65262576289 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 4) <| besselDerivativeNearFromState (31801302838341 / 160000000000) 4 (IntervalRat.scale (215 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-56519000755 / 1000000000000) (-56519000614 / 1000000000000), orderedInterval (3071276008 / 1000000000000) (3071276149 / 1000000000000)))) (orderedInterval (-16834886354 / 1000000000000) (-16834885219 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate230_chunkChecks4_2 :
    compactCertificate230.chunkChecks (4 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 4) <| besselDerivativeNearFromState (87964077261727 / 800000000000) 4 (IntervalRat.scale (215 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-53708048654 / 1000000000000) (-53708048653 / 1000000000000), orderedInterval (-53656257239 / 1000000000000) (-53656257238 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 4) <| besselDerivativeNearFromState (74568122470247 / 800000000000) 4 (IntervalRat.scale (215 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-20731849100 / 1000000000000) (-20731848818 / 1000000000000), orderedInterval (80112560194 / 1000000000000) (80112560477 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 4) <| besselDerivativeNearFromState (46661268732941 / 800000000000) 4 (IntervalRat.scale (215 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (57289624526 / 1000000000000) (57289638057 / 1000000000000), orderedInterval (-87856990765 / 1000000000000) (-87856977234 / 1000000000000)))) (orderedInterval (10328752973 / 1000000000000) (10328753046 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 4) <| besselDerivativeNearFromState (25094585512947 / 800000000000) 4 (IntervalRat.scale (215 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (95390982148 / 1000000000000) (95390982149 / 1000000000000), orderedInterval (104290440415 / 1000000000000) (104290440416 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 4) <| besselDerivativeNearFromState (68136681259841 / 800000000000) 4 (IntervalRat.scale (215 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-78256639128 / 1000000000000) (-78256639127 / 1000000000000), orderedInterval (-36288891029 / 1000000000000) (-36288891028 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 4) <| besselDerivativeNearFromState (93034813076257 / 800000000000) 4 (IntervalRat.scale (215 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-55040743071 / 1000000000000) (-55040743070 / 1000000000000), orderedInterval (-49207884229 / 1000000000000) (-49207884228 / 1000000000000)))) (orderedInterval (6558048986 / 1000000000000) (6558049000 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 4) <| besselDerivativeNearFromState (39338731267059 / 800000000000) 4 (IntervalRat.scale (215 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-34623961687 / 1000000000000) (-34623960944 / 1000000000000), orderedInterval (108740898441 / 1000000000000) (108740899185 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 4) <| besselDerivativeNearFromState (159909758579539 / 800000000000) 4 (IntervalRat.scale (215 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-21453701448 / 1000000000000) (-21453700646 / 1000000000000), orderedInterval (52251757274 / 1000000000000) (52251758076 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 4) <| besselDerivativeNearFromState (106812307863101 / 800000000000) 4 (IntervalRat.scale (215 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (48984623724 / 1000000000000) (48984688780 / 1000000000000), orderedInterval (-48852156688 / 1000000000000) (-48852091632 / 1000000000000)))) (orderedInterval (-1181984497 / 1000000000000) (-1181954079 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate230_chunkChecks4 :
    compactCertificate230.chunkChecks (4 : Fin 5) 0 9 = true :=
  compactCertificate230.chunkChecks_nine_of_three (4 : Fin 5) compactCertificate230_chunkChecks4_0
    compactCertificate230_chunkChecks4_1 compactCertificate230_chunkChecks4_2

theorem compactCertificate230_chunks :
    ∀ r : Fin 5, ∀ b, compactCertificate230.chunkCheck r b = true :=
  compactCertificate230.chunkChecks_all (by
    intro r
    fin_cases r
    · exact compactCertificate230_chunkChecks0
    · exact compactCertificate230_chunkChecks1
    · exact compactCertificate230_chunkChecks2
    · exact compactCertificate230_chunkChecks3
    · exact compactCertificate230_chunkChecks4)

theorem compactCertificate230_coefficient0 :
    compactCertificate230.coefficientCheck (0 : Fin 5) = true := by
  norm_num [CompactCertificate.coefficientCheck, intervalFinSumHull,
    compactCertificate230, rationalIntervalSubset, orderedInterval, Fin.sum_univ_succ]

theorem compactCertificate230_coefficient1 :
    compactCertificate230.coefficientCheck (1 : Fin 5) = true := by
  norm_num [CompactCertificate.coefficientCheck, intervalFinSumHull,
    compactCertificate230, rationalIntervalSubset, orderedInterval, Fin.sum_univ_succ]

theorem compactCertificate230_coefficient2 :
    compactCertificate230.coefficientCheck (2 : Fin 5) = true := by
  norm_num [CompactCertificate.coefficientCheck, intervalFinSumHull,
    compactCertificate230, rationalIntervalSubset, orderedInterval, Fin.sum_univ_succ]

theorem compactCertificate230_coefficient3 :
    compactCertificate230.coefficientCheck (3 : Fin 5) = true := by
  norm_num [CompactCertificate.coefficientCheck, intervalFinSumHull,
    compactCertificate230, rationalIntervalSubset, orderedInterval, Fin.sum_univ_succ]

theorem compactCertificate230_coefficient4 :
    compactCertificate230.coefficientCheck (4 : Fin 5) = true := by
  norm_num [CompactCertificate.coefficientCheck, intervalFinSumHull,
    compactCertificate230, rationalIntervalSubset, orderedInterval, Fin.sum_univ_succ]

theorem compactCertificate230_coefficients : ∀ r : Fin 5,
    compactCertificate230.coefficientCheck r = true := by
  intro r
  fin_cases r
  · exact compactCertificate230_coefficient0
  · exact compactCertificate230_coefficient1
  · exact compactCertificate230_coefficient2
  · exact compactCertificate230_coefficient3
  · exact compactCertificate230_coefficient4

theorem compactCertificate230_lower : (1 : ℚ) ≤ compactCertificate230.output.lo := by
  norm_num [CompactCertificate.output, CompactCertificate.interval,
    CompactCertificate.coefficientTargetNat, compactCertificate230, dualConstant,
    intervalTaylorSum, intervalPow, intervalSub, intervalMaxAbs, widenInterval,
    rationalErrorInterval, orderedInterval, IntervalRat.add, IntervalRat.mul, IntervalRat.scale,
    IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4]

theorem compactCertificate230_proves {t : ℝ} (ht : t ∈ compactCertificate230.interval) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t :=
  compactCertificate230.proves compactCertificate230_states compactCertificate230_chunks
    compactCertificate230_coefficients compactCertificate230_lower ht

end Erdos232
