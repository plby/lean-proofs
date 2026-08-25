/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, OpenAI Codex
-/
import ErdosProblems.Erdos232.CompactBase

open LeanCert.Core
namespace Erdos232

def compactCertificate237 : CompactCertificate where
  left := 114
  right := 115
  center := 229 / 2
  grid := fun i =>
    match i.val with
    | 0 => 36
    | 1 => 27
    | 2 => 43
    | 3 => 8
    | 4 => 21
    | 5 => 57
    | 6 => 42
    | 7 => 72
    | 8 => 53
    | 9 => 82
    | 10 => 47
    | 11 => 84
    | 12 => 78
    | 13 => 56
    | 14 => 63
    | 15 => 53
    | 16 => 47
    | 17 => 67
    | 18 => 37
    | 19 => 32
    | 20 => 20
    | 21 => 11
    | 22 => 29
    | 23 => 39
    | 24 => 17
    | 25 => 68
    | _ => 45
  point := fun i =>
    match i.val with
    | 0 => 229 / 2
    | 1 => 337360727069329 / 4000000000000
    | 2 => 109095527620657 / 800000000000
    | 3 => 98441018769203 / 4000000000000
    | 4 => 264426423288791 / 4000000000000
    | 5 => 717969177493947 / 4000000000000
    | 6 => 528852846577811 / 4000000000000
    | 7 => 906198366619103 / 4000000000000
    | 8 => 667501615352477 / 4000000000000
    | 9 => 1024119133694771 / 4000000000000
    | 10 => 591275457520859 / 4000000000000
    | 11 => 1049228675263831 / 4000000000000
    | 12 => 980325530795539 / 4000000000000
    | 13 => 699606556096387 / 4000000000000
    | 14 => 793279269866373 / 4000000000000
    | 15 => 661353551693237 / 4000000000000
    | 16 => 584325919761977 / 4000000000000
    | 17 => 169360426743723 / 800000000000
    | 18 => 468459853324081 / 4000000000000
    | 19 => 397118605713641 / 4000000000000
    | 20 => 248498384647523 / 4000000000000
    | 21 => 133643257731741 / 4000000000000
    | 22 => 362867442058223 / 4000000000000
    | 23 => 495464469638671 / 4000000000000
    | 24 => 209501615352477 / 4000000000000
    | 25 => 851612435225917 / 4000000000000
    | _ => 568837639550003 / 4000000000000
  state := fun i =>
    match i.val with
    | 0 => (orderedInterval (60852144261 / 1000000000000) (60852188251 / 1000000000000), orderedInterval (-43358600612 / 1000000000000) (-43358556623 / 1000000000000))
    | 1 => (orderedInterval (-25765723173 / 1000000000000) (-25765723172 / 1000000000000), orderedInterval (-82819992357 / 1000000000000) (-82819992356 / 1000000000000))
    | 2 => (orderedInterval (-60136568546 / 1000000000000) (-60136552746 / 1000000000000), orderedInterval (32653860312 / 1000000000000) (32653876112 / 1000000000000))
    | 3 => (orderedInterval (41007143304 / 1000000000000) (41007143305 / 1000000000000), orderedInterval (154702146332 / 1000000000000) (154702146333 / 1000000000000))
    | 4 => (orderedInterval (-77875571304 / 1000000000000) (-77875571303 / 1000000000000), orderedInterval (-59123018930 / 1000000000000) (-59123018929 / 1000000000000))
    | 5 => (orderedInterval (-55640388203 / 1000000000000) (-55640388202 / 1000000000000), orderedInterval (-21079824434 / 1000000000000) (-21079824433 / 1000000000000))
    | 6 => (orderedInterval (60217748113 / 1000000000000) (60217748114 / 1000000000000), orderedInterval (34252773970 / 1000000000000) (34252773971 / 1000000000000))
    | 7 => (orderedInterval (48161512288 / 1000000000000) (48161512289 / 1000000000000), orderedInterval (22041671756 / 1000000000000) (22041671757 / 1000000000000))
    | 8 => (orderedInterval (-56518385440 / 1000000000000) (-56518385439 / 1000000000000), orderedInterval (-24742528510 / 1000000000000) (-24742528509 / 1000000000000))
    | 9 => (orderedInterval (-35628272262 / 1000000000000) (-35628231954 / 1000000000000), orderedInterval (34957007759 / 1000000000000) (34957048066 / 1000000000000))
    | 10 => (orderedInterval (-53326014272 / 1000000000000) (-53326014271 / 1000000000000), orderedInterval (-38069910105 / 1000000000000) (-38069910104 / 1000000000000))
    | 11 => (orderedInterval (-35398289777 / 1000000000000) (-35398248514 / 1000000000000), orderedInterval (34330602443 / 1000000000000) (34330643705 / 1000000000000))
    | 12 => (orderedInterval (37334900551 / 1000000000000) (37334900552 / 1000000000000), orderedInterval (34618067840 / 1000000000000) (34618067841 / 1000000000000))
    | 13 => (orderedInterval (-14508793177 / 1000000000000) (-14508793036 / 1000000000000), orderedInterval (58602395154 / 1000000000000) (58602395295 / 1000000000000))
    | 14 => (orderedInterval (-52476945088 / 1000000000000) (-52476945087 / 1000000000000), orderedInterval (-21227221376 / 1000000000000) (-21227221375 / 1000000000000))
    | 15 => (orderedInterval (23095700686 / 1000000000000) (23095701578 / 1000000000000), orderedInterval (-57663301638 / 1000000000000) (-57663300747 / 1000000000000))
    | 16 => (orderedInterval (46839496609 / 1000000000000) (46839558321 / 1000000000000), orderedInterval (-46679544028 / 1000000000000) (-46679482316 / 1000000000000))
    | 17 => (orderedInterval (-49894839933 / 1000000000000) (-49894828006 / 1000000000000), orderedInterval (22870228069 / 1000000000000) (22870239996 / 1000000000000))
    | 18 => (orderedInterval (-73432352476 / 1000000000000) (-73432352341 / 1000000000000), orderedInterval (6908519334 / 1000000000000) (6908519469 / 1000000000000))
    | 19 => (orderedInterval (-36063845208 / 1000000000000) (-36063841758 / 1000000000000), orderedInterval (71678731510 / 1000000000000) (71678734960 / 1000000000000))
    | 20 => (orderedInterval (7698999402 / 1000000000000) (7698999405 / 1000000000000), orderedInterval (100876242235 / 1000000000000) (100876242238 / 1000000000000))
    | 21 => (orderedInterval (49275520958 / 1000000000000) (49275522517 / 1000000000000), orderedInterval (-129686133478 / 1000000000000) (-129686131919 / 1000000000000))
    | 22 => (orderedInterval (-32212027453 / 1000000000000) (-32212027452 / 1000000000000), orderedInterval (-77153679488 / 1000000000000) (-77153679487 / 1000000000000))
    | 23 => (orderedInterval (-60831561334 / 1000000000000) (-60831534354 / 1000000000000), orderedInterval (38180794811 / 1000000000000) (38180821792 / 1000000000000))
    | 24 => (orderedInterval (27132284880 / 1000000000000) (27132285222 / 1000000000000), orderedInterval (-107119947317 / 1000000000000) (-107119946976 / 1000000000000))
    | 25 => (orderedInterval (3258208184 / 1000000000000) (3258208185 / 1000000000000), orderedInterval (54577856235 / 1000000000000) (54577856237 / 1000000000000))
    | _ => (orderedInterval (-66818879594 / 1000000000000) (-66818879500 / 1000000000000), orderedInterval (3676711987 / 1000000000000) (3676712081 / 1000000000000))
  chunkTarget := fun r b =>
    match r.val with
    | 0 =>
      match b.val with
      | 0 => orderedInterval (20350690777 / 1000000000000) (20350709149 / 1000000000000)
      | 1 => orderedInterval (667183705 / 1000000000000) (667183720 / 1000000000000)
      | 2 => orderedInterval (-2851431602 / 1000000000000) (-2851431595 / 1000000000000)
      | 3 => orderedInterval (-2652387676 / 1000000000000) (-2652374602 / 1000000000000)
      | 4 => orderedInterval (-1780439674 / 1000000000000) (-1780439646 / 1000000000000)
      | 5 => orderedInterval (-3691275738 / 1000000000000) (-3691271879 / 1000000000000)
      | 6 => orderedInterval (14033132992 / 1000000000000) (14033133238 / 1000000000000)
      | 7 => orderedInterval (4482971579 / 1000000000000) (4482973690 / 1000000000000)
      | _ => orderedInterval (12435332659 / 1000000000000) (12435332711 / 1000000000000)
    | 1 =>
      match b.val with
      | 0 => orderedInterval (-15472126221 / 1000000000000) (-15472107671 / 1000000000000)
      | 1 => orderedInterval (742096785 / 1000000000000) (742096802 / 1000000000000)
      | 2 => orderedInterval (-2216666681 / 1000000000000) (-2216666669 / 1000000000000)
      | 3 => orderedInterval (-6350443866 / 1000000000000) (-6350414318 / 1000000000000)
      | 4 => orderedInterval (7313308882 / 1000000000000) (7313308926 / 1000000000000)
      | 5 => orderedInterval (3529251191 / 1000000000000) (3529256293 / 1000000000000)
      | 6 => orderedInterval (-2865728449 / 1000000000000) (-2865728230 / 1000000000000)
      | 7 => orderedInterval (-1079935472 / 1000000000000) (-1079933213 / 1000000000000)
      | _ => orderedInterval (-9413070747 / 1000000000000) (-9413070679 / 1000000000000)
    | 2 =>
      match b.val with
      | 0 => orderedInterval (-18848640466 / 1000000000000) (-18848621542 / 1000000000000)
      | 1 => orderedInterval (-8758379740 / 1000000000000) (-8758379718 / 1000000000000)
      | 2 => orderedInterval (8736231043 / 1000000000000) (8736231064 / 1000000000000)
      | 3 => orderedInterval (1396169385 / 1000000000000) (1396236440 / 1000000000000)
      | 4 => orderedInterval (5428746372 / 1000000000000) (5428746441 / 1000000000000)
      | 5 => orderedInterval (8143237309 / 1000000000000) (8143244192 / 1000000000000)
      | 6 => orderedInterval (-13867065399 / 1000000000000) (-13867065202 / 1000000000000)
      | 7 => orderedInterval (-5827798391 / 1000000000000) (-5827795936 / 1000000000000)
      | _ => orderedInterval (-18374248672 / 1000000000000) (-18374248577 / 1000000000000)
    | 3 =>
      match b.val with
      | 0 => orderedInterval (14420488006 / 1000000000000) (14420507182 / 1000000000000)
      | 1 => orderedInterval (-5264249257 / 1000000000000) (-5264249224 / 1000000000000)
      | 2 => orderedInterval (7040794102 / 1000000000000) (7040794140 / 1000000000000)
      | 3 => orderedInterval (16826375977 / 1000000000000) (16826527594 / 1000000000000)
      | 4 => orderedInterval (-14227879361 / 1000000000000) (-14227879250 / 1000000000000)
      | 5 => orderedInterval (-7314452037 / 1000000000000) (-7314442646 / 1000000000000)
      | 6 => orderedInterval (3423053012 / 1000000000000) (3423053189 / 1000000000000)
      | 7 => orderedInterval (2825346798 / 1000000000000) (2825349451 / 1000000000000)
      | _ => orderedInterval (30104657496 / 1000000000000) (30104657633 / 1000000000000)
    | _ =>
      match b.val with
      | 0 => orderedInterval (16695263475 / 1000000000000) (16695283119 / 1000000000000)
      | 1 => orderedInterval (23661191880 / 1000000000000) (23661191931 / 1000000000000)
      | 2 => orderedInterval (-29051919972 / 1000000000000) (-29051919904 / 1000000000000)
      | 3 => orderedInterval (8397978603 / 1000000000000) (8398322821 / 1000000000000)
      | 4 => orderedInterval (-18978435158 / 1000000000000) (-18978434975 / 1000000000000)
      | 5 => orderedInterval (-20742792726 / 1000000000000) (-20742779537 / 1000000000000)
      | 6 => orderedInterval (13965791134 / 1000000000000) (13965791296 / 1000000000000)
      | 7 => orderedInterval (6616637514 / 1000000000000) (6616640406 / 1000000000000)
      | _ => orderedInterval (26141653788 / 1000000000000) (26141653996 / 1000000000000)
  coefficientTarget := fun i =>
    match i.val with
    | 0 => orderedInterval (40993777022 / 1000000000000) (40993814786 / 1000000000000)
    | 1 => orderedInterval (-25813314578 / 1000000000000) (-25813258759 / 1000000000000)
    | 2 => orderedInterval (-41971748559 / 1000000000000) (-41971652838 / 1000000000000)
    | 3 => orderedInterval (47834134736 / 1000000000000) (47834318069 / 1000000000000)
    | _ => orderedInterval (26705368538 / 1000000000000) (26705749153 / 1000000000000)

theorem compactCertificate237_stateChecks0 :
    compactCertificate237.stateChecks 0 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 36 12 (229 / 2)) (orderedInterval (60852144261 / 1000000000000) (60852188251 / 1000000000000), orderedInterval (-43358600612 / 1000000000000) (-43358556623 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 27 12 (337360727069329 / 4000000000000)) (orderedInterval (-25765723173 / 1000000000000) (-25765723172 / 1000000000000), orderedInterval (-82819992357 / 1000000000000) (-82819992356 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 43 12 (109095527620657 / 800000000000)) (orderedInterval (-60136568546 / 1000000000000) (-60136552746 / 1000000000000), orderedInterval (32653860312 / 1000000000000) (32653876112 / 1000000000000))) = true
  norm_num [besselStateAtRationalPoint, besselIntervalStepZero,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, besselZeroTransition,
    besselInitial, besselGridStateAt, besselGridStateBlock00, besselGridStateBlock01,
    besselGridStateBlock02, besselGridStateBlock03, besselGridStateBlock04,
    besselGridStateBlock05, besselGridStateBlock06, besselGridStateBlock07,
    besselGridStateBlock08, besselGridStateBlock09, besselGridStateBlock10,
    besselGridStateBlock11, besselGridStateBlock12, besselGridStateBlock13,
    besselGridStateBlock14, besselGridState008, besselGridState011, besselGridState017, besselGridState020, besselGridState021, besselGridState027, besselGridState029, besselGridState032, besselGridState036, besselGridState037, besselGridState039, besselGridState042, besselGridState043, besselGridState045, besselGridState047, besselGridState053, besselGridState056, besselGridState057, besselGridState063, besselGridState067, besselGridState068, besselGridState072, besselGridState078, besselGridState082, besselGridState084, besselStateSubset, linearInterval, widenInterval,
    rationalErrorInterval, rationalIntervalSubset, orderedInterval, Finset.sum_range_succ,
    IntervalRat.add, IntervalRat.mul, IntervalRat.scale, IntervalRat.singleton]

theorem compactCertificate237_stateChecks1 :
    compactCertificate237.stateChecks 3 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 8 12 (98441018769203 / 4000000000000)) (orderedInterval (41007143304 / 1000000000000) (41007143305 / 1000000000000), orderedInterval (154702146332 / 1000000000000) (154702146333 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 21 12 (264426423288791 / 4000000000000)) (orderedInterval (-77875571304 / 1000000000000) (-77875571303 / 1000000000000), orderedInterval (-59123018930 / 1000000000000) (-59123018929 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 57 12 (717969177493947 / 4000000000000)) (orderedInterval (-55640388203 / 1000000000000) (-55640388202 / 1000000000000), orderedInterval (-21079824434 / 1000000000000) (-21079824433 / 1000000000000))) = true
  norm_num [besselStateAtRationalPoint, besselIntervalStepZero,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, besselZeroTransition,
    besselInitial, besselGridStateAt, besselGridStateBlock00, besselGridStateBlock01,
    besselGridStateBlock02, besselGridStateBlock03, besselGridStateBlock04,
    besselGridStateBlock05, besselGridStateBlock06, besselGridStateBlock07,
    besselGridStateBlock08, besselGridStateBlock09, besselGridStateBlock10,
    besselGridStateBlock11, besselGridStateBlock12, besselGridStateBlock13,
    besselGridStateBlock14, besselGridState008, besselGridState011, besselGridState017, besselGridState020, besselGridState021, besselGridState027, besselGridState029, besselGridState032, besselGridState036, besselGridState037, besselGridState039, besselGridState042, besselGridState043, besselGridState045, besselGridState047, besselGridState053, besselGridState056, besselGridState057, besselGridState063, besselGridState067, besselGridState068, besselGridState072, besselGridState078, besselGridState082, besselGridState084, besselStateSubset, linearInterval, widenInterval,
    rationalErrorInterval, rationalIntervalSubset, orderedInterval, Finset.sum_range_succ,
    IntervalRat.add, IntervalRat.mul, IntervalRat.scale, IntervalRat.singleton]

theorem compactCertificate237_stateChecks2 :
    compactCertificate237.stateChecks 6 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 42 12 (528852846577811 / 4000000000000)) (orderedInterval (60217748113 / 1000000000000) (60217748114 / 1000000000000), orderedInterval (34252773970 / 1000000000000) (34252773971 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 72 12 (906198366619103 / 4000000000000)) (orderedInterval (48161512288 / 1000000000000) (48161512289 / 1000000000000), orderedInterval (22041671756 / 1000000000000) (22041671757 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 53 12 (667501615352477 / 4000000000000)) (orderedInterval (-56518385440 / 1000000000000) (-56518385439 / 1000000000000), orderedInterval (-24742528510 / 1000000000000) (-24742528509 / 1000000000000))) = true
  norm_num [besselStateAtRationalPoint, besselIntervalStepZero,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, besselZeroTransition,
    besselInitial, besselGridStateAt, besselGridStateBlock00, besselGridStateBlock01,
    besselGridStateBlock02, besselGridStateBlock03, besselGridStateBlock04,
    besselGridStateBlock05, besselGridStateBlock06, besselGridStateBlock07,
    besselGridStateBlock08, besselGridStateBlock09, besselGridStateBlock10,
    besselGridStateBlock11, besselGridStateBlock12, besselGridStateBlock13,
    besselGridStateBlock14, besselGridState008, besselGridState011, besselGridState017, besselGridState020, besselGridState021, besselGridState027, besselGridState029, besselGridState032, besselGridState036, besselGridState037, besselGridState039, besselGridState042, besselGridState043, besselGridState045, besselGridState047, besselGridState053, besselGridState056, besselGridState057, besselGridState063, besselGridState067, besselGridState068, besselGridState072, besselGridState078, besselGridState082, besselGridState084, besselStateSubset, linearInterval, widenInterval,
    rationalErrorInterval, rationalIntervalSubset, orderedInterval, Finset.sum_range_succ,
    IntervalRat.add, IntervalRat.mul, IntervalRat.scale, IntervalRat.singleton]

theorem compactCertificate237_stateChecks3 :
    compactCertificate237.stateChecks 9 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 82 12 (1024119133694771 / 4000000000000)) (orderedInterval (-35628272262 / 1000000000000) (-35628231954 / 1000000000000), orderedInterval (34957007759 / 1000000000000) (34957048066 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 47 12 (591275457520859 / 4000000000000)) (orderedInterval (-53326014272 / 1000000000000) (-53326014271 / 1000000000000), orderedInterval (-38069910105 / 1000000000000) (-38069910104 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 84 12 (1049228675263831 / 4000000000000)) (orderedInterval (-35398289777 / 1000000000000) (-35398248514 / 1000000000000), orderedInterval (34330602443 / 1000000000000) (34330643705 / 1000000000000))) = true
  norm_num [besselStateAtRationalPoint, besselIntervalStepZero,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, besselZeroTransition,
    besselInitial, besselGridStateAt, besselGridStateBlock00, besselGridStateBlock01,
    besselGridStateBlock02, besselGridStateBlock03, besselGridStateBlock04,
    besselGridStateBlock05, besselGridStateBlock06, besselGridStateBlock07,
    besselGridStateBlock08, besselGridStateBlock09, besselGridStateBlock10,
    besselGridStateBlock11, besselGridStateBlock12, besselGridStateBlock13,
    besselGridStateBlock14, besselGridState008, besselGridState011, besselGridState017, besselGridState020, besselGridState021, besselGridState027, besselGridState029, besselGridState032, besselGridState036, besselGridState037, besselGridState039, besselGridState042, besselGridState043, besselGridState045, besselGridState047, besselGridState053, besselGridState056, besselGridState057, besselGridState063, besselGridState067, besselGridState068, besselGridState072, besselGridState078, besselGridState082, besselGridState084, besselStateSubset, linearInterval, widenInterval,
    rationalErrorInterval, rationalIntervalSubset, orderedInterval, Finset.sum_range_succ,
    IntervalRat.add, IntervalRat.mul, IntervalRat.scale, IntervalRat.singleton]

theorem compactCertificate237_stateChecks4 :
    compactCertificate237.stateChecks 12 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 78 12 (980325530795539 / 4000000000000)) (orderedInterval (37334900551 / 1000000000000) (37334900552 / 1000000000000), orderedInterval (34618067840 / 1000000000000) (34618067841 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 56 12 (699606556096387 / 4000000000000)) (orderedInterval (-14508793177 / 1000000000000) (-14508793036 / 1000000000000), orderedInterval (58602395154 / 1000000000000) (58602395295 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 63 12 (793279269866373 / 4000000000000)) (orderedInterval (-52476945088 / 1000000000000) (-52476945087 / 1000000000000), orderedInterval (-21227221376 / 1000000000000) (-21227221375 / 1000000000000))) = true
  norm_num [besselStateAtRationalPoint, besselIntervalStepZero,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, besselZeroTransition,
    besselInitial, besselGridStateAt, besselGridStateBlock00, besselGridStateBlock01,
    besselGridStateBlock02, besselGridStateBlock03, besselGridStateBlock04,
    besselGridStateBlock05, besselGridStateBlock06, besselGridStateBlock07,
    besselGridStateBlock08, besselGridStateBlock09, besselGridStateBlock10,
    besselGridStateBlock11, besselGridStateBlock12, besselGridStateBlock13,
    besselGridStateBlock14, besselGridState008, besselGridState011, besselGridState017, besselGridState020, besselGridState021, besselGridState027, besselGridState029, besselGridState032, besselGridState036, besselGridState037, besselGridState039, besselGridState042, besselGridState043, besselGridState045, besselGridState047, besselGridState053, besselGridState056, besselGridState057, besselGridState063, besselGridState067, besselGridState068, besselGridState072, besselGridState078, besselGridState082, besselGridState084, besselStateSubset, linearInterval, widenInterval,
    rationalErrorInterval, rationalIntervalSubset, orderedInterval, Finset.sum_range_succ,
    IntervalRat.add, IntervalRat.mul, IntervalRat.scale, IntervalRat.singleton]

theorem compactCertificate237_stateChecks5 :
    compactCertificate237.stateChecks 15 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 53 12 (661353551693237 / 4000000000000)) (orderedInterval (23095700686 / 1000000000000) (23095701578 / 1000000000000), orderedInterval (-57663301638 / 1000000000000) (-57663300747 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 47 12 (584325919761977 / 4000000000000)) (orderedInterval (46839496609 / 1000000000000) (46839558321 / 1000000000000), orderedInterval (-46679544028 / 1000000000000) (-46679482316 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 67 12 (169360426743723 / 800000000000)) (orderedInterval (-49894839933 / 1000000000000) (-49894828006 / 1000000000000), orderedInterval (22870228069 / 1000000000000) (22870239996 / 1000000000000))) = true
  norm_num [besselStateAtRationalPoint, besselIntervalStepZero,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, besselZeroTransition,
    besselInitial, besselGridStateAt, besselGridStateBlock00, besselGridStateBlock01,
    besselGridStateBlock02, besselGridStateBlock03, besselGridStateBlock04,
    besselGridStateBlock05, besselGridStateBlock06, besselGridStateBlock07,
    besselGridStateBlock08, besselGridStateBlock09, besselGridStateBlock10,
    besselGridStateBlock11, besselGridStateBlock12, besselGridStateBlock13,
    besselGridStateBlock14, besselGridState008, besselGridState011, besselGridState017, besselGridState020, besselGridState021, besselGridState027, besselGridState029, besselGridState032, besselGridState036, besselGridState037, besselGridState039, besselGridState042, besselGridState043, besselGridState045, besselGridState047, besselGridState053, besselGridState056, besselGridState057, besselGridState063, besselGridState067, besselGridState068, besselGridState072, besselGridState078, besselGridState082, besselGridState084, besselStateSubset, linearInterval, widenInterval,
    rationalErrorInterval, rationalIntervalSubset, orderedInterval, Finset.sum_range_succ,
    IntervalRat.add, IntervalRat.mul, IntervalRat.scale, IntervalRat.singleton]

theorem compactCertificate237_stateChecks6 :
    compactCertificate237.stateChecks 18 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 37 12 (468459853324081 / 4000000000000)) (orderedInterval (-73432352476 / 1000000000000) (-73432352341 / 1000000000000), orderedInterval (6908519334 / 1000000000000) (6908519469 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 32 12 (397118605713641 / 4000000000000)) (orderedInterval (-36063845208 / 1000000000000) (-36063841758 / 1000000000000), orderedInterval (71678731510 / 1000000000000) (71678734960 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 20 12 (248498384647523 / 4000000000000)) (orderedInterval (7698999402 / 1000000000000) (7698999405 / 1000000000000), orderedInterval (100876242235 / 1000000000000) (100876242238 / 1000000000000))) = true
  norm_num [besselStateAtRationalPoint, besselIntervalStepZero,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, besselZeroTransition,
    besselInitial, besselGridStateAt, besselGridStateBlock00, besselGridStateBlock01,
    besselGridStateBlock02, besselGridStateBlock03, besselGridStateBlock04,
    besselGridStateBlock05, besselGridStateBlock06, besselGridStateBlock07,
    besselGridStateBlock08, besselGridStateBlock09, besselGridStateBlock10,
    besselGridStateBlock11, besselGridStateBlock12, besselGridStateBlock13,
    besselGridStateBlock14, besselGridState008, besselGridState011, besselGridState017, besselGridState020, besselGridState021, besselGridState027, besselGridState029, besselGridState032, besselGridState036, besselGridState037, besselGridState039, besselGridState042, besselGridState043, besselGridState045, besselGridState047, besselGridState053, besselGridState056, besselGridState057, besselGridState063, besselGridState067, besselGridState068, besselGridState072, besselGridState078, besselGridState082, besselGridState084, besselStateSubset, linearInterval, widenInterval,
    rationalErrorInterval, rationalIntervalSubset, orderedInterval, Finset.sum_range_succ,
    IntervalRat.add, IntervalRat.mul, IntervalRat.scale, IntervalRat.singleton]

theorem compactCertificate237_stateChecks7 :
    compactCertificate237.stateChecks 21 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 11 12 (133643257731741 / 4000000000000)) (orderedInterval (49275520958 / 1000000000000) (49275522517 / 1000000000000), orderedInterval (-129686133478 / 1000000000000) (-129686131919 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 29 12 (362867442058223 / 4000000000000)) (orderedInterval (-32212027453 / 1000000000000) (-32212027452 / 1000000000000), orderedInterval (-77153679488 / 1000000000000) (-77153679487 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 39 12 (495464469638671 / 4000000000000)) (orderedInterval (-60831561334 / 1000000000000) (-60831534354 / 1000000000000), orderedInterval (38180794811 / 1000000000000) (38180821792 / 1000000000000))) = true
  norm_num [besselStateAtRationalPoint, besselIntervalStepZero,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, besselZeroTransition,
    besselInitial, besselGridStateAt, besselGridStateBlock00, besselGridStateBlock01,
    besselGridStateBlock02, besselGridStateBlock03, besselGridStateBlock04,
    besselGridStateBlock05, besselGridStateBlock06, besselGridStateBlock07,
    besselGridStateBlock08, besselGridStateBlock09, besselGridStateBlock10,
    besselGridStateBlock11, besselGridStateBlock12, besselGridStateBlock13,
    besselGridStateBlock14, besselGridState008, besselGridState011, besselGridState017, besselGridState020, besselGridState021, besselGridState027, besselGridState029, besselGridState032, besselGridState036, besselGridState037, besselGridState039, besselGridState042, besselGridState043, besselGridState045, besselGridState047, besselGridState053, besselGridState056, besselGridState057, besselGridState063, besselGridState067, besselGridState068, besselGridState072, besselGridState078, besselGridState082, besselGridState084, besselStateSubset, linearInterval, widenInterval,
    rationalErrorInterval, rationalIntervalSubset, orderedInterval, Finset.sum_range_succ,
    IntervalRat.add, IntervalRat.mul, IntervalRat.scale, IntervalRat.singleton]

theorem compactCertificate237_stateChecks8 :
    compactCertificate237.stateChecks 24 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 17 12 (209501615352477 / 4000000000000)) (orderedInterval (27132284880 / 1000000000000) (27132285222 / 1000000000000), orderedInterval (-107119947317 / 1000000000000) (-107119946976 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 68 12 (851612435225917 / 4000000000000)) (orderedInterval (3258208184 / 1000000000000) (3258208185 / 1000000000000), orderedInterval (54577856235 / 1000000000000) (54577856237 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 45 12 (568837639550003 / 4000000000000)) (orderedInterval (-66818879594 / 1000000000000) (-66818879500 / 1000000000000), orderedInterval (3676711987 / 1000000000000) (3676712081 / 1000000000000))) = true
  norm_num [besselStateAtRationalPoint, besselIntervalStepZero,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, besselZeroTransition,
    besselInitial, besselGridStateAt, besselGridStateBlock00, besselGridStateBlock01,
    besselGridStateBlock02, besselGridStateBlock03, besselGridStateBlock04,
    besselGridStateBlock05, besselGridStateBlock06, besselGridStateBlock07,
    besselGridStateBlock08, besselGridStateBlock09, besselGridStateBlock10,
    besselGridStateBlock11, besselGridStateBlock12, besselGridStateBlock13,
    besselGridStateBlock14, besselGridState008, besselGridState011, besselGridState017, besselGridState020, besselGridState021, besselGridState027, besselGridState029, besselGridState032, besselGridState036, besselGridState037, besselGridState039, besselGridState042, besselGridState043, besselGridState045, besselGridState047, besselGridState053, besselGridState056, besselGridState057, besselGridState063, besselGridState067, besselGridState068, besselGridState072, besselGridState078, besselGridState082, besselGridState084, besselStateSubset, linearInterval, widenInterval,
    rationalErrorInterval, rationalIntervalSubset, orderedInterval, Finset.sum_range_succ,
    IntervalRat.add, IntervalRat.mul, IntervalRat.scale, IntervalRat.singleton]

theorem compactCertificate237_states : ∀ j,
    BesselStateValid (compactCertificate237.point j) (compactCertificate237.state j) :=
  compactCertificate237.statesValid_of_checks3 compactCertificate237_stateChecks0
    compactCertificate237_stateChecks1 compactCertificate237_stateChecks2
    compactCertificate237_stateChecks3 compactCertificate237_stateChecks4
    compactCertificate237_stateChecks5 compactCertificate237_stateChecks6
    compactCertificate237_stateChecks7 compactCertificate237_stateChecks8

theorem compactCertificate237_chunkChecks0_0 :
    compactCertificate237.chunkChecks (0 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 0) <| besselDerivativeNearFromState (229 / 2) 0 (IntervalRat.scale (229 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (60852144261 / 1000000000000) (60852188251 / 1000000000000), orderedInterval (-43358600612 / 1000000000000) (-43358556623 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 0) <| besselDerivativeNearFromState (337360727069329 / 4000000000000) 0 (IntervalRat.scale (229 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-25765723173 / 1000000000000) (-25765723172 / 1000000000000), orderedInterval (-82819992357 / 1000000000000) (-82819992356 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 0) <| besselDerivativeNearFromState (109095527620657 / 800000000000) 0 (IntervalRat.scale (229 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-60136568546 / 1000000000000) (-60136552746 / 1000000000000), orderedInterval (32653860312 / 1000000000000) (32653876112 / 1000000000000)))) (orderedInterval (20350690777 / 1000000000000) (20350709149 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 0) <| besselDerivativeNearFromState (98441018769203 / 4000000000000) 0 (IntervalRat.scale (229 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (41007143304 / 1000000000000) (41007143305 / 1000000000000), orderedInterval (154702146332 / 1000000000000) (154702146333 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 0) <| besselDerivativeNearFromState (264426423288791 / 4000000000000) 0 (IntervalRat.scale (229 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-77875571304 / 1000000000000) (-77875571303 / 1000000000000), orderedInterval (-59123018930 / 1000000000000) (-59123018929 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 0) <| besselDerivativeNearFromState (717969177493947 / 4000000000000) 0 (IntervalRat.scale (229 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-55640388203 / 1000000000000) (-55640388202 / 1000000000000), orderedInterval (-21079824434 / 1000000000000) (-21079824433 / 1000000000000)))) (orderedInterval (667183705 / 1000000000000) (667183720 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 0) <| besselDerivativeNearFromState (528852846577811 / 4000000000000) 0 (IntervalRat.scale (229 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (60217748113 / 1000000000000) (60217748114 / 1000000000000), orderedInterval (34252773970 / 1000000000000) (34252773971 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 0) <| besselDerivativeNearFromState (906198366619103 / 4000000000000) 0 (IntervalRat.scale (229 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (48161512288 / 1000000000000) (48161512289 / 1000000000000), orderedInterval (22041671756 / 1000000000000) (22041671757 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 0) <| besselDerivativeNearFromState (667501615352477 / 4000000000000) 0 (IntervalRat.scale (229 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-56518385440 / 1000000000000) (-56518385439 / 1000000000000), orderedInterval (-24742528510 / 1000000000000) (-24742528509 / 1000000000000)))) (orderedInterval (-2851431602 / 1000000000000) (-2851431595 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate237_chunkChecks0_1 :
    compactCertificate237.chunkChecks (0 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 0) <| besselDerivativeNearFromState (1024119133694771 / 4000000000000) 0 (IntervalRat.scale (229 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-35628272262 / 1000000000000) (-35628231954 / 1000000000000), orderedInterval (34957007759 / 1000000000000) (34957048066 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 0) <| besselDerivativeNearFromState (591275457520859 / 4000000000000) 0 (IntervalRat.scale (229 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-53326014272 / 1000000000000) (-53326014271 / 1000000000000), orderedInterval (-38069910105 / 1000000000000) (-38069910104 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 0) <| besselDerivativeNearFromState (1049228675263831 / 4000000000000) 0 (IntervalRat.scale (229 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-35398289777 / 1000000000000) (-35398248514 / 1000000000000), orderedInterval (34330602443 / 1000000000000) (34330643705 / 1000000000000)))) (orderedInterval (-2652387676 / 1000000000000) (-2652374602 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 0) <| besselDerivativeNearFromState (980325530795539 / 4000000000000) 0 (IntervalRat.scale (229 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (37334900551 / 1000000000000) (37334900552 / 1000000000000), orderedInterval (34618067840 / 1000000000000) (34618067841 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 0) <| besselDerivativeNearFromState (699606556096387 / 4000000000000) 0 (IntervalRat.scale (229 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-14508793177 / 1000000000000) (-14508793036 / 1000000000000), orderedInterval (58602395154 / 1000000000000) (58602395295 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 0) <| besselDerivativeNearFromState (793279269866373 / 4000000000000) 0 (IntervalRat.scale (229 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-52476945088 / 1000000000000) (-52476945087 / 1000000000000), orderedInterval (-21227221376 / 1000000000000) (-21227221375 / 1000000000000)))) (orderedInterval (-1780439674 / 1000000000000) (-1780439646 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 0) <| besselDerivativeNearFromState (661353551693237 / 4000000000000) 0 (IntervalRat.scale (229 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (23095700686 / 1000000000000) (23095701578 / 1000000000000), orderedInterval (-57663301638 / 1000000000000) (-57663300747 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 0) <| besselDerivativeNearFromState (584325919761977 / 4000000000000) 0 (IntervalRat.scale (229 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (46839496609 / 1000000000000) (46839558321 / 1000000000000), orderedInterval (-46679544028 / 1000000000000) (-46679482316 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 0) <| besselDerivativeNearFromState (169360426743723 / 800000000000) 0 (IntervalRat.scale (229 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-49894839933 / 1000000000000) (-49894828006 / 1000000000000), orderedInterval (22870228069 / 1000000000000) (22870239996 / 1000000000000)))) (orderedInterval (-3691275738 / 1000000000000) (-3691271879 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate237_chunkChecks0_2 :
    compactCertificate237.chunkChecks (0 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 0) <| besselDerivativeNearFromState (468459853324081 / 4000000000000) 0 (IntervalRat.scale (229 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-73432352476 / 1000000000000) (-73432352341 / 1000000000000), orderedInterval (6908519334 / 1000000000000) (6908519469 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 0) <| besselDerivativeNearFromState (397118605713641 / 4000000000000) 0 (IntervalRat.scale (229 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-36063845208 / 1000000000000) (-36063841758 / 1000000000000), orderedInterval (71678731510 / 1000000000000) (71678734960 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 0) <| besselDerivativeNearFromState (248498384647523 / 4000000000000) 0 (IntervalRat.scale (229 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (7698999402 / 1000000000000) (7698999405 / 1000000000000), orderedInterval (100876242235 / 1000000000000) (100876242238 / 1000000000000)))) (orderedInterval (14033132992 / 1000000000000) (14033133238 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 0) <| besselDerivativeNearFromState (133643257731741 / 4000000000000) 0 (IntervalRat.scale (229 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (49275520958 / 1000000000000) (49275522517 / 1000000000000), orderedInterval (-129686133478 / 1000000000000) (-129686131919 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 0) <| besselDerivativeNearFromState (362867442058223 / 4000000000000) 0 (IntervalRat.scale (229 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-32212027453 / 1000000000000) (-32212027452 / 1000000000000), orderedInterval (-77153679488 / 1000000000000) (-77153679487 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 0) <| besselDerivativeNearFromState (495464469638671 / 4000000000000) 0 (IntervalRat.scale (229 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-60831561334 / 1000000000000) (-60831534354 / 1000000000000), orderedInterval (38180794811 / 1000000000000) (38180821792 / 1000000000000)))) (orderedInterval (4482971579 / 1000000000000) (4482973690 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 0) <| besselDerivativeNearFromState (209501615352477 / 4000000000000) 0 (IntervalRat.scale (229 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (27132284880 / 1000000000000) (27132285222 / 1000000000000), orderedInterval (-107119947317 / 1000000000000) (-107119946976 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 0) <| besselDerivativeNearFromState (851612435225917 / 4000000000000) 0 (IntervalRat.scale (229 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (3258208184 / 1000000000000) (3258208185 / 1000000000000), orderedInterval (54577856235 / 1000000000000) (54577856237 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 0) <| besselDerivativeNearFromState (568837639550003 / 4000000000000) 0 (IntervalRat.scale (229 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-66818879594 / 1000000000000) (-66818879500 / 1000000000000), orderedInterval (3676711987 / 1000000000000) (3676712081 / 1000000000000)))) (orderedInterval (12435332659 / 1000000000000) (12435332711 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate237_chunkChecks0 :
    compactCertificate237.chunkChecks (0 : Fin 5) 0 9 = true :=
  compactCertificate237.chunkChecks_nine_of_three (0 : Fin 5) compactCertificate237_chunkChecks0_0
    compactCertificate237_chunkChecks0_1 compactCertificate237_chunkChecks0_2

theorem compactCertificate237_chunkChecks1_0 :
    compactCertificate237.chunkChecks (1 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 1) <| besselDerivativeNearFromState (229 / 2) 1 (IntervalRat.scale (229 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (60852144261 / 1000000000000) (60852188251 / 1000000000000), orderedInterval (-43358600612 / 1000000000000) (-43358556623 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 1) <| besselDerivativeNearFromState (337360727069329 / 4000000000000) 1 (IntervalRat.scale (229 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-25765723173 / 1000000000000) (-25765723172 / 1000000000000), orderedInterval (-82819992357 / 1000000000000) (-82819992356 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 1) <| besselDerivativeNearFromState (109095527620657 / 800000000000) 1 (IntervalRat.scale (229 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-60136568546 / 1000000000000) (-60136552746 / 1000000000000), orderedInterval (32653860312 / 1000000000000) (32653876112 / 1000000000000)))) (orderedInterval (-15472126221 / 1000000000000) (-15472107671 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 1) <| besselDerivativeNearFromState (98441018769203 / 4000000000000) 1 (IntervalRat.scale (229 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (41007143304 / 1000000000000) (41007143305 / 1000000000000), orderedInterval (154702146332 / 1000000000000) (154702146333 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 1) <| besselDerivativeNearFromState (264426423288791 / 4000000000000) 1 (IntervalRat.scale (229 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-77875571304 / 1000000000000) (-77875571303 / 1000000000000), orderedInterval (-59123018930 / 1000000000000) (-59123018929 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 1) <| besselDerivativeNearFromState (717969177493947 / 4000000000000) 1 (IntervalRat.scale (229 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-55640388203 / 1000000000000) (-55640388202 / 1000000000000), orderedInterval (-21079824434 / 1000000000000) (-21079824433 / 1000000000000)))) (orderedInterval (742096785 / 1000000000000) (742096802 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 1) <| besselDerivativeNearFromState (528852846577811 / 4000000000000) 1 (IntervalRat.scale (229 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (60217748113 / 1000000000000) (60217748114 / 1000000000000), orderedInterval (34252773970 / 1000000000000) (34252773971 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 1) <| besselDerivativeNearFromState (906198366619103 / 4000000000000) 1 (IntervalRat.scale (229 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (48161512288 / 1000000000000) (48161512289 / 1000000000000), orderedInterval (22041671756 / 1000000000000) (22041671757 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 1) <| besselDerivativeNearFromState (667501615352477 / 4000000000000) 1 (IntervalRat.scale (229 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-56518385440 / 1000000000000) (-56518385439 / 1000000000000), orderedInterval (-24742528510 / 1000000000000) (-24742528509 / 1000000000000)))) (orderedInterval (-2216666681 / 1000000000000) (-2216666669 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate237_chunkChecks1_1 :
    compactCertificate237.chunkChecks (1 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 1) <| besselDerivativeNearFromState (1024119133694771 / 4000000000000) 1 (IntervalRat.scale (229 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-35628272262 / 1000000000000) (-35628231954 / 1000000000000), orderedInterval (34957007759 / 1000000000000) (34957048066 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 1) <| besselDerivativeNearFromState (591275457520859 / 4000000000000) 1 (IntervalRat.scale (229 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-53326014272 / 1000000000000) (-53326014271 / 1000000000000), orderedInterval (-38069910105 / 1000000000000) (-38069910104 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 1) <| besselDerivativeNearFromState (1049228675263831 / 4000000000000) 1 (IntervalRat.scale (229 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-35398289777 / 1000000000000) (-35398248514 / 1000000000000), orderedInterval (34330602443 / 1000000000000) (34330643705 / 1000000000000)))) (orderedInterval (-6350443866 / 1000000000000) (-6350414318 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 1) <| besselDerivativeNearFromState (980325530795539 / 4000000000000) 1 (IntervalRat.scale (229 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (37334900551 / 1000000000000) (37334900552 / 1000000000000), orderedInterval (34618067840 / 1000000000000) (34618067841 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 1) <| besselDerivativeNearFromState (699606556096387 / 4000000000000) 1 (IntervalRat.scale (229 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-14508793177 / 1000000000000) (-14508793036 / 1000000000000), orderedInterval (58602395154 / 1000000000000) (58602395295 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 1) <| besselDerivativeNearFromState (793279269866373 / 4000000000000) 1 (IntervalRat.scale (229 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-52476945088 / 1000000000000) (-52476945087 / 1000000000000), orderedInterval (-21227221376 / 1000000000000) (-21227221375 / 1000000000000)))) (orderedInterval (7313308882 / 1000000000000) (7313308926 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 1) <| besselDerivativeNearFromState (661353551693237 / 4000000000000) 1 (IntervalRat.scale (229 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (23095700686 / 1000000000000) (23095701578 / 1000000000000), orderedInterval (-57663301638 / 1000000000000) (-57663300747 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 1) <| besselDerivativeNearFromState (584325919761977 / 4000000000000) 1 (IntervalRat.scale (229 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (46839496609 / 1000000000000) (46839558321 / 1000000000000), orderedInterval (-46679544028 / 1000000000000) (-46679482316 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 1) <| besselDerivativeNearFromState (169360426743723 / 800000000000) 1 (IntervalRat.scale (229 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-49894839933 / 1000000000000) (-49894828006 / 1000000000000), orderedInterval (22870228069 / 1000000000000) (22870239996 / 1000000000000)))) (orderedInterval (3529251191 / 1000000000000) (3529256293 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate237_chunkChecks1_2 :
    compactCertificate237.chunkChecks (1 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 1) <| besselDerivativeNearFromState (468459853324081 / 4000000000000) 1 (IntervalRat.scale (229 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-73432352476 / 1000000000000) (-73432352341 / 1000000000000), orderedInterval (6908519334 / 1000000000000) (6908519469 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 1) <| besselDerivativeNearFromState (397118605713641 / 4000000000000) 1 (IntervalRat.scale (229 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-36063845208 / 1000000000000) (-36063841758 / 1000000000000), orderedInterval (71678731510 / 1000000000000) (71678734960 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 1) <| besselDerivativeNearFromState (248498384647523 / 4000000000000) 1 (IntervalRat.scale (229 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (7698999402 / 1000000000000) (7698999405 / 1000000000000), orderedInterval (100876242235 / 1000000000000) (100876242238 / 1000000000000)))) (orderedInterval (-2865728449 / 1000000000000) (-2865728230 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 1) <| besselDerivativeNearFromState (133643257731741 / 4000000000000) 1 (IntervalRat.scale (229 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (49275520958 / 1000000000000) (49275522517 / 1000000000000), orderedInterval (-129686133478 / 1000000000000) (-129686131919 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 1) <| besselDerivativeNearFromState (362867442058223 / 4000000000000) 1 (IntervalRat.scale (229 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-32212027453 / 1000000000000) (-32212027452 / 1000000000000), orderedInterval (-77153679488 / 1000000000000) (-77153679487 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 1) <| besselDerivativeNearFromState (495464469638671 / 4000000000000) 1 (IntervalRat.scale (229 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-60831561334 / 1000000000000) (-60831534354 / 1000000000000), orderedInterval (38180794811 / 1000000000000) (38180821792 / 1000000000000)))) (orderedInterval (-1079935472 / 1000000000000) (-1079933213 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 1) <| besselDerivativeNearFromState (209501615352477 / 4000000000000) 1 (IntervalRat.scale (229 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (27132284880 / 1000000000000) (27132285222 / 1000000000000), orderedInterval (-107119947317 / 1000000000000) (-107119946976 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 1) <| besselDerivativeNearFromState (851612435225917 / 4000000000000) 1 (IntervalRat.scale (229 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (3258208184 / 1000000000000) (3258208185 / 1000000000000), orderedInterval (54577856235 / 1000000000000) (54577856237 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 1) <| besselDerivativeNearFromState (568837639550003 / 4000000000000) 1 (IntervalRat.scale (229 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-66818879594 / 1000000000000) (-66818879500 / 1000000000000), orderedInterval (3676711987 / 1000000000000) (3676712081 / 1000000000000)))) (orderedInterval (-9413070747 / 1000000000000) (-9413070679 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate237_chunkChecks1 :
    compactCertificate237.chunkChecks (1 : Fin 5) 0 9 = true :=
  compactCertificate237.chunkChecks_nine_of_three (1 : Fin 5) compactCertificate237_chunkChecks1_0
    compactCertificate237_chunkChecks1_1 compactCertificate237_chunkChecks1_2

theorem compactCertificate237_chunkChecks2_0 :
    compactCertificate237.chunkChecks (2 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 2) <| besselDerivativeNearFromState (229 / 2) 2 (IntervalRat.scale (229 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (60852144261 / 1000000000000) (60852188251 / 1000000000000), orderedInterval (-43358600612 / 1000000000000) (-43358556623 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 2) <| besselDerivativeNearFromState (337360727069329 / 4000000000000) 2 (IntervalRat.scale (229 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-25765723173 / 1000000000000) (-25765723172 / 1000000000000), orderedInterval (-82819992357 / 1000000000000) (-82819992356 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 2) <| besselDerivativeNearFromState (109095527620657 / 800000000000) 2 (IntervalRat.scale (229 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-60136568546 / 1000000000000) (-60136552746 / 1000000000000), orderedInterval (32653860312 / 1000000000000) (32653876112 / 1000000000000)))) (orderedInterval (-18848640466 / 1000000000000) (-18848621542 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 2) <| besselDerivativeNearFromState (98441018769203 / 4000000000000) 2 (IntervalRat.scale (229 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (41007143304 / 1000000000000) (41007143305 / 1000000000000), orderedInterval (154702146332 / 1000000000000) (154702146333 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 2) <| besselDerivativeNearFromState (264426423288791 / 4000000000000) 2 (IntervalRat.scale (229 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-77875571304 / 1000000000000) (-77875571303 / 1000000000000), orderedInterval (-59123018930 / 1000000000000) (-59123018929 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 2) <| besselDerivativeNearFromState (717969177493947 / 4000000000000) 2 (IntervalRat.scale (229 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-55640388203 / 1000000000000) (-55640388202 / 1000000000000), orderedInterval (-21079824434 / 1000000000000) (-21079824433 / 1000000000000)))) (orderedInterval (-8758379740 / 1000000000000) (-8758379718 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 2) <| besselDerivativeNearFromState (528852846577811 / 4000000000000) 2 (IntervalRat.scale (229 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (60217748113 / 1000000000000) (60217748114 / 1000000000000), orderedInterval (34252773970 / 1000000000000) (34252773971 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 2) <| besselDerivativeNearFromState (906198366619103 / 4000000000000) 2 (IntervalRat.scale (229 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (48161512288 / 1000000000000) (48161512289 / 1000000000000), orderedInterval (22041671756 / 1000000000000) (22041671757 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 2) <| besselDerivativeNearFromState (667501615352477 / 4000000000000) 2 (IntervalRat.scale (229 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-56518385440 / 1000000000000) (-56518385439 / 1000000000000), orderedInterval (-24742528510 / 1000000000000) (-24742528509 / 1000000000000)))) (orderedInterval (8736231043 / 1000000000000) (8736231064 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate237_chunkChecks2_1 :
    compactCertificate237.chunkChecks (2 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 2) <| besselDerivativeNearFromState (1024119133694771 / 4000000000000) 2 (IntervalRat.scale (229 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-35628272262 / 1000000000000) (-35628231954 / 1000000000000), orderedInterval (34957007759 / 1000000000000) (34957048066 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 2) <| besselDerivativeNearFromState (591275457520859 / 4000000000000) 2 (IntervalRat.scale (229 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-53326014272 / 1000000000000) (-53326014271 / 1000000000000), orderedInterval (-38069910105 / 1000000000000) (-38069910104 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 2) <| besselDerivativeNearFromState (1049228675263831 / 4000000000000) 2 (IntervalRat.scale (229 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-35398289777 / 1000000000000) (-35398248514 / 1000000000000), orderedInterval (34330602443 / 1000000000000) (34330643705 / 1000000000000)))) (orderedInterval (1396169385 / 1000000000000) (1396236440 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 2) <| besselDerivativeNearFromState (980325530795539 / 4000000000000) 2 (IntervalRat.scale (229 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (37334900551 / 1000000000000) (37334900552 / 1000000000000), orderedInterval (34618067840 / 1000000000000) (34618067841 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 2) <| besselDerivativeNearFromState (699606556096387 / 4000000000000) 2 (IntervalRat.scale (229 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-14508793177 / 1000000000000) (-14508793036 / 1000000000000), orderedInterval (58602395154 / 1000000000000) (58602395295 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 2) <| besselDerivativeNearFromState (793279269866373 / 4000000000000) 2 (IntervalRat.scale (229 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-52476945088 / 1000000000000) (-52476945087 / 1000000000000), orderedInterval (-21227221376 / 1000000000000) (-21227221375 / 1000000000000)))) (orderedInterval (5428746372 / 1000000000000) (5428746441 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 2) <| besselDerivativeNearFromState (661353551693237 / 4000000000000) 2 (IntervalRat.scale (229 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (23095700686 / 1000000000000) (23095701578 / 1000000000000), orderedInterval (-57663301638 / 1000000000000) (-57663300747 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 2) <| besselDerivativeNearFromState (584325919761977 / 4000000000000) 2 (IntervalRat.scale (229 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (46839496609 / 1000000000000) (46839558321 / 1000000000000), orderedInterval (-46679544028 / 1000000000000) (-46679482316 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 2) <| besselDerivativeNearFromState (169360426743723 / 800000000000) 2 (IntervalRat.scale (229 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-49894839933 / 1000000000000) (-49894828006 / 1000000000000), orderedInterval (22870228069 / 1000000000000) (22870239996 / 1000000000000)))) (orderedInterval (8143237309 / 1000000000000) (8143244192 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate237_chunkChecks2_2 :
    compactCertificate237.chunkChecks (2 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 2) <| besselDerivativeNearFromState (468459853324081 / 4000000000000) 2 (IntervalRat.scale (229 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-73432352476 / 1000000000000) (-73432352341 / 1000000000000), orderedInterval (6908519334 / 1000000000000) (6908519469 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 2) <| besselDerivativeNearFromState (397118605713641 / 4000000000000) 2 (IntervalRat.scale (229 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-36063845208 / 1000000000000) (-36063841758 / 1000000000000), orderedInterval (71678731510 / 1000000000000) (71678734960 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 2) <| besselDerivativeNearFromState (248498384647523 / 4000000000000) 2 (IntervalRat.scale (229 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (7698999402 / 1000000000000) (7698999405 / 1000000000000), orderedInterval (100876242235 / 1000000000000) (100876242238 / 1000000000000)))) (orderedInterval (-13867065399 / 1000000000000) (-13867065202 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 2) <| besselDerivativeNearFromState (133643257731741 / 4000000000000) 2 (IntervalRat.scale (229 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (49275520958 / 1000000000000) (49275522517 / 1000000000000), orderedInterval (-129686133478 / 1000000000000) (-129686131919 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 2) <| besselDerivativeNearFromState (362867442058223 / 4000000000000) 2 (IntervalRat.scale (229 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-32212027453 / 1000000000000) (-32212027452 / 1000000000000), orderedInterval (-77153679488 / 1000000000000) (-77153679487 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 2) <| besselDerivativeNearFromState (495464469638671 / 4000000000000) 2 (IntervalRat.scale (229 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-60831561334 / 1000000000000) (-60831534354 / 1000000000000), orderedInterval (38180794811 / 1000000000000) (38180821792 / 1000000000000)))) (orderedInterval (-5827798391 / 1000000000000) (-5827795936 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 2) <| besselDerivativeNearFromState (209501615352477 / 4000000000000) 2 (IntervalRat.scale (229 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (27132284880 / 1000000000000) (27132285222 / 1000000000000), orderedInterval (-107119947317 / 1000000000000) (-107119946976 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 2) <| besselDerivativeNearFromState (851612435225917 / 4000000000000) 2 (IntervalRat.scale (229 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (3258208184 / 1000000000000) (3258208185 / 1000000000000), orderedInterval (54577856235 / 1000000000000) (54577856237 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 2) <| besselDerivativeNearFromState (568837639550003 / 4000000000000) 2 (IntervalRat.scale (229 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-66818879594 / 1000000000000) (-66818879500 / 1000000000000), orderedInterval (3676711987 / 1000000000000) (3676712081 / 1000000000000)))) (orderedInterval (-18374248672 / 1000000000000) (-18374248577 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate237_chunkChecks2 :
    compactCertificate237.chunkChecks (2 : Fin 5) 0 9 = true :=
  compactCertificate237.chunkChecks_nine_of_three (2 : Fin 5) compactCertificate237_chunkChecks2_0
    compactCertificate237_chunkChecks2_1 compactCertificate237_chunkChecks2_2

theorem compactCertificate237_chunkChecks3_0 :
    compactCertificate237.chunkChecks (3 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 3) <| besselDerivativeNearFromState (229 / 2) 3 (IntervalRat.scale (229 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (60852144261 / 1000000000000) (60852188251 / 1000000000000), orderedInterval (-43358600612 / 1000000000000) (-43358556623 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 3) <| besselDerivativeNearFromState (337360727069329 / 4000000000000) 3 (IntervalRat.scale (229 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-25765723173 / 1000000000000) (-25765723172 / 1000000000000), orderedInterval (-82819992357 / 1000000000000) (-82819992356 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 3) <| besselDerivativeNearFromState (109095527620657 / 800000000000) 3 (IntervalRat.scale (229 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-60136568546 / 1000000000000) (-60136552746 / 1000000000000), orderedInterval (32653860312 / 1000000000000) (32653876112 / 1000000000000)))) (orderedInterval (14420488006 / 1000000000000) (14420507182 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 3) <| besselDerivativeNearFromState (98441018769203 / 4000000000000) 3 (IntervalRat.scale (229 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (41007143304 / 1000000000000) (41007143305 / 1000000000000), orderedInterval (154702146332 / 1000000000000) (154702146333 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 3) <| besselDerivativeNearFromState (264426423288791 / 4000000000000) 3 (IntervalRat.scale (229 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-77875571304 / 1000000000000) (-77875571303 / 1000000000000), orderedInterval (-59123018930 / 1000000000000) (-59123018929 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 3) <| besselDerivativeNearFromState (717969177493947 / 4000000000000) 3 (IntervalRat.scale (229 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-55640388203 / 1000000000000) (-55640388202 / 1000000000000), orderedInterval (-21079824434 / 1000000000000) (-21079824433 / 1000000000000)))) (orderedInterval (-5264249257 / 1000000000000) (-5264249224 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 3) <| besselDerivativeNearFromState (528852846577811 / 4000000000000) 3 (IntervalRat.scale (229 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (60217748113 / 1000000000000) (60217748114 / 1000000000000), orderedInterval (34252773970 / 1000000000000) (34252773971 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 3) <| besselDerivativeNearFromState (906198366619103 / 4000000000000) 3 (IntervalRat.scale (229 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (48161512288 / 1000000000000) (48161512289 / 1000000000000), orderedInterval (22041671756 / 1000000000000) (22041671757 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 3) <| besselDerivativeNearFromState (667501615352477 / 4000000000000) 3 (IntervalRat.scale (229 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-56518385440 / 1000000000000) (-56518385439 / 1000000000000), orderedInterval (-24742528510 / 1000000000000) (-24742528509 / 1000000000000)))) (orderedInterval (7040794102 / 1000000000000) (7040794140 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate237_chunkChecks3_1 :
    compactCertificate237.chunkChecks (3 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 3) <| besselDerivativeNearFromState (1024119133694771 / 4000000000000) 3 (IntervalRat.scale (229 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-35628272262 / 1000000000000) (-35628231954 / 1000000000000), orderedInterval (34957007759 / 1000000000000) (34957048066 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 3) <| besselDerivativeNearFromState (591275457520859 / 4000000000000) 3 (IntervalRat.scale (229 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-53326014272 / 1000000000000) (-53326014271 / 1000000000000), orderedInterval (-38069910105 / 1000000000000) (-38069910104 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 3) <| besselDerivativeNearFromState (1049228675263831 / 4000000000000) 3 (IntervalRat.scale (229 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-35398289777 / 1000000000000) (-35398248514 / 1000000000000), orderedInterval (34330602443 / 1000000000000) (34330643705 / 1000000000000)))) (orderedInterval (16826375977 / 1000000000000) (16826527594 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 3) <| besselDerivativeNearFromState (980325530795539 / 4000000000000) 3 (IntervalRat.scale (229 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (37334900551 / 1000000000000) (37334900552 / 1000000000000), orderedInterval (34618067840 / 1000000000000) (34618067841 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 3) <| besselDerivativeNearFromState (699606556096387 / 4000000000000) 3 (IntervalRat.scale (229 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-14508793177 / 1000000000000) (-14508793036 / 1000000000000), orderedInterval (58602395154 / 1000000000000) (58602395295 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 3) <| besselDerivativeNearFromState (793279269866373 / 4000000000000) 3 (IntervalRat.scale (229 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-52476945088 / 1000000000000) (-52476945087 / 1000000000000), orderedInterval (-21227221376 / 1000000000000) (-21227221375 / 1000000000000)))) (orderedInterval (-14227879361 / 1000000000000) (-14227879250 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 3) <| besselDerivativeNearFromState (661353551693237 / 4000000000000) 3 (IntervalRat.scale (229 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (23095700686 / 1000000000000) (23095701578 / 1000000000000), orderedInterval (-57663301638 / 1000000000000) (-57663300747 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 3) <| besselDerivativeNearFromState (584325919761977 / 4000000000000) 3 (IntervalRat.scale (229 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (46839496609 / 1000000000000) (46839558321 / 1000000000000), orderedInterval (-46679544028 / 1000000000000) (-46679482316 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 3) <| besselDerivativeNearFromState (169360426743723 / 800000000000) 3 (IntervalRat.scale (229 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-49894839933 / 1000000000000) (-49894828006 / 1000000000000), orderedInterval (22870228069 / 1000000000000) (22870239996 / 1000000000000)))) (orderedInterval (-7314452037 / 1000000000000) (-7314442646 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate237_chunkChecks3_2 :
    compactCertificate237.chunkChecks (3 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 3) <| besselDerivativeNearFromState (468459853324081 / 4000000000000) 3 (IntervalRat.scale (229 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-73432352476 / 1000000000000) (-73432352341 / 1000000000000), orderedInterval (6908519334 / 1000000000000) (6908519469 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 3) <| besselDerivativeNearFromState (397118605713641 / 4000000000000) 3 (IntervalRat.scale (229 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-36063845208 / 1000000000000) (-36063841758 / 1000000000000), orderedInterval (71678731510 / 1000000000000) (71678734960 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 3) <| besselDerivativeNearFromState (248498384647523 / 4000000000000) 3 (IntervalRat.scale (229 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (7698999402 / 1000000000000) (7698999405 / 1000000000000), orderedInterval (100876242235 / 1000000000000) (100876242238 / 1000000000000)))) (orderedInterval (3423053012 / 1000000000000) (3423053189 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 3) <| besselDerivativeNearFromState (133643257731741 / 4000000000000) 3 (IntervalRat.scale (229 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (49275520958 / 1000000000000) (49275522517 / 1000000000000), orderedInterval (-129686133478 / 1000000000000) (-129686131919 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 3) <| besselDerivativeNearFromState (362867442058223 / 4000000000000) 3 (IntervalRat.scale (229 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-32212027453 / 1000000000000) (-32212027452 / 1000000000000), orderedInterval (-77153679488 / 1000000000000) (-77153679487 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 3) <| besselDerivativeNearFromState (495464469638671 / 4000000000000) 3 (IntervalRat.scale (229 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-60831561334 / 1000000000000) (-60831534354 / 1000000000000), orderedInterval (38180794811 / 1000000000000) (38180821792 / 1000000000000)))) (orderedInterval (2825346798 / 1000000000000) (2825349451 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 3) <| besselDerivativeNearFromState (209501615352477 / 4000000000000) 3 (IntervalRat.scale (229 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (27132284880 / 1000000000000) (27132285222 / 1000000000000), orderedInterval (-107119947317 / 1000000000000) (-107119946976 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 3) <| besselDerivativeNearFromState (851612435225917 / 4000000000000) 3 (IntervalRat.scale (229 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (3258208184 / 1000000000000) (3258208185 / 1000000000000), orderedInterval (54577856235 / 1000000000000) (54577856237 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 3) <| besselDerivativeNearFromState (568837639550003 / 4000000000000) 3 (IntervalRat.scale (229 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-66818879594 / 1000000000000) (-66818879500 / 1000000000000), orderedInterval (3676711987 / 1000000000000) (3676712081 / 1000000000000)))) (orderedInterval (30104657496 / 1000000000000) (30104657633 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate237_chunkChecks3 :
    compactCertificate237.chunkChecks (3 : Fin 5) 0 9 = true :=
  compactCertificate237.chunkChecks_nine_of_three (3 : Fin 5) compactCertificate237_chunkChecks3_0
    compactCertificate237_chunkChecks3_1 compactCertificate237_chunkChecks3_2

theorem compactCertificate237_chunkChecks4_0 :
    compactCertificate237.chunkChecks (4 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 4) <| besselDerivativeNearFromState (229 / 2) 4 (IntervalRat.scale (229 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (60852144261 / 1000000000000) (60852188251 / 1000000000000), orderedInterval (-43358600612 / 1000000000000) (-43358556623 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 4) <| besselDerivativeNearFromState (337360727069329 / 4000000000000) 4 (IntervalRat.scale (229 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-25765723173 / 1000000000000) (-25765723172 / 1000000000000), orderedInterval (-82819992357 / 1000000000000) (-82819992356 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 4) <| besselDerivativeNearFromState (109095527620657 / 800000000000) 4 (IntervalRat.scale (229 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-60136568546 / 1000000000000) (-60136552746 / 1000000000000), orderedInterval (32653860312 / 1000000000000) (32653876112 / 1000000000000)))) (orderedInterval (16695263475 / 1000000000000) (16695283119 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 4) <| besselDerivativeNearFromState (98441018769203 / 4000000000000) 4 (IntervalRat.scale (229 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (41007143304 / 1000000000000) (41007143305 / 1000000000000), orderedInterval (154702146332 / 1000000000000) (154702146333 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 4) <| besselDerivativeNearFromState (264426423288791 / 4000000000000) 4 (IntervalRat.scale (229 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-77875571304 / 1000000000000) (-77875571303 / 1000000000000), orderedInterval (-59123018930 / 1000000000000) (-59123018929 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 4) <| besselDerivativeNearFromState (717969177493947 / 4000000000000) 4 (IntervalRat.scale (229 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-55640388203 / 1000000000000) (-55640388202 / 1000000000000), orderedInterval (-21079824434 / 1000000000000) (-21079824433 / 1000000000000)))) (orderedInterval (23661191880 / 1000000000000) (23661191931 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 4) <| besselDerivativeNearFromState (528852846577811 / 4000000000000) 4 (IntervalRat.scale (229 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (60217748113 / 1000000000000) (60217748114 / 1000000000000), orderedInterval (34252773970 / 1000000000000) (34252773971 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 4) <| besselDerivativeNearFromState (906198366619103 / 4000000000000) 4 (IntervalRat.scale (229 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (48161512288 / 1000000000000) (48161512289 / 1000000000000), orderedInterval (22041671756 / 1000000000000) (22041671757 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 4) <| besselDerivativeNearFromState (667501615352477 / 4000000000000) 4 (IntervalRat.scale (229 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-56518385440 / 1000000000000) (-56518385439 / 1000000000000), orderedInterval (-24742528510 / 1000000000000) (-24742528509 / 1000000000000)))) (orderedInterval (-29051919972 / 1000000000000) (-29051919904 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate237_chunkChecks4_1 :
    compactCertificate237.chunkChecks (4 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 4) <| besselDerivativeNearFromState (1024119133694771 / 4000000000000) 4 (IntervalRat.scale (229 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-35628272262 / 1000000000000) (-35628231954 / 1000000000000), orderedInterval (34957007759 / 1000000000000) (34957048066 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 4) <| besselDerivativeNearFromState (591275457520859 / 4000000000000) 4 (IntervalRat.scale (229 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-53326014272 / 1000000000000) (-53326014271 / 1000000000000), orderedInterval (-38069910105 / 1000000000000) (-38069910104 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 4) <| besselDerivativeNearFromState (1049228675263831 / 4000000000000) 4 (IntervalRat.scale (229 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-35398289777 / 1000000000000) (-35398248514 / 1000000000000), orderedInterval (34330602443 / 1000000000000) (34330643705 / 1000000000000)))) (orderedInterval (8397978603 / 1000000000000) (8398322821 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 4) <| besselDerivativeNearFromState (980325530795539 / 4000000000000) 4 (IntervalRat.scale (229 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (37334900551 / 1000000000000) (37334900552 / 1000000000000), orderedInterval (34618067840 / 1000000000000) (34618067841 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 4) <| besselDerivativeNearFromState (699606556096387 / 4000000000000) 4 (IntervalRat.scale (229 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-14508793177 / 1000000000000) (-14508793036 / 1000000000000), orderedInterval (58602395154 / 1000000000000) (58602395295 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 4) <| besselDerivativeNearFromState (793279269866373 / 4000000000000) 4 (IntervalRat.scale (229 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-52476945088 / 1000000000000) (-52476945087 / 1000000000000), orderedInterval (-21227221376 / 1000000000000) (-21227221375 / 1000000000000)))) (orderedInterval (-18978435158 / 1000000000000) (-18978434975 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 4) <| besselDerivativeNearFromState (661353551693237 / 4000000000000) 4 (IntervalRat.scale (229 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (23095700686 / 1000000000000) (23095701578 / 1000000000000), orderedInterval (-57663301638 / 1000000000000) (-57663300747 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 4) <| besselDerivativeNearFromState (584325919761977 / 4000000000000) 4 (IntervalRat.scale (229 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (46839496609 / 1000000000000) (46839558321 / 1000000000000), orderedInterval (-46679544028 / 1000000000000) (-46679482316 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 4) <| besselDerivativeNearFromState (169360426743723 / 800000000000) 4 (IntervalRat.scale (229 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-49894839933 / 1000000000000) (-49894828006 / 1000000000000), orderedInterval (22870228069 / 1000000000000) (22870239996 / 1000000000000)))) (orderedInterval (-20742792726 / 1000000000000) (-20742779537 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate237_chunkChecks4_2 :
    compactCertificate237.chunkChecks (4 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 4) <| besselDerivativeNearFromState (468459853324081 / 4000000000000) 4 (IntervalRat.scale (229 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-73432352476 / 1000000000000) (-73432352341 / 1000000000000), orderedInterval (6908519334 / 1000000000000) (6908519469 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 4) <| besselDerivativeNearFromState (397118605713641 / 4000000000000) 4 (IntervalRat.scale (229 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-36063845208 / 1000000000000) (-36063841758 / 1000000000000), orderedInterval (71678731510 / 1000000000000) (71678734960 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 4) <| besselDerivativeNearFromState (248498384647523 / 4000000000000) 4 (IntervalRat.scale (229 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (7698999402 / 1000000000000) (7698999405 / 1000000000000), orderedInterval (100876242235 / 1000000000000) (100876242238 / 1000000000000)))) (orderedInterval (13965791134 / 1000000000000) (13965791296 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 4) <| besselDerivativeNearFromState (133643257731741 / 4000000000000) 4 (IntervalRat.scale (229 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (49275520958 / 1000000000000) (49275522517 / 1000000000000), orderedInterval (-129686133478 / 1000000000000) (-129686131919 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 4) <| besselDerivativeNearFromState (362867442058223 / 4000000000000) 4 (IntervalRat.scale (229 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-32212027453 / 1000000000000) (-32212027452 / 1000000000000), orderedInterval (-77153679488 / 1000000000000) (-77153679487 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 4) <| besselDerivativeNearFromState (495464469638671 / 4000000000000) 4 (IntervalRat.scale (229 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-60831561334 / 1000000000000) (-60831534354 / 1000000000000), orderedInterval (38180794811 / 1000000000000) (38180821792 / 1000000000000)))) (orderedInterval (6616637514 / 1000000000000) (6616640406 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 4) <| besselDerivativeNearFromState (209501615352477 / 4000000000000) 4 (IntervalRat.scale (229 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (27132284880 / 1000000000000) (27132285222 / 1000000000000), orderedInterval (-107119947317 / 1000000000000) (-107119946976 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 4) <| besselDerivativeNearFromState (851612435225917 / 4000000000000) 4 (IntervalRat.scale (229 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (3258208184 / 1000000000000) (3258208185 / 1000000000000), orderedInterval (54577856235 / 1000000000000) (54577856237 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 4) <| besselDerivativeNearFromState (568837639550003 / 4000000000000) 4 (IntervalRat.scale (229 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-66818879594 / 1000000000000) (-66818879500 / 1000000000000), orderedInterval (3676711987 / 1000000000000) (3676712081 / 1000000000000)))) (orderedInterval (26141653788 / 1000000000000) (26141653996 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate237_chunkChecks4 :
    compactCertificate237.chunkChecks (4 : Fin 5) 0 9 = true :=
  compactCertificate237.chunkChecks_nine_of_three (4 : Fin 5) compactCertificate237_chunkChecks4_0
    compactCertificate237_chunkChecks4_1 compactCertificate237_chunkChecks4_2

theorem compactCertificate237_chunks :
    ∀ r : Fin 5, ∀ b, compactCertificate237.chunkCheck r b = true :=
  compactCertificate237.chunkChecks_all (by
    intro r
    fin_cases r
    · exact compactCertificate237_chunkChecks0
    · exact compactCertificate237_chunkChecks1
    · exact compactCertificate237_chunkChecks2
    · exact compactCertificate237_chunkChecks3
    · exact compactCertificate237_chunkChecks4)

theorem compactCertificate237_coefficient0 :
    compactCertificate237.coefficientCheck (0 : Fin 5) = true := by
  norm_num [CompactCertificate.coefficientCheck, intervalFinSumHull,
    compactCertificate237, rationalIntervalSubset, orderedInterval, Fin.sum_univ_succ]

theorem compactCertificate237_coefficient1 :
    compactCertificate237.coefficientCheck (1 : Fin 5) = true := by
  norm_num [CompactCertificate.coefficientCheck, intervalFinSumHull,
    compactCertificate237, rationalIntervalSubset, orderedInterval, Fin.sum_univ_succ]

theorem compactCertificate237_coefficient2 :
    compactCertificate237.coefficientCheck (2 : Fin 5) = true := by
  norm_num [CompactCertificate.coefficientCheck, intervalFinSumHull,
    compactCertificate237, rationalIntervalSubset, orderedInterval, Fin.sum_univ_succ]

theorem compactCertificate237_coefficient3 :
    compactCertificate237.coefficientCheck (3 : Fin 5) = true := by
  norm_num [CompactCertificate.coefficientCheck, intervalFinSumHull,
    compactCertificate237, rationalIntervalSubset, orderedInterval, Fin.sum_univ_succ]

theorem compactCertificate237_coefficient4 :
    compactCertificate237.coefficientCheck (4 : Fin 5) = true := by
  norm_num [CompactCertificate.coefficientCheck, intervalFinSumHull,
    compactCertificate237, rationalIntervalSubset, orderedInterval, Fin.sum_univ_succ]

theorem compactCertificate237_coefficients : ∀ r : Fin 5,
    compactCertificate237.coefficientCheck r = true := by
  intro r
  fin_cases r
  · exact compactCertificate237_coefficient0
  · exact compactCertificate237_coefficient1
  · exact compactCertificate237_coefficient2
  · exact compactCertificate237_coefficient3
  · exact compactCertificate237_coefficient4

theorem compactCertificate237_lower : (1 : ℚ) ≤ compactCertificate237.output.lo := by
  norm_num [CompactCertificate.output, CompactCertificate.interval,
    CompactCertificate.coefficientTargetNat, compactCertificate237, dualConstant,
    intervalTaylorSum, intervalPow, intervalSub, intervalMaxAbs, widenInterval,
    rationalErrorInterval, orderedInterval, IntervalRat.add, IntervalRat.mul, IntervalRat.scale,
    IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4]

theorem compactCertificate237_proves {t : ℝ} (ht : t ∈ compactCertificate237.interval) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t :=
  compactCertificate237.proves compactCertificate237_states compactCertificate237_chunks
    compactCertificate237_coefficients compactCertificate237_lower ht

end Erdos232
