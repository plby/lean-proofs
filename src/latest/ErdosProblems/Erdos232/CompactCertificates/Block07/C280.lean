/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, OpenAI Codex
-/
import ErdosProblems.Erdos232.CompactBase

open LeanCert.Core
namespace Erdos232

def compactCertificate280 : CompactCertificate where
  left := 154
  right := 155
  center := 309 / 2
  grid := fun i =>
    match i.val with
    | 0 => 49
    | 1 => 36
    | 2 => 59
    | 3 => 11
    | 4 => 28
    | 5 => 77
    | 6 => 57
    | 7 => 97
    | 8 => 72
    | 9 => 110
    | 10 => 64
    | 11 => 113
    | 12 => 105
    | 13 => 75
    | 14 => 85
    | 15 => 71
    | 16 => 63
    | 17 => 91
    | 18 => 50
    | 19 => 43
    | 20 => 27
    | 21 => 14
    | 22 => 39
    | 23 => 53
    | 24 => 23
    | 25 => 91
    | _ => 61
  point := fun i =>
    match i.val with
    | 0 => 309 / 2
    | 1 => 455216002901409 / 4000000000000
    | 2 => 147207502335297 / 800000000000
    | 3 => 132830894321763 / 4000000000000
    | 4 => 356802466359111 / 4000000000000
    | 5 => 968788104129387 / 4000000000000
    | 6 => 713604932718531 / 4000000000000
    | 7 => 1222774215219663 / 4000000000000
    | 8 => 900689952593517 / 4000000000000
    | 9 => 1381890010094691 / 4000000000000
    | 10 => 797834569318539 / 4000000000000
    | 11 => 1415771443914951 / 4000000000000
    | 12 => 1322797331946819 / 4000000000000
    | 13 => 944010593160627 / 4000000000000
    | 14 => 1070407399077333 / 4000000000000
    | 15 => 892394093769477 / 4000000000000
    | 16 => 788457245443017 / 4000000000000
    | 17 => 228525641326683 / 800000000000
    | 18 => 632113950555201 / 4000000000000
    | 19 => 535849996355961 / 4000000000000
    | 20 => 335310047406483 / 4000000000000
    | 21 => 180330858686061 / 4000000000000
    | 22 => 489633360681183 / 4000000000000
    | 23 => 668552493966591 / 4000000000000
    | 24 => 282689952593517 / 4000000000000
    | 25 => 1149118962815757 / 4000000000000
    | _ => 767558212318563 / 4000000000000
  state := fun i =>
    match i.val with
    | 0 => (orderedInterval (-62583849473 / 1000000000000) (-62583849471 / 1000000000000), orderedInterval (-14071871475 / 1000000000000) (-14071871473 / 1000000000000))
    | 1 => (orderedInterval (74554496443 / 1000000000000) (74554496454 / 1000000000000), orderedInterval (5636965842 / 1000000000000) (5636965853 / 1000000000000))
    | 2 => (orderedInterval (31237466554 / 1000000000000) (31237472435 / 1000000000000), orderedInterval (-49924021497 / 1000000000000) (-49924015616 / 1000000000000))
    | 3 => (orderedInterval (74497943879 / 1000000000000) (74497957261 / 1000000000000), orderedInterval (-117833929792 / 1000000000000) (-117833916410 / 1000000000000))
    | 4 => (orderedInterval (76098092703 / 1000000000000) (76098100706 / 1000000000000), orderedInterval (-37113784604 / 1000000000000) (-37113776601 / 1000000000000))
    | 5 => (orderedInterval (-45199570086 / 1000000000000) (-45199570085 / 1000000000000), orderedInterval (-24104125596 / 1000000000000) (-24104125595 / 1000000000000))
    | 6 => (orderedInterval (-6863441110 / 1000000000000) (-6863441109 / 1000000000000), orderedInterval (-59321969391 / 1000000000000) (-59321969390 / 1000000000000))
    | 7 => (orderedInterval (-44951611018 / 1000000000000) (-44951609717 / 1000000000000), orderedInterval (7940698892 / 1000000000000) (7940700193 / 1000000000000))
    | 8 => (orderedInterval (-12501656617 / 1000000000000) (-12501656525 / 1000000000000), orderedInterval (51709174259 / 1000000000000) (51709174351 / 1000000000000))
    | 9 => (orderedInterval (27070622054 / 1000000000000) (27070622055 / 1000000000000), orderedInterval (33276474003 / 1000000000000) (33276474004 / 1000000000000))
    | 10 => (orderedInterval (-41249151814 / 1000000000000) (-41249088565 / 1000000000000), orderedInterval (38707093600 / 1000000000000) (38707156848 / 1000000000000))
    | 11 => (orderedInterval (11396544993 / 1000000000000) (11396545052 / 1000000000000), orderedInterval (-40866699842 / 1000000000000) (-40866699782 / 1000000000000))
    | 12 => (orderedInterval (-43828532015 / 1000000000000) (-43828531696 / 1000000000000), orderedInterval (2098219864 / 1000000000000) (2098220184 / 1000000000000))
    | 13 => (orderedInterval (-47782251897 / 1000000000000) (-47782251896 / 1000000000000), orderedInterval (-20254684781 / 1000000000000) (-20254684780 / 1000000000000))
    | 14 => (orderedInterval (-47605635137 / 1000000000000) (-47605635133 / 1000000000000), orderedInterval (-10526180239 / 1000000000000) (-10526180235 / 1000000000000))
    | 15 => (orderedInterval (-39429337473 / 1000000000000) (-39429337472 / 1000000000000), orderedInterval (-35951377225 / 1000000000000) (-35951377224 / 1000000000000))
    | 16 => (orderedInterval (1208223986 / 1000000000000) (1208223991 / 1000000000000), orderedInterval (-56820746490 / 1000000000000) (-56820746486 / 1000000000000))
    | 17 => (orderedInterval (-24959464847 / 1000000000000) (-24959464846 / 1000000000000), orderedInterval (-40026778472 / 1000000000000) (-40026778471 / 1000000000000))
    | 18 => (orderedInterval (62632537843 / 1000000000000) (62632538307 / 1000000000000), orderedInterval (-10477212729 / 1000000000000) (-10477212266 / 1000000000000))
    | 19 => (orderedInterval (23088063684 / 1000000000000) (23088064349 / 1000000000000), orderedInterval (-65041470750 / 1000000000000) (-65041470085 / 1000000000000))
    | 20 => (orderedInterval (18301126012 / 1000000000000) (18301126184 / 1000000000000), orderedInterval (-85312402749 / 1000000000000) (-85312402577 / 1000000000000))
    | 21 => (orderedInterval (113082895405 / 1000000000000) (113082896853 / 1000000000000), orderedInterval (-37760243892 / 1000000000000) (-37760242444 / 1000000000000))
    | 22 => (orderedInterval (-44817257591 / 1000000000000) (-44817257590 / 1000000000000), orderedInterval (-56316592048 / 1000000000000) (-56316592047 / 1000000000000))
    | 23 => (orderedInterval (-61000874493 / 1000000000000) (-61000874488 / 1000000000000), orderedInterval (-9188810358 / 1000000000000) (-9188810353 / 1000000000000))
    | 24 => (orderedInterval (68117748734 / 1000000000000) (68117842490 / 1000000000000), orderedInterval (-66572693603 / 1000000000000) (-66572599848 / 1000000000000))
    | 25 => (orderedInterval (-38612293654 / 1000000000000) (-38612205838 / 1000000000000), orderedInterval (26995215163 / 1000000000000) (26995302979 / 1000000000000))
    | _ => (orderedInterval (-49590113507 / 1000000000000) (-49590113506 / 1000000000000), orderedInterval (-29170131036 / 1000000000000) (-29170131035 / 1000000000000))
  chunkTarget := fun r b =>
    match r.val with
    | 0 =>
      match b.val with
      | 0 => orderedInterval (-22278293645 / 1000000000000) (-22278293287 / 1000000000000)
      | 1 => orderedInterval (5183445416 / 1000000000000) (5183445872 / 1000000000000)
      | 2 => orderedInterval (1084347116 / 1000000000000) (1084347167 / 1000000000000)
      | 3 => orderedInterval (-6246259410 / 1000000000000) (-6246254654 / 1000000000000)
      | 4 => orderedInterval (-3486274506 / 1000000000000) (-3486274481 / 1000000000000)
      | 5 => orderedInterval (-1163520519 / 1000000000000) (-1163520503 / 1000000000000)
      | 6 => orderedInterval (-10725454828 / 1000000000000) (-10725454671 / 1000000000000)
      | 7 => orderedInterval (3603712097 / 1000000000000) (3603712144 / 1000000000000)
      | _ => orderedInterval (12858159050 / 1000000000000) (12858166807 / 1000000000000)
    | 1 =>
      match b.val with
      | 0 => orderedInterval (-9028056629 / 1000000000000) (-9028056204 / 1000000000000)
      | 1 => orderedInterval (2178615179 / 1000000000000) (2178615401 / 1000000000000)
      | 2 => orderedInterval (1336755011 / 1000000000000) (1336755109 / 1000000000000)
      | 3 => orderedInterval (-22827877550 / 1000000000000) (-22827871353 / 1000000000000)
      | 4 => orderedInterval (-2914546783 / 1000000000000) (-2914546739 / 1000000000000)
      | 5 => orderedInterval (1654207221 / 1000000000000) (1654207243 / 1000000000000)
      | 6 => orderedInterval (3398548879 / 1000000000000) (3398549027 / 1000000000000)
      | 7 => orderedInterval (1977543263 / 1000000000000) (1977543288 / 1000000000000)
      | _ => orderedInterval (2528019923 / 1000000000000) (2528033534 / 1000000000000)
    | 2 =>
      match b.val with
      | 0 => orderedInterval (21887410061 / 1000000000000) (21887410569 / 1000000000000)
      | 1 => orderedInterval (-8799176805 / 1000000000000) (-8799176670 / 1000000000000)
      | 2 => orderedInterval (-4794774238 / 1000000000000) (-4794774048 / 1000000000000)
      | 3 => orderedInterval (20789547907 / 1000000000000) (20789556074 / 1000000000000)
      | 4 => orderedInterval (6214040382 / 1000000000000) (6214040459 / 1000000000000)
      | 5 => orderedInterval (3235856497 / 1000000000000) (3235856530 / 1000000000000)
      | 6 => orderedInterval (11262180515 / 1000000000000) (11262180658 / 1000000000000)
      | 7 => orderedInterval (-5944406422 / 1000000000000) (-5944406402 / 1000000000000)
      | _ => orderedInterval (-25322102779 / 1000000000000) (-25322077768 / 1000000000000)
    | 3 =>
      match b.val with
      | 0 => orderedInterval (10363845835 / 1000000000000) (10363846439 / 1000000000000)
      | 1 => orderedInterval (-6295999180 / 1000000000000) (-6295999077 / 1000000000000)
      | 2 => orderedInterval (-1940492925 / 1000000000000) (-1940492557 / 1000000000000)
      | 3 => orderedInterval (129648318527 / 1000000000000) (129648329362 / 1000000000000)
      | 4 => orderedInterval (6881037755 / 1000000000000) (6881037897 / 1000000000000)
      | 5 => orderedInterval (953978234 / 1000000000000) (953978284 / 1000000000000)
      | 6 => orderedInterval (-3821556934 / 1000000000000) (-3821556795 / 1000000000000)
      | 7 => orderedInterval (-1505739491 / 1000000000000) (-1505739472 / 1000000000000)
      | _ => orderedInterval (3843633040 / 1000000000000) (3843679347 / 1000000000000)
    | _ =>
      match b.val with
      | 0 => orderedInterval (-21046527996 / 1000000000000) (-21046527273 / 1000000000000)
      | 1 => orderedInterval (19792602491 / 1000000000000) (19792602593 / 1000000000000)
      | 2 => orderedInterval (19911152334 / 1000000000000) (19911153054 / 1000000000000)
      | 3 => orderedInterval (-85797198999 / 1000000000000) (-85797184291 / 1000000000000)
      | 4 => orderedInterval (-5912532681 / 1000000000000) (-5912532413 / 1000000000000)
      | 5 => orderedInterval (-9643112771 / 1000000000000) (-9643112691 / 1000000000000)
      | 6 => orderedInterval (-11598183890 / 1000000000000) (-11598183752 / 1000000000000)
      | 7 => orderedInterval (6807589494 / 1000000000000) (6807589514 / 1000000000000)
      | _ => orderedInterval (59679340650 / 1000000000000) (59679426939 / 1000000000000)
  coefficientTarget := fun i =>
    match i.val with
    | 0 => orderedInterval (-21170139229 / 1000000000000) (-21170125606 / 1000000000000)
    | 1 => orderedInterval (-21696791486 / 1000000000000) (-21696770694 / 1000000000000)
    | 2 => orderedInterval (18528575118 / 1000000000000) (18528609402 / 1000000000000)
    | 3 => orderedInterval (138127024861 / 1000000000000) (138127083428 / 1000000000000)
    | _ => orderedInterval (-27806871368 / 1000000000000) (-27806768320 / 1000000000000)

theorem compactCertificate280_stateChecks0 :
    compactCertificate280.stateChecks 0 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 49 12 (309 / 2)) (orderedInterval (-62583849473 / 1000000000000) (-62583849471 / 1000000000000), orderedInterval (-14071871475 / 1000000000000) (-14071871473 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 36 12 (455216002901409 / 4000000000000)) (orderedInterval (74554496443 / 1000000000000) (74554496454 / 1000000000000), orderedInterval (5636965842 / 1000000000000) (5636965853 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 59 12 (147207502335297 / 800000000000)) (orderedInterval (31237466554 / 1000000000000) (31237472435 / 1000000000000), orderedInterval (-49924021497 / 1000000000000) (-49924015616 / 1000000000000))) = true
  norm_num [besselStateAtRationalPoint, besselIntervalStepZero,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, besselZeroTransition,
    besselInitial, besselGridStateAt, besselGridStateBlock00, besselGridStateBlock01,
    besselGridStateBlock02, besselGridStateBlock03, besselGridStateBlock04,
    besselGridStateBlock05, besselGridStateBlock06, besselGridStateBlock07,
    besselGridStateBlock08, besselGridStateBlock09, besselGridStateBlock10,
    besselGridStateBlock11, besselGridStateBlock12, besselGridStateBlock13,
    besselGridStateBlock14, besselGridState011, besselGridState014, besselGridState023, besselGridState027, besselGridState028, besselGridState036, besselGridState039, besselGridState043, besselGridState049, besselGridState050, besselGridState053, besselGridState057, besselGridState059, besselGridState061, besselGridState063, besselGridState064, besselGridState071, besselGridState072, besselGridState075, besselGridState077, besselGridState085, besselGridState091, besselGridState097, besselGridState105, besselGridState110, besselGridState113, besselStateSubset, linearInterval, widenInterval,
    rationalErrorInterval, rationalIntervalSubset, orderedInterval, Finset.sum_range_succ,
    IntervalRat.add, IntervalRat.mul, IntervalRat.scale, IntervalRat.singleton]

theorem compactCertificate280_stateChecks1 :
    compactCertificate280.stateChecks 3 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 11 12 (132830894321763 / 4000000000000)) (orderedInterval (74497943879 / 1000000000000) (74497957261 / 1000000000000), orderedInterval (-117833929792 / 1000000000000) (-117833916410 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 28 12 (356802466359111 / 4000000000000)) (orderedInterval (76098092703 / 1000000000000) (76098100706 / 1000000000000), orderedInterval (-37113784604 / 1000000000000) (-37113776601 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 77 12 (968788104129387 / 4000000000000)) (orderedInterval (-45199570086 / 1000000000000) (-45199570085 / 1000000000000), orderedInterval (-24104125596 / 1000000000000) (-24104125595 / 1000000000000))) = true
  norm_num [besselStateAtRationalPoint, besselIntervalStepZero,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, besselZeroTransition,
    besselInitial, besselGridStateAt, besselGridStateBlock00, besselGridStateBlock01,
    besselGridStateBlock02, besselGridStateBlock03, besselGridStateBlock04,
    besselGridStateBlock05, besselGridStateBlock06, besselGridStateBlock07,
    besselGridStateBlock08, besselGridStateBlock09, besselGridStateBlock10,
    besselGridStateBlock11, besselGridStateBlock12, besselGridStateBlock13,
    besselGridStateBlock14, besselGridState011, besselGridState014, besselGridState023, besselGridState027, besselGridState028, besselGridState036, besselGridState039, besselGridState043, besselGridState049, besselGridState050, besselGridState053, besselGridState057, besselGridState059, besselGridState061, besselGridState063, besselGridState064, besselGridState071, besselGridState072, besselGridState075, besselGridState077, besselGridState085, besselGridState091, besselGridState097, besselGridState105, besselGridState110, besselGridState113, besselStateSubset, linearInterval, widenInterval,
    rationalErrorInterval, rationalIntervalSubset, orderedInterval, Finset.sum_range_succ,
    IntervalRat.add, IntervalRat.mul, IntervalRat.scale, IntervalRat.singleton]

theorem compactCertificate280_stateChecks2 :
    compactCertificate280.stateChecks 6 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 57 12 (713604932718531 / 4000000000000)) (orderedInterval (-6863441110 / 1000000000000) (-6863441109 / 1000000000000), orderedInterval (-59321969391 / 1000000000000) (-59321969390 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 97 12 (1222774215219663 / 4000000000000)) (orderedInterval (-44951611018 / 1000000000000) (-44951609717 / 1000000000000), orderedInterval (7940698892 / 1000000000000) (7940700193 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 72 12 (900689952593517 / 4000000000000)) (orderedInterval (-12501656617 / 1000000000000) (-12501656525 / 1000000000000), orderedInterval (51709174259 / 1000000000000) (51709174351 / 1000000000000))) = true
  norm_num [besselStateAtRationalPoint, besselIntervalStepZero,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, besselZeroTransition,
    besselInitial, besselGridStateAt, besselGridStateBlock00, besselGridStateBlock01,
    besselGridStateBlock02, besselGridStateBlock03, besselGridStateBlock04,
    besselGridStateBlock05, besselGridStateBlock06, besselGridStateBlock07,
    besselGridStateBlock08, besselGridStateBlock09, besselGridStateBlock10,
    besselGridStateBlock11, besselGridStateBlock12, besselGridStateBlock13,
    besselGridStateBlock14, besselGridState011, besselGridState014, besselGridState023, besselGridState027, besselGridState028, besselGridState036, besselGridState039, besselGridState043, besselGridState049, besselGridState050, besselGridState053, besselGridState057, besselGridState059, besselGridState061, besselGridState063, besselGridState064, besselGridState071, besselGridState072, besselGridState075, besselGridState077, besselGridState085, besselGridState091, besselGridState097, besselGridState105, besselGridState110, besselGridState113, besselStateSubset, linearInterval, widenInterval,
    rationalErrorInterval, rationalIntervalSubset, orderedInterval, Finset.sum_range_succ,
    IntervalRat.add, IntervalRat.mul, IntervalRat.scale, IntervalRat.singleton]

theorem compactCertificate280_stateChecks3 :
    compactCertificate280.stateChecks 9 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 110 12 (1381890010094691 / 4000000000000)) (orderedInterval (27070622054 / 1000000000000) (27070622055 / 1000000000000), orderedInterval (33276474003 / 1000000000000) (33276474004 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 64 12 (797834569318539 / 4000000000000)) (orderedInterval (-41249151814 / 1000000000000) (-41249088565 / 1000000000000), orderedInterval (38707093600 / 1000000000000) (38707156848 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 113 12 (1415771443914951 / 4000000000000)) (orderedInterval (11396544993 / 1000000000000) (11396545052 / 1000000000000), orderedInterval (-40866699842 / 1000000000000) (-40866699782 / 1000000000000))) = true
  norm_num [besselStateAtRationalPoint, besselIntervalStepZero,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, besselZeroTransition,
    besselInitial, besselGridStateAt, besselGridStateBlock00, besselGridStateBlock01,
    besselGridStateBlock02, besselGridStateBlock03, besselGridStateBlock04,
    besselGridStateBlock05, besselGridStateBlock06, besselGridStateBlock07,
    besselGridStateBlock08, besselGridStateBlock09, besselGridStateBlock10,
    besselGridStateBlock11, besselGridStateBlock12, besselGridStateBlock13,
    besselGridStateBlock14, besselGridState011, besselGridState014, besselGridState023, besselGridState027, besselGridState028, besselGridState036, besselGridState039, besselGridState043, besselGridState049, besselGridState050, besselGridState053, besselGridState057, besselGridState059, besselGridState061, besselGridState063, besselGridState064, besselGridState071, besselGridState072, besselGridState075, besselGridState077, besselGridState085, besselGridState091, besselGridState097, besselGridState105, besselGridState110, besselGridState113, besselStateSubset, linearInterval, widenInterval,
    rationalErrorInterval, rationalIntervalSubset, orderedInterval, Finset.sum_range_succ,
    IntervalRat.add, IntervalRat.mul, IntervalRat.scale, IntervalRat.singleton]

theorem compactCertificate280_stateChecks4 :
    compactCertificate280.stateChecks 12 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 105 12 (1322797331946819 / 4000000000000)) (orderedInterval (-43828532015 / 1000000000000) (-43828531696 / 1000000000000), orderedInterval (2098219864 / 1000000000000) (2098220184 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 75 12 (944010593160627 / 4000000000000)) (orderedInterval (-47782251897 / 1000000000000) (-47782251896 / 1000000000000), orderedInterval (-20254684781 / 1000000000000) (-20254684780 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 85 12 (1070407399077333 / 4000000000000)) (orderedInterval (-47605635137 / 1000000000000) (-47605635133 / 1000000000000), orderedInterval (-10526180239 / 1000000000000) (-10526180235 / 1000000000000))) = true
  norm_num [besselStateAtRationalPoint, besselIntervalStepZero,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, besselZeroTransition,
    besselInitial, besselGridStateAt, besselGridStateBlock00, besselGridStateBlock01,
    besselGridStateBlock02, besselGridStateBlock03, besselGridStateBlock04,
    besselGridStateBlock05, besselGridStateBlock06, besselGridStateBlock07,
    besselGridStateBlock08, besselGridStateBlock09, besselGridStateBlock10,
    besselGridStateBlock11, besselGridStateBlock12, besselGridStateBlock13,
    besselGridStateBlock14, besselGridState011, besselGridState014, besselGridState023, besselGridState027, besselGridState028, besselGridState036, besselGridState039, besselGridState043, besselGridState049, besselGridState050, besselGridState053, besselGridState057, besselGridState059, besselGridState061, besselGridState063, besselGridState064, besselGridState071, besselGridState072, besselGridState075, besselGridState077, besselGridState085, besselGridState091, besselGridState097, besselGridState105, besselGridState110, besselGridState113, besselStateSubset, linearInterval, widenInterval,
    rationalErrorInterval, rationalIntervalSubset, orderedInterval, Finset.sum_range_succ,
    IntervalRat.add, IntervalRat.mul, IntervalRat.scale, IntervalRat.singleton]

theorem compactCertificate280_stateChecks5 :
    compactCertificate280.stateChecks 15 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 71 12 (892394093769477 / 4000000000000)) (orderedInterval (-39429337473 / 1000000000000) (-39429337472 / 1000000000000), orderedInterval (-35951377225 / 1000000000000) (-35951377224 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 63 12 (788457245443017 / 4000000000000)) (orderedInterval (1208223986 / 1000000000000) (1208223991 / 1000000000000), orderedInterval (-56820746490 / 1000000000000) (-56820746486 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 91 12 (228525641326683 / 800000000000)) (orderedInterval (-24959464847 / 1000000000000) (-24959464846 / 1000000000000), orderedInterval (-40026778472 / 1000000000000) (-40026778471 / 1000000000000))) = true
  norm_num [besselStateAtRationalPoint, besselIntervalStepZero,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, besselZeroTransition,
    besselInitial, besselGridStateAt, besselGridStateBlock00, besselGridStateBlock01,
    besselGridStateBlock02, besselGridStateBlock03, besselGridStateBlock04,
    besselGridStateBlock05, besselGridStateBlock06, besselGridStateBlock07,
    besselGridStateBlock08, besselGridStateBlock09, besselGridStateBlock10,
    besselGridStateBlock11, besselGridStateBlock12, besselGridStateBlock13,
    besselGridStateBlock14, besselGridState011, besselGridState014, besselGridState023, besselGridState027, besselGridState028, besselGridState036, besselGridState039, besselGridState043, besselGridState049, besselGridState050, besselGridState053, besselGridState057, besselGridState059, besselGridState061, besselGridState063, besselGridState064, besselGridState071, besselGridState072, besselGridState075, besselGridState077, besselGridState085, besselGridState091, besselGridState097, besselGridState105, besselGridState110, besselGridState113, besselStateSubset, linearInterval, widenInterval,
    rationalErrorInterval, rationalIntervalSubset, orderedInterval, Finset.sum_range_succ,
    IntervalRat.add, IntervalRat.mul, IntervalRat.scale, IntervalRat.singleton]

theorem compactCertificate280_stateChecks6 :
    compactCertificate280.stateChecks 18 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 50 12 (632113950555201 / 4000000000000)) (orderedInterval (62632537843 / 1000000000000) (62632538307 / 1000000000000), orderedInterval (-10477212729 / 1000000000000) (-10477212266 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 43 12 (535849996355961 / 4000000000000)) (orderedInterval (23088063684 / 1000000000000) (23088064349 / 1000000000000), orderedInterval (-65041470750 / 1000000000000) (-65041470085 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 27 12 (335310047406483 / 4000000000000)) (orderedInterval (18301126012 / 1000000000000) (18301126184 / 1000000000000), orderedInterval (-85312402749 / 1000000000000) (-85312402577 / 1000000000000))) = true
  norm_num [besselStateAtRationalPoint, besselIntervalStepZero,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, besselZeroTransition,
    besselInitial, besselGridStateAt, besselGridStateBlock00, besselGridStateBlock01,
    besselGridStateBlock02, besselGridStateBlock03, besselGridStateBlock04,
    besselGridStateBlock05, besselGridStateBlock06, besselGridStateBlock07,
    besselGridStateBlock08, besselGridStateBlock09, besselGridStateBlock10,
    besselGridStateBlock11, besselGridStateBlock12, besselGridStateBlock13,
    besselGridStateBlock14, besselGridState011, besselGridState014, besselGridState023, besselGridState027, besselGridState028, besselGridState036, besselGridState039, besselGridState043, besselGridState049, besselGridState050, besselGridState053, besselGridState057, besselGridState059, besselGridState061, besselGridState063, besselGridState064, besselGridState071, besselGridState072, besselGridState075, besselGridState077, besselGridState085, besselGridState091, besselGridState097, besselGridState105, besselGridState110, besselGridState113, besselStateSubset, linearInterval, widenInterval,
    rationalErrorInterval, rationalIntervalSubset, orderedInterval, Finset.sum_range_succ,
    IntervalRat.add, IntervalRat.mul, IntervalRat.scale, IntervalRat.singleton]

theorem compactCertificate280_stateChecks7 :
    compactCertificate280.stateChecks 21 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 14 12 (180330858686061 / 4000000000000)) (orderedInterval (113082895405 / 1000000000000) (113082896853 / 1000000000000), orderedInterval (-37760243892 / 1000000000000) (-37760242444 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 39 12 (489633360681183 / 4000000000000)) (orderedInterval (-44817257591 / 1000000000000) (-44817257590 / 1000000000000), orderedInterval (-56316592048 / 1000000000000) (-56316592047 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 53 12 (668552493966591 / 4000000000000)) (orderedInterval (-61000874493 / 1000000000000) (-61000874488 / 1000000000000), orderedInterval (-9188810358 / 1000000000000) (-9188810353 / 1000000000000))) = true
  norm_num [besselStateAtRationalPoint, besselIntervalStepZero,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, besselZeroTransition,
    besselInitial, besselGridStateAt, besselGridStateBlock00, besselGridStateBlock01,
    besselGridStateBlock02, besselGridStateBlock03, besselGridStateBlock04,
    besselGridStateBlock05, besselGridStateBlock06, besselGridStateBlock07,
    besselGridStateBlock08, besselGridStateBlock09, besselGridStateBlock10,
    besselGridStateBlock11, besselGridStateBlock12, besselGridStateBlock13,
    besselGridStateBlock14, besselGridState011, besselGridState014, besselGridState023, besselGridState027, besselGridState028, besselGridState036, besselGridState039, besselGridState043, besselGridState049, besselGridState050, besselGridState053, besselGridState057, besselGridState059, besselGridState061, besselGridState063, besselGridState064, besselGridState071, besselGridState072, besselGridState075, besselGridState077, besselGridState085, besselGridState091, besselGridState097, besselGridState105, besselGridState110, besselGridState113, besselStateSubset, linearInterval, widenInterval,
    rationalErrorInterval, rationalIntervalSubset, orderedInterval, Finset.sum_range_succ,
    IntervalRat.add, IntervalRat.mul, IntervalRat.scale, IntervalRat.singleton]

theorem compactCertificate280_stateChecks8 :
    compactCertificate280.stateChecks 24 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 23 12 (282689952593517 / 4000000000000)) (orderedInterval (68117748734 / 1000000000000) (68117842490 / 1000000000000), orderedInterval (-66572693603 / 1000000000000) (-66572599848 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 91 12 (1149118962815757 / 4000000000000)) (orderedInterval (-38612293654 / 1000000000000) (-38612205838 / 1000000000000), orderedInterval (26995215163 / 1000000000000) (26995302979 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 61 12 (767558212318563 / 4000000000000)) (orderedInterval (-49590113507 / 1000000000000) (-49590113506 / 1000000000000), orderedInterval (-29170131036 / 1000000000000) (-29170131035 / 1000000000000))) = true
  norm_num [besselStateAtRationalPoint, besselIntervalStepZero,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, besselZeroTransition,
    besselInitial, besselGridStateAt, besselGridStateBlock00, besselGridStateBlock01,
    besselGridStateBlock02, besselGridStateBlock03, besselGridStateBlock04,
    besselGridStateBlock05, besselGridStateBlock06, besselGridStateBlock07,
    besselGridStateBlock08, besselGridStateBlock09, besselGridStateBlock10,
    besselGridStateBlock11, besselGridStateBlock12, besselGridStateBlock13,
    besselGridStateBlock14, besselGridState011, besselGridState014, besselGridState023, besselGridState027, besselGridState028, besselGridState036, besselGridState039, besselGridState043, besselGridState049, besselGridState050, besselGridState053, besselGridState057, besselGridState059, besselGridState061, besselGridState063, besselGridState064, besselGridState071, besselGridState072, besselGridState075, besselGridState077, besselGridState085, besselGridState091, besselGridState097, besselGridState105, besselGridState110, besselGridState113, besselStateSubset, linearInterval, widenInterval,
    rationalErrorInterval, rationalIntervalSubset, orderedInterval, Finset.sum_range_succ,
    IntervalRat.add, IntervalRat.mul, IntervalRat.scale, IntervalRat.singleton]

theorem compactCertificate280_states : ∀ j,
    BesselStateValid (compactCertificate280.point j) (compactCertificate280.state j) :=
  compactCertificate280.statesValid_of_checks3 compactCertificate280_stateChecks0
    compactCertificate280_stateChecks1 compactCertificate280_stateChecks2
    compactCertificate280_stateChecks3 compactCertificate280_stateChecks4
    compactCertificate280_stateChecks5 compactCertificate280_stateChecks6
    compactCertificate280_stateChecks7 compactCertificate280_stateChecks8

theorem compactCertificate280_chunkChecks0_0 :
    compactCertificate280.chunkChecks (0 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 0) <| besselDerivativeNearFromState (309 / 2) 0 (IntervalRat.scale (309 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-62583849473 / 1000000000000) (-62583849471 / 1000000000000), orderedInterval (-14071871475 / 1000000000000) (-14071871473 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 0) <| besselDerivativeNearFromState (455216002901409 / 4000000000000) 0 (IntervalRat.scale (309 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (74554496443 / 1000000000000) (74554496454 / 1000000000000), orderedInterval (5636965842 / 1000000000000) (5636965853 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 0) <| besselDerivativeNearFromState (147207502335297 / 800000000000) 0 (IntervalRat.scale (309 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (31237466554 / 1000000000000) (31237472435 / 1000000000000), orderedInterval (-49924021497 / 1000000000000) (-49924015616 / 1000000000000)))) (orderedInterval (-22278293645 / 1000000000000) (-22278293287 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 0) <| besselDerivativeNearFromState (132830894321763 / 4000000000000) 0 (IntervalRat.scale (309 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (74497943879 / 1000000000000) (74497957261 / 1000000000000), orderedInterval (-117833929792 / 1000000000000) (-117833916410 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 0) <| besselDerivativeNearFromState (356802466359111 / 4000000000000) 0 (IntervalRat.scale (309 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (76098092703 / 1000000000000) (76098100706 / 1000000000000), orderedInterval (-37113784604 / 1000000000000) (-37113776601 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 0) <| besselDerivativeNearFromState (968788104129387 / 4000000000000) 0 (IntervalRat.scale (309 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-45199570086 / 1000000000000) (-45199570085 / 1000000000000), orderedInterval (-24104125596 / 1000000000000) (-24104125595 / 1000000000000)))) (orderedInterval (5183445416 / 1000000000000) (5183445872 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 0) <| besselDerivativeNearFromState (713604932718531 / 4000000000000) 0 (IntervalRat.scale (309 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-6863441110 / 1000000000000) (-6863441109 / 1000000000000), orderedInterval (-59321969391 / 1000000000000) (-59321969390 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 0) <| besselDerivativeNearFromState (1222774215219663 / 4000000000000) 0 (IntervalRat.scale (309 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-44951611018 / 1000000000000) (-44951609717 / 1000000000000), orderedInterval (7940698892 / 1000000000000) (7940700193 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 0) <| besselDerivativeNearFromState (900689952593517 / 4000000000000) 0 (IntervalRat.scale (309 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-12501656617 / 1000000000000) (-12501656525 / 1000000000000), orderedInterval (51709174259 / 1000000000000) (51709174351 / 1000000000000)))) (orderedInterval (1084347116 / 1000000000000) (1084347167 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate280_chunkChecks0_1 :
    compactCertificate280.chunkChecks (0 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 0) <| besselDerivativeNearFromState (1381890010094691 / 4000000000000) 0 (IntervalRat.scale (309 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (27070622054 / 1000000000000) (27070622055 / 1000000000000), orderedInterval (33276474003 / 1000000000000) (33276474004 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 0) <| besselDerivativeNearFromState (797834569318539 / 4000000000000) 0 (IntervalRat.scale (309 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-41249151814 / 1000000000000) (-41249088565 / 1000000000000), orderedInterval (38707093600 / 1000000000000) (38707156848 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 0) <| besselDerivativeNearFromState (1415771443914951 / 4000000000000) 0 (IntervalRat.scale (309 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (11396544993 / 1000000000000) (11396545052 / 1000000000000), orderedInterval (-40866699842 / 1000000000000) (-40866699782 / 1000000000000)))) (orderedInterval (-6246259410 / 1000000000000) (-6246254654 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 0) <| besselDerivativeNearFromState (1322797331946819 / 4000000000000) 0 (IntervalRat.scale (309 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-43828532015 / 1000000000000) (-43828531696 / 1000000000000), orderedInterval (2098219864 / 1000000000000) (2098220184 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 0) <| besselDerivativeNearFromState (944010593160627 / 4000000000000) 0 (IntervalRat.scale (309 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-47782251897 / 1000000000000) (-47782251896 / 1000000000000), orderedInterval (-20254684781 / 1000000000000) (-20254684780 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 0) <| besselDerivativeNearFromState (1070407399077333 / 4000000000000) 0 (IntervalRat.scale (309 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-47605635137 / 1000000000000) (-47605635133 / 1000000000000), orderedInterval (-10526180239 / 1000000000000) (-10526180235 / 1000000000000)))) (orderedInterval (-3486274506 / 1000000000000) (-3486274481 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 0) <| besselDerivativeNearFromState (892394093769477 / 4000000000000) 0 (IntervalRat.scale (309 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-39429337473 / 1000000000000) (-39429337472 / 1000000000000), orderedInterval (-35951377225 / 1000000000000) (-35951377224 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 0) <| besselDerivativeNearFromState (788457245443017 / 4000000000000) 0 (IntervalRat.scale (309 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (1208223986 / 1000000000000) (1208223991 / 1000000000000), orderedInterval (-56820746490 / 1000000000000) (-56820746486 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 0) <| besselDerivativeNearFromState (228525641326683 / 800000000000) 0 (IntervalRat.scale (309 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-24959464847 / 1000000000000) (-24959464846 / 1000000000000), orderedInterval (-40026778472 / 1000000000000) (-40026778471 / 1000000000000)))) (orderedInterval (-1163520519 / 1000000000000) (-1163520503 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate280_chunkChecks0_2 :
    compactCertificate280.chunkChecks (0 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 0) <| besselDerivativeNearFromState (632113950555201 / 4000000000000) 0 (IntervalRat.scale (309 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (62632537843 / 1000000000000) (62632538307 / 1000000000000), orderedInterval (-10477212729 / 1000000000000) (-10477212266 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 0) <| besselDerivativeNearFromState (535849996355961 / 4000000000000) 0 (IntervalRat.scale (309 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (23088063684 / 1000000000000) (23088064349 / 1000000000000), orderedInterval (-65041470750 / 1000000000000) (-65041470085 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 0) <| besselDerivativeNearFromState (335310047406483 / 4000000000000) 0 (IntervalRat.scale (309 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (18301126012 / 1000000000000) (18301126184 / 1000000000000), orderedInterval (-85312402749 / 1000000000000) (-85312402577 / 1000000000000)))) (orderedInterval (-10725454828 / 1000000000000) (-10725454671 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 0) <| besselDerivativeNearFromState (180330858686061 / 4000000000000) 0 (IntervalRat.scale (309 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (113082895405 / 1000000000000) (113082896853 / 1000000000000), orderedInterval (-37760243892 / 1000000000000) (-37760242444 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 0) <| besselDerivativeNearFromState (489633360681183 / 4000000000000) 0 (IntervalRat.scale (309 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-44817257591 / 1000000000000) (-44817257590 / 1000000000000), orderedInterval (-56316592048 / 1000000000000) (-56316592047 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 0) <| besselDerivativeNearFromState (668552493966591 / 4000000000000) 0 (IntervalRat.scale (309 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-61000874493 / 1000000000000) (-61000874488 / 1000000000000), orderedInterval (-9188810358 / 1000000000000) (-9188810353 / 1000000000000)))) (orderedInterval (3603712097 / 1000000000000) (3603712144 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 0) <| besselDerivativeNearFromState (282689952593517 / 4000000000000) 0 (IntervalRat.scale (309 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (68117748734 / 1000000000000) (68117842490 / 1000000000000), orderedInterval (-66572693603 / 1000000000000) (-66572599848 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 0) <| besselDerivativeNearFromState (1149118962815757 / 4000000000000) 0 (IntervalRat.scale (309 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-38612293654 / 1000000000000) (-38612205838 / 1000000000000), orderedInterval (26995215163 / 1000000000000) (26995302979 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 0) <| besselDerivativeNearFromState (767558212318563 / 4000000000000) 0 (IntervalRat.scale (309 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-49590113507 / 1000000000000) (-49590113506 / 1000000000000), orderedInterval (-29170131036 / 1000000000000) (-29170131035 / 1000000000000)))) (orderedInterval (12858159050 / 1000000000000) (12858166807 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate280_chunkChecks0 :
    compactCertificate280.chunkChecks (0 : Fin 5) 0 9 = true :=
  compactCertificate280.chunkChecks_nine_of_three (0 : Fin 5) compactCertificate280_chunkChecks0_0
    compactCertificate280_chunkChecks0_1 compactCertificate280_chunkChecks0_2

theorem compactCertificate280_chunkChecks1_0 :
    compactCertificate280.chunkChecks (1 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 1) <| besselDerivativeNearFromState (309 / 2) 1 (IntervalRat.scale (309 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-62583849473 / 1000000000000) (-62583849471 / 1000000000000), orderedInterval (-14071871475 / 1000000000000) (-14071871473 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 1) <| besselDerivativeNearFromState (455216002901409 / 4000000000000) 1 (IntervalRat.scale (309 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (74554496443 / 1000000000000) (74554496454 / 1000000000000), orderedInterval (5636965842 / 1000000000000) (5636965853 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 1) <| besselDerivativeNearFromState (147207502335297 / 800000000000) 1 (IntervalRat.scale (309 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (31237466554 / 1000000000000) (31237472435 / 1000000000000), orderedInterval (-49924021497 / 1000000000000) (-49924015616 / 1000000000000)))) (orderedInterval (-9028056629 / 1000000000000) (-9028056204 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 1) <| besselDerivativeNearFromState (132830894321763 / 4000000000000) 1 (IntervalRat.scale (309 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (74497943879 / 1000000000000) (74497957261 / 1000000000000), orderedInterval (-117833929792 / 1000000000000) (-117833916410 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 1) <| besselDerivativeNearFromState (356802466359111 / 4000000000000) 1 (IntervalRat.scale (309 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (76098092703 / 1000000000000) (76098100706 / 1000000000000), orderedInterval (-37113784604 / 1000000000000) (-37113776601 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 1) <| besselDerivativeNearFromState (968788104129387 / 4000000000000) 1 (IntervalRat.scale (309 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-45199570086 / 1000000000000) (-45199570085 / 1000000000000), orderedInterval (-24104125596 / 1000000000000) (-24104125595 / 1000000000000)))) (orderedInterval (2178615179 / 1000000000000) (2178615401 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 1) <| besselDerivativeNearFromState (713604932718531 / 4000000000000) 1 (IntervalRat.scale (309 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-6863441110 / 1000000000000) (-6863441109 / 1000000000000), orderedInterval (-59321969391 / 1000000000000) (-59321969390 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 1) <| besselDerivativeNearFromState (1222774215219663 / 4000000000000) 1 (IntervalRat.scale (309 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-44951611018 / 1000000000000) (-44951609717 / 1000000000000), orderedInterval (7940698892 / 1000000000000) (7940700193 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 1) <| besselDerivativeNearFromState (900689952593517 / 4000000000000) 1 (IntervalRat.scale (309 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-12501656617 / 1000000000000) (-12501656525 / 1000000000000), orderedInterval (51709174259 / 1000000000000) (51709174351 / 1000000000000)))) (orderedInterval (1336755011 / 1000000000000) (1336755109 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate280_chunkChecks1_1 :
    compactCertificate280.chunkChecks (1 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 1) <| besselDerivativeNearFromState (1381890010094691 / 4000000000000) 1 (IntervalRat.scale (309 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (27070622054 / 1000000000000) (27070622055 / 1000000000000), orderedInterval (33276474003 / 1000000000000) (33276474004 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 1) <| besselDerivativeNearFromState (797834569318539 / 4000000000000) 1 (IntervalRat.scale (309 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-41249151814 / 1000000000000) (-41249088565 / 1000000000000), orderedInterval (38707093600 / 1000000000000) (38707156848 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 1) <| besselDerivativeNearFromState (1415771443914951 / 4000000000000) 1 (IntervalRat.scale (309 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (11396544993 / 1000000000000) (11396545052 / 1000000000000), orderedInterval (-40866699842 / 1000000000000) (-40866699782 / 1000000000000)))) (orderedInterval (-22827877550 / 1000000000000) (-22827871353 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 1) <| besselDerivativeNearFromState (1322797331946819 / 4000000000000) 1 (IntervalRat.scale (309 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-43828532015 / 1000000000000) (-43828531696 / 1000000000000), orderedInterval (2098219864 / 1000000000000) (2098220184 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 1) <| besselDerivativeNearFromState (944010593160627 / 4000000000000) 1 (IntervalRat.scale (309 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-47782251897 / 1000000000000) (-47782251896 / 1000000000000), orderedInterval (-20254684781 / 1000000000000) (-20254684780 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 1) <| besselDerivativeNearFromState (1070407399077333 / 4000000000000) 1 (IntervalRat.scale (309 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-47605635137 / 1000000000000) (-47605635133 / 1000000000000), orderedInterval (-10526180239 / 1000000000000) (-10526180235 / 1000000000000)))) (orderedInterval (-2914546783 / 1000000000000) (-2914546739 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 1) <| besselDerivativeNearFromState (892394093769477 / 4000000000000) 1 (IntervalRat.scale (309 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-39429337473 / 1000000000000) (-39429337472 / 1000000000000), orderedInterval (-35951377225 / 1000000000000) (-35951377224 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 1) <| besselDerivativeNearFromState (788457245443017 / 4000000000000) 1 (IntervalRat.scale (309 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (1208223986 / 1000000000000) (1208223991 / 1000000000000), orderedInterval (-56820746490 / 1000000000000) (-56820746486 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 1) <| besselDerivativeNearFromState (228525641326683 / 800000000000) 1 (IntervalRat.scale (309 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-24959464847 / 1000000000000) (-24959464846 / 1000000000000), orderedInterval (-40026778472 / 1000000000000) (-40026778471 / 1000000000000)))) (orderedInterval (1654207221 / 1000000000000) (1654207243 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate280_chunkChecks1_2 :
    compactCertificate280.chunkChecks (1 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 1) <| besselDerivativeNearFromState (632113950555201 / 4000000000000) 1 (IntervalRat.scale (309 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (62632537843 / 1000000000000) (62632538307 / 1000000000000), orderedInterval (-10477212729 / 1000000000000) (-10477212266 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 1) <| besselDerivativeNearFromState (535849996355961 / 4000000000000) 1 (IntervalRat.scale (309 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (23088063684 / 1000000000000) (23088064349 / 1000000000000), orderedInterval (-65041470750 / 1000000000000) (-65041470085 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 1) <| besselDerivativeNearFromState (335310047406483 / 4000000000000) 1 (IntervalRat.scale (309 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (18301126012 / 1000000000000) (18301126184 / 1000000000000), orderedInterval (-85312402749 / 1000000000000) (-85312402577 / 1000000000000)))) (orderedInterval (3398548879 / 1000000000000) (3398549027 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 1) <| besselDerivativeNearFromState (180330858686061 / 4000000000000) 1 (IntervalRat.scale (309 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (113082895405 / 1000000000000) (113082896853 / 1000000000000), orderedInterval (-37760243892 / 1000000000000) (-37760242444 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 1) <| besselDerivativeNearFromState (489633360681183 / 4000000000000) 1 (IntervalRat.scale (309 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-44817257591 / 1000000000000) (-44817257590 / 1000000000000), orderedInterval (-56316592048 / 1000000000000) (-56316592047 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 1) <| besselDerivativeNearFromState (668552493966591 / 4000000000000) 1 (IntervalRat.scale (309 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-61000874493 / 1000000000000) (-61000874488 / 1000000000000), orderedInterval (-9188810358 / 1000000000000) (-9188810353 / 1000000000000)))) (orderedInterval (1977543263 / 1000000000000) (1977543288 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 1) <| besselDerivativeNearFromState (282689952593517 / 4000000000000) 1 (IntervalRat.scale (309 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (68117748734 / 1000000000000) (68117842490 / 1000000000000), orderedInterval (-66572693603 / 1000000000000) (-66572599848 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 1) <| besselDerivativeNearFromState (1149118962815757 / 4000000000000) 1 (IntervalRat.scale (309 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-38612293654 / 1000000000000) (-38612205838 / 1000000000000), orderedInterval (26995215163 / 1000000000000) (26995302979 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 1) <| besselDerivativeNearFromState (767558212318563 / 4000000000000) 1 (IntervalRat.scale (309 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-49590113507 / 1000000000000) (-49590113506 / 1000000000000), orderedInterval (-29170131036 / 1000000000000) (-29170131035 / 1000000000000)))) (orderedInterval (2528019923 / 1000000000000) (2528033534 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate280_chunkChecks1 :
    compactCertificate280.chunkChecks (1 : Fin 5) 0 9 = true :=
  compactCertificate280.chunkChecks_nine_of_three (1 : Fin 5) compactCertificate280_chunkChecks1_0
    compactCertificate280_chunkChecks1_1 compactCertificate280_chunkChecks1_2

theorem compactCertificate280_chunkChecks2_0 :
    compactCertificate280.chunkChecks (2 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 2) <| besselDerivativeNearFromState (309 / 2) 2 (IntervalRat.scale (309 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-62583849473 / 1000000000000) (-62583849471 / 1000000000000), orderedInterval (-14071871475 / 1000000000000) (-14071871473 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 2) <| besselDerivativeNearFromState (455216002901409 / 4000000000000) 2 (IntervalRat.scale (309 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (74554496443 / 1000000000000) (74554496454 / 1000000000000), orderedInterval (5636965842 / 1000000000000) (5636965853 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 2) <| besselDerivativeNearFromState (147207502335297 / 800000000000) 2 (IntervalRat.scale (309 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (31237466554 / 1000000000000) (31237472435 / 1000000000000), orderedInterval (-49924021497 / 1000000000000) (-49924015616 / 1000000000000)))) (orderedInterval (21887410061 / 1000000000000) (21887410569 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 2) <| besselDerivativeNearFromState (132830894321763 / 4000000000000) 2 (IntervalRat.scale (309 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (74497943879 / 1000000000000) (74497957261 / 1000000000000), orderedInterval (-117833929792 / 1000000000000) (-117833916410 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 2) <| besselDerivativeNearFromState (356802466359111 / 4000000000000) 2 (IntervalRat.scale (309 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (76098092703 / 1000000000000) (76098100706 / 1000000000000), orderedInterval (-37113784604 / 1000000000000) (-37113776601 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 2) <| besselDerivativeNearFromState (968788104129387 / 4000000000000) 2 (IntervalRat.scale (309 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-45199570086 / 1000000000000) (-45199570085 / 1000000000000), orderedInterval (-24104125596 / 1000000000000) (-24104125595 / 1000000000000)))) (orderedInterval (-8799176805 / 1000000000000) (-8799176670 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 2) <| besselDerivativeNearFromState (713604932718531 / 4000000000000) 2 (IntervalRat.scale (309 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-6863441110 / 1000000000000) (-6863441109 / 1000000000000), orderedInterval (-59321969391 / 1000000000000) (-59321969390 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 2) <| besselDerivativeNearFromState (1222774215219663 / 4000000000000) 2 (IntervalRat.scale (309 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-44951611018 / 1000000000000) (-44951609717 / 1000000000000), orderedInterval (7940698892 / 1000000000000) (7940700193 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 2) <| besselDerivativeNearFromState (900689952593517 / 4000000000000) 2 (IntervalRat.scale (309 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-12501656617 / 1000000000000) (-12501656525 / 1000000000000), orderedInterval (51709174259 / 1000000000000) (51709174351 / 1000000000000)))) (orderedInterval (-4794774238 / 1000000000000) (-4794774048 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate280_chunkChecks2_1 :
    compactCertificate280.chunkChecks (2 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 2) <| besselDerivativeNearFromState (1381890010094691 / 4000000000000) 2 (IntervalRat.scale (309 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (27070622054 / 1000000000000) (27070622055 / 1000000000000), orderedInterval (33276474003 / 1000000000000) (33276474004 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 2) <| besselDerivativeNearFromState (797834569318539 / 4000000000000) 2 (IntervalRat.scale (309 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-41249151814 / 1000000000000) (-41249088565 / 1000000000000), orderedInterval (38707093600 / 1000000000000) (38707156848 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 2) <| besselDerivativeNearFromState (1415771443914951 / 4000000000000) 2 (IntervalRat.scale (309 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (11396544993 / 1000000000000) (11396545052 / 1000000000000), orderedInterval (-40866699842 / 1000000000000) (-40866699782 / 1000000000000)))) (orderedInterval (20789547907 / 1000000000000) (20789556074 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 2) <| besselDerivativeNearFromState (1322797331946819 / 4000000000000) 2 (IntervalRat.scale (309 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-43828532015 / 1000000000000) (-43828531696 / 1000000000000), orderedInterval (2098219864 / 1000000000000) (2098220184 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 2) <| besselDerivativeNearFromState (944010593160627 / 4000000000000) 2 (IntervalRat.scale (309 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-47782251897 / 1000000000000) (-47782251896 / 1000000000000), orderedInterval (-20254684781 / 1000000000000) (-20254684780 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 2) <| besselDerivativeNearFromState (1070407399077333 / 4000000000000) 2 (IntervalRat.scale (309 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-47605635137 / 1000000000000) (-47605635133 / 1000000000000), orderedInterval (-10526180239 / 1000000000000) (-10526180235 / 1000000000000)))) (orderedInterval (6214040382 / 1000000000000) (6214040459 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 2) <| besselDerivativeNearFromState (892394093769477 / 4000000000000) 2 (IntervalRat.scale (309 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-39429337473 / 1000000000000) (-39429337472 / 1000000000000), orderedInterval (-35951377225 / 1000000000000) (-35951377224 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 2) <| besselDerivativeNearFromState (788457245443017 / 4000000000000) 2 (IntervalRat.scale (309 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (1208223986 / 1000000000000) (1208223991 / 1000000000000), orderedInterval (-56820746490 / 1000000000000) (-56820746486 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 2) <| besselDerivativeNearFromState (228525641326683 / 800000000000) 2 (IntervalRat.scale (309 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-24959464847 / 1000000000000) (-24959464846 / 1000000000000), orderedInterval (-40026778472 / 1000000000000) (-40026778471 / 1000000000000)))) (orderedInterval (3235856497 / 1000000000000) (3235856530 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate280_chunkChecks2_2 :
    compactCertificate280.chunkChecks (2 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 2) <| besselDerivativeNearFromState (632113950555201 / 4000000000000) 2 (IntervalRat.scale (309 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (62632537843 / 1000000000000) (62632538307 / 1000000000000), orderedInterval (-10477212729 / 1000000000000) (-10477212266 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 2) <| besselDerivativeNearFromState (535849996355961 / 4000000000000) 2 (IntervalRat.scale (309 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (23088063684 / 1000000000000) (23088064349 / 1000000000000), orderedInterval (-65041470750 / 1000000000000) (-65041470085 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 2) <| besselDerivativeNearFromState (335310047406483 / 4000000000000) 2 (IntervalRat.scale (309 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (18301126012 / 1000000000000) (18301126184 / 1000000000000), orderedInterval (-85312402749 / 1000000000000) (-85312402577 / 1000000000000)))) (orderedInterval (11262180515 / 1000000000000) (11262180658 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 2) <| besselDerivativeNearFromState (180330858686061 / 4000000000000) 2 (IntervalRat.scale (309 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (113082895405 / 1000000000000) (113082896853 / 1000000000000), orderedInterval (-37760243892 / 1000000000000) (-37760242444 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 2) <| besselDerivativeNearFromState (489633360681183 / 4000000000000) 2 (IntervalRat.scale (309 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-44817257591 / 1000000000000) (-44817257590 / 1000000000000), orderedInterval (-56316592048 / 1000000000000) (-56316592047 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 2) <| besselDerivativeNearFromState (668552493966591 / 4000000000000) 2 (IntervalRat.scale (309 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-61000874493 / 1000000000000) (-61000874488 / 1000000000000), orderedInterval (-9188810358 / 1000000000000) (-9188810353 / 1000000000000)))) (orderedInterval (-5944406422 / 1000000000000) (-5944406402 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 2) <| besselDerivativeNearFromState (282689952593517 / 4000000000000) 2 (IntervalRat.scale (309 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (68117748734 / 1000000000000) (68117842490 / 1000000000000), orderedInterval (-66572693603 / 1000000000000) (-66572599848 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 2) <| besselDerivativeNearFromState (1149118962815757 / 4000000000000) 2 (IntervalRat.scale (309 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-38612293654 / 1000000000000) (-38612205838 / 1000000000000), orderedInterval (26995215163 / 1000000000000) (26995302979 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 2) <| besselDerivativeNearFromState (767558212318563 / 4000000000000) 2 (IntervalRat.scale (309 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-49590113507 / 1000000000000) (-49590113506 / 1000000000000), orderedInterval (-29170131036 / 1000000000000) (-29170131035 / 1000000000000)))) (orderedInterval (-25322102779 / 1000000000000) (-25322077768 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate280_chunkChecks2 :
    compactCertificate280.chunkChecks (2 : Fin 5) 0 9 = true :=
  compactCertificate280.chunkChecks_nine_of_three (2 : Fin 5) compactCertificate280_chunkChecks2_0
    compactCertificate280_chunkChecks2_1 compactCertificate280_chunkChecks2_2

theorem compactCertificate280_chunkChecks3_0 :
    compactCertificate280.chunkChecks (3 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 3) <| besselDerivativeNearFromState (309 / 2) 3 (IntervalRat.scale (309 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-62583849473 / 1000000000000) (-62583849471 / 1000000000000), orderedInterval (-14071871475 / 1000000000000) (-14071871473 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 3) <| besselDerivativeNearFromState (455216002901409 / 4000000000000) 3 (IntervalRat.scale (309 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (74554496443 / 1000000000000) (74554496454 / 1000000000000), orderedInterval (5636965842 / 1000000000000) (5636965853 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 3) <| besselDerivativeNearFromState (147207502335297 / 800000000000) 3 (IntervalRat.scale (309 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (31237466554 / 1000000000000) (31237472435 / 1000000000000), orderedInterval (-49924021497 / 1000000000000) (-49924015616 / 1000000000000)))) (orderedInterval (10363845835 / 1000000000000) (10363846439 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 3) <| besselDerivativeNearFromState (132830894321763 / 4000000000000) 3 (IntervalRat.scale (309 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (74497943879 / 1000000000000) (74497957261 / 1000000000000), orderedInterval (-117833929792 / 1000000000000) (-117833916410 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 3) <| besselDerivativeNearFromState (356802466359111 / 4000000000000) 3 (IntervalRat.scale (309 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (76098092703 / 1000000000000) (76098100706 / 1000000000000), orderedInterval (-37113784604 / 1000000000000) (-37113776601 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 3) <| besselDerivativeNearFromState (968788104129387 / 4000000000000) 3 (IntervalRat.scale (309 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-45199570086 / 1000000000000) (-45199570085 / 1000000000000), orderedInterval (-24104125596 / 1000000000000) (-24104125595 / 1000000000000)))) (orderedInterval (-6295999180 / 1000000000000) (-6295999077 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 3) <| besselDerivativeNearFromState (713604932718531 / 4000000000000) 3 (IntervalRat.scale (309 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-6863441110 / 1000000000000) (-6863441109 / 1000000000000), orderedInterval (-59321969391 / 1000000000000) (-59321969390 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 3) <| besselDerivativeNearFromState (1222774215219663 / 4000000000000) 3 (IntervalRat.scale (309 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-44951611018 / 1000000000000) (-44951609717 / 1000000000000), orderedInterval (7940698892 / 1000000000000) (7940700193 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 3) <| besselDerivativeNearFromState (900689952593517 / 4000000000000) 3 (IntervalRat.scale (309 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-12501656617 / 1000000000000) (-12501656525 / 1000000000000), orderedInterval (51709174259 / 1000000000000) (51709174351 / 1000000000000)))) (orderedInterval (-1940492925 / 1000000000000) (-1940492557 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate280_chunkChecks3_1 :
    compactCertificate280.chunkChecks (3 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 3) <| besselDerivativeNearFromState (1381890010094691 / 4000000000000) 3 (IntervalRat.scale (309 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (27070622054 / 1000000000000) (27070622055 / 1000000000000), orderedInterval (33276474003 / 1000000000000) (33276474004 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 3) <| besselDerivativeNearFromState (797834569318539 / 4000000000000) 3 (IntervalRat.scale (309 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-41249151814 / 1000000000000) (-41249088565 / 1000000000000), orderedInterval (38707093600 / 1000000000000) (38707156848 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 3) <| besselDerivativeNearFromState (1415771443914951 / 4000000000000) 3 (IntervalRat.scale (309 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (11396544993 / 1000000000000) (11396545052 / 1000000000000), orderedInterval (-40866699842 / 1000000000000) (-40866699782 / 1000000000000)))) (orderedInterval (129648318527 / 1000000000000) (129648329362 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 3) <| besselDerivativeNearFromState (1322797331946819 / 4000000000000) 3 (IntervalRat.scale (309 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-43828532015 / 1000000000000) (-43828531696 / 1000000000000), orderedInterval (2098219864 / 1000000000000) (2098220184 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 3) <| besselDerivativeNearFromState (944010593160627 / 4000000000000) 3 (IntervalRat.scale (309 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-47782251897 / 1000000000000) (-47782251896 / 1000000000000), orderedInterval (-20254684781 / 1000000000000) (-20254684780 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 3) <| besselDerivativeNearFromState (1070407399077333 / 4000000000000) 3 (IntervalRat.scale (309 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-47605635137 / 1000000000000) (-47605635133 / 1000000000000), orderedInterval (-10526180239 / 1000000000000) (-10526180235 / 1000000000000)))) (orderedInterval (6881037755 / 1000000000000) (6881037897 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 3) <| besselDerivativeNearFromState (892394093769477 / 4000000000000) 3 (IntervalRat.scale (309 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-39429337473 / 1000000000000) (-39429337472 / 1000000000000), orderedInterval (-35951377225 / 1000000000000) (-35951377224 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 3) <| besselDerivativeNearFromState (788457245443017 / 4000000000000) 3 (IntervalRat.scale (309 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (1208223986 / 1000000000000) (1208223991 / 1000000000000), orderedInterval (-56820746490 / 1000000000000) (-56820746486 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 3) <| besselDerivativeNearFromState (228525641326683 / 800000000000) 3 (IntervalRat.scale (309 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-24959464847 / 1000000000000) (-24959464846 / 1000000000000), orderedInterval (-40026778472 / 1000000000000) (-40026778471 / 1000000000000)))) (orderedInterval (953978234 / 1000000000000) (953978284 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate280_chunkChecks3_2 :
    compactCertificate280.chunkChecks (3 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 3) <| besselDerivativeNearFromState (632113950555201 / 4000000000000) 3 (IntervalRat.scale (309 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (62632537843 / 1000000000000) (62632538307 / 1000000000000), orderedInterval (-10477212729 / 1000000000000) (-10477212266 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 3) <| besselDerivativeNearFromState (535849996355961 / 4000000000000) 3 (IntervalRat.scale (309 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (23088063684 / 1000000000000) (23088064349 / 1000000000000), orderedInterval (-65041470750 / 1000000000000) (-65041470085 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 3) <| besselDerivativeNearFromState (335310047406483 / 4000000000000) 3 (IntervalRat.scale (309 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (18301126012 / 1000000000000) (18301126184 / 1000000000000), orderedInterval (-85312402749 / 1000000000000) (-85312402577 / 1000000000000)))) (orderedInterval (-3821556934 / 1000000000000) (-3821556795 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 3) <| besselDerivativeNearFromState (180330858686061 / 4000000000000) 3 (IntervalRat.scale (309 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (113082895405 / 1000000000000) (113082896853 / 1000000000000), orderedInterval (-37760243892 / 1000000000000) (-37760242444 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 3) <| besselDerivativeNearFromState (489633360681183 / 4000000000000) 3 (IntervalRat.scale (309 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-44817257591 / 1000000000000) (-44817257590 / 1000000000000), orderedInterval (-56316592048 / 1000000000000) (-56316592047 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 3) <| besselDerivativeNearFromState (668552493966591 / 4000000000000) 3 (IntervalRat.scale (309 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-61000874493 / 1000000000000) (-61000874488 / 1000000000000), orderedInterval (-9188810358 / 1000000000000) (-9188810353 / 1000000000000)))) (orderedInterval (-1505739491 / 1000000000000) (-1505739472 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 3) <| besselDerivativeNearFromState (282689952593517 / 4000000000000) 3 (IntervalRat.scale (309 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (68117748734 / 1000000000000) (68117842490 / 1000000000000), orderedInterval (-66572693603 / 1000000000000) (-66572599848 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 3) <| besselDerivativeNearFromState (1149118962815757 / 4000000000000) 3 (IntervalRat.scale (309 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-38612293654 / 1000000000000) (-38612205838 / 1000000000000), orderedInterval (26995215163 / 1000000000000) (26995302979 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 3) <| besselDerivativeNearFromState (767558212318563 / 4000000000000) 3 (IntervalRat.scale (309 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-49590113507 / 1000000000000) (-49590113506 / 1000000000000), orderedInterval (-29170131036 / 1000000000000) (-29170131035 / 1000000000000)))) (orderedInterval (3843633040 / 1000000000000) (3843679347 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate280_chunkChecks3 :
    compactCertificate280.chunkChecks (3 : Fin 5) 0 9 = true :=
  compactCertificate280.chunkChecks_nine_of_three (3 : Fin 5) compactCertificate280_chunkChecks3_0
    compactCertificate280_chunkChecks3_1 compactCertificate280_chunkChecks3_2

theorem compactCertificate280_chunkChecks4_0 :
    compactCertificate280.chunkChecks (4 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 4) <| besselDerivativeNearFromState (309 / 2) 4 (IntervalRat.scale (309 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-62583849473 / 1000000000000) (-62583849471 / 1000000000000), orderedInterval (-14071871475 / 1000000000000) (-14071871473 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 4) <| besselDerivativeNearFromState (455216002901409 / 4000000000000) 4 (IntervalRat.scale (309 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (74554496443 / 1000000000000) (74554496454 / 1000000000000), orderedInterval (5636965842 / 1000000000000) (5636965853 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 4) <| besselDerivativeNearFromState (147207502335297 / 800000000000) 4 (IntervalRat.scale (309 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (31237466554 / 1000000000000) (31237472435 / 1000000000000), orderedInterval (-49924021497 / 1000000000000) (-49924015616 / 1000000000000)))) (orderedInterval (-21046527996 / 1000000000000) (-21046527273 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 4) <| besselDerivativeNearFromState (132830894321763 / 4000000000000) 4 (IntervalRat.scale (309 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (74497943879 / 1000000000000) (74497957261 / 1000000000000), orderedInterval (-117833929792 / 1000000000000) (-117833916410 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 4) <| besselDerivativeNearFromState (356802466359111 / 4000000000000) 4 (IntervalRat.scale (309 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (76098092703 / 1000000000000) (76098100706 / 1000000000000), orderedInterval (-37113784604 / 1000000000000) (-37113776601 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 4) <| besselDerivativeNearFromState (968788104129387 / 4000000000000) 4 (IntervalRat.scale (309 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-45199570086 / 1000000000000) (-45199570085 / 1000000000000), orderedInterval (-24104125596 / 1000000000000) (-24104125595 / 1000000000000)))) (orderedInterval (19792602491 / 1000000000000) (19792602593 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 4) <| besselDerivativeNearFromState (713604932718531 / 4000000000000) 4 (IntervalRat.scale (309 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-6863441110 / 1000000000000) (-6863441109 / 1000000000000), orderedInterval (-59321969391 / 1000000000000) (-59321969390 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 4) <| besselDerivativeNearFromState (1222774215219663 / 4000000000000) 4 (IntervalRat.scale (309 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-44951611018 / 1000000000000) (-44951609717 / 1000000000000), orderedInterval (7940698892 / 1000000000000) (7940700193 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 4) <| besselDerivativeNearFromState (900689952593517 / 4000000000000) 4 (IntervalRat.scale (309 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-12501656617 / 1000000000000) (-12501656525 / 1000000000000), orderedInterval (51709174259 / 1000000000000) (51709174351 / 1000000000000)))) (orderedInterval (19911152334 / 1000000000000) (19911153054 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate280_chunkChecks4_1 :
    compactCertificate280.chunkChecks (4 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 4) <| besselDerivativeNearFromState (1381890010094691 / 4000000000000) 4 (IntervalRat.scale (309 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (27070622054 / 1000000000000) (27070622055 / 1000000000000), orderedInterval (33276474003 / 1000000000000) (33276474004 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 4) <| besselDerivativeNearFromState (797834569318539 / 4000000000000) 4 (IntervalRat.scale (309 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-41249151814 / 1000000000000) (-41249088565 / 1000000000000), orderedInterval (38707093600 / 1000000000000) (38707156848 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 4) <| besselDerivativeNearFromState (1415771443914951 / 4000000000000) 4 (IntervalRat.scale (309 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (11396544993 / 1000000000000) (11396545052 / 1000000000000), orderedInterval (-40866699842 / 1000000000000) (-40866699782 / 1000000000000)))) (orderedInterval (-85797198999 / 1000000000000) (-85797184291 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 4) <| besselDerivativeNearFromState (1322797331946819 / 4000000000000) 4 (IntervalRat.scale (309 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-43828532015 / 1000000000000) (-43828531696 / 1000000000000), orderedInterval (2098219864 / 1000000000000) (2098220184 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 4) <| besselDerivativeNearFromState (944010593160627 / 4000000000000) 4 (IntervalRat.scale (309 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-47782251897 / 1000000000000) (-47782251896 / 1000000000000), orderedInterval (-20254684781 / 1000000000000) (-20254684780 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 4) <| besselDerivativeNearFromState (1070407399077333 / 4000000000000) 4 (IntervalRat.scale (309 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-47605635137 / 1000000000000) (-47605635133 / 1000000000000), orderedInterval (-10526180239 / 1000000000000) (-10526180235 / 1000000000000)))) (orderedInterval (-5912532681 / 1000000000000) (-5912532413 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 4) <| besselDerivativeNearFromState (892394093769477 / 4000000000000) 4 (IntervalRat.scale (309 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-39429337473 / 1000000000000) (-39429337472 / 1000000000000), orderedInterval (-35951377225 / 1000000000000) (-35951377224 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 4) <| besselDerivativeNearFromState (788457245443017 / 4000000000000) 4 (IntervalRat.scale (309 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (1208223986 / 1000000000000) (1208223991 / 1000000000000), orderedInterval (-56820746490 / 1000000000000) (-56820746486 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 4) <| besselDerivativeNearFromState (228525641326683 / 800000000000) 4 (IntervalRat.scale (309 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-24959464847 / 1000000000000) (-24959464846 / 1000000000000), orderedInterval (-40026778472 / 1000000000000) (-40026778471 / 1000000000000)))) (orderedInterval (-9643112771 / 1000000000000) (-9643112691 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate280_chunkChecks4_2 :
    compactCertificate280.chunkChecks (4 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 4) <| besselDerivativeNearFromState (632113950555201 / 4000000000000) 4 (IntervalRat.scale (309 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (62632537843 / 1000000000000) (62632538307 / 1000000000000), orderedInterval (-10477212729 / 1000000000000) (-10477212266 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 4) <| besselDerivativeNearFromState (535849996355961 / 4000000000000) 4 (IntervalRat.scale (309 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (23088063684 / 1000000000000) (23088064349 / 1000000000000), orderedInterval (-65041470750 / 1000000000000) (-65041470085 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 4) <| besselDerivativeNearFromState (335310047406483 / 4000000000000) 4 (IntervalRat.scale (309 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (18301126012 / 1000000000000) (18301126184 / 1000000000000), orderedInterval (-85312402749 / 1000000000000) (-85312402577 / 1000000000000)))) (orderedInterval (-11598183890 / 1000000000000) (-11598183752 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 4) <| besselDerivativeNearFromState (180330858686061 / 4000000000000) 4 (IntervalRat.scale (309 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (113082895405 / 1000000000000) (113082896853 / 1000000000000), orderedInterval (-37760243892 / 1000000000000) (-37760242444 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 4) <| besselDerivativeNearFromState (489633360681183 / 4000000000000) 4 (IntervalRat.scale (309 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-44817257591 / 1000000000000) (-44817257590 / 1000000000000), orderedInterval (-56316592048 / 1000000000000) (-56316592047 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 4) <| besselDerivativeNearFromState (668552493966591 / 4000000000000) 4 (IntervalRat.scale (309 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-61000874493 / 1000000000000) (-61000874488 / 1000000000000), orderedInterval (-9188810358 / 1000000000000) (-9188810353 / 1000000000000)))) (orderedInterval (6807589494 / 1000000000000) (6807589514 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 4) <| besselDerivativeNearFromState (282689952593517 / 4000000000000) 4 (IntervalRat.scale (309 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (68117748734 / 1000000000000) (68117842490 / 1000000000000), orderedInterval (-66572693603 / 1000000000000) (-66572599848 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 4) <| besselDerivativeNearFromState (1149118962815757 / 4000000000000) 4 (IntervalRat.scale (309 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-38612293654 / 1000000000000) (-38612205838 / 1000000000000), orderedInterval (26995215163 / 1000000000000) (26995302979 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 4) <| besselDerivativeNearFromState (767558212318563 / 4000000000000) 4 (IntervalRat.scale (309 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-49590113507 / 1000000000000) (-49590113506 / 1000000000000), orderedInterval (-29170131036 / 1000000000000) (-29170131035 / 1000000000000)))) (orderedInterval (59679340650 / 1000000000000) (59679426939 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate280_chunkChecks4 :
    compactCertificate280.chunkChecks (4 : Fin 5) 0 9 = true :=
  compactCertificate280.chunkChecks_nine_of_three (4 : Fin 5) compactCertificate280_chunkChecks4_0
    compactCertificate280_chunkChecks4_1 compactCertificate280_chunkChecks4_2

theorem compactCertificate280_chunks :
    ∀ r : Fin 5, ∀ b, compactCertificate280.chunkCheck r b = true :=
  compactCertificate280.chunkChecks_all (by
    intro r
    fin_cases r
    · exact compactCertificate280_chunkChecks0
    · exact compactCertificate280_chunkChecks1
    · exact compactCertificate280_chunkChecks2
    · exact compactCertificate280_chunkChecks3
    · exact compactCertificate280_chunkChecks4)

theorem compactCertificate280_coefficient0 :
    compactCertificate280.coefficientCheck (0 : Fin 5) = true := by
  norm_num [CompactCertificate.coefficientCheck, intervalFinSumHull,
    compactCertificate280, rationalIntervalSubset, orderedInterval, Fin.sum_univ_succ]

theorem compactCertificate280_coefficient1 :
    compactCertificate280.coefficientCheck (1 : Fin 5) = true := by
  norm_num [CompactCertificate.coefficientCheck, intervalFinSumHull,
    compactCertificate280, rationalIntervalSubset, orderedInterval, Fin.sum_univ_succ]

theorem compactCertificate280_coefficient2 :
    compactCertificate280.coefficientCheck (2 : Fin 5) = true := by
  norm_num [CompactCertificate.coefficientCheck, intervalFinSumHull,
    compactCertificate280, rationalIntervalSubset, orderedInterval, Fin.sum_univ_succ]

theorem compactCertificate280_coefficient3 :
    compactCertificate280.coefficientCheck (3 : Fin 5) = true := by
  norm_num [CompactCertificate.coefficientCheck, intervalFinSumHull,
    compactCertificate280, rationalIntervalSubset, orderedInterval, Fin.sum_univ_succ]

theorem compactCertificate280_coefficient4 :
    compactCertificate280.coefficientCheck (4 : Fin 5) = true := by
  norm_num [CompactCertificate.coefficientCheck, intervalFinSumHull,
    compactCertificate280, rationalIntervalSubset, orderedInterval, Fin.sum_univ_succ]

theorem compactCertificate280_coefficients : ∀ r : Fin 5,
    compactCertificate280.coefficientCheck r = true := by
  intro r
  fin_cases r
  · exact compactCertificate280_coefficient0
  · exact compactCertificate280_coefficient1
  · exact compactCertificate280_coefficient2
  · exact compactCertificate280_coefficient3
  · exact compactCertificate280_coefficient4

theorem compactCertificate280_lower : (1 : ℚ) ≤ compactCertificate280.output.lo := by
  norm_num [CompactCertificate.output, CompactCertificate.interval,
    CompactCertificate.coefficientTargetNat, compactCertificate280, dualConstant,
    intervalTaylorSum, intervalPow, intervalSub, intervalMaxAbs, widenInterval,
    rationalErrorInterval, orderedInterval, IntervalRat.add, IntervalRat.mul, IntervalRat.scale,
    IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4]

theorem compactCertificate280_proves {t : ℝ} (ht : t ∈ compactCertificate280.interval) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t :=
  compactCertificate280.proves compactCertificate280_states compactCertificate280_chunks
    compactCertificate280_coefficients compactCertificate280_lower ht

end Erdos232
