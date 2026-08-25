/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, OpenAI Codex
-/
import ErdosProblems.Erdos232.CompactBase

open LeanCert.Core
namespace Erdos232

def compactCertificate239 : CompactCertificate where
  left := 116
  right := 233 / 2
  center := 465 / 4
  grid := fun i =>
    match i.val with
    | 0 => 37
    | 1 => 27
    | 2 => 44
    | 3 => 8
    | 4 => 21
    | 5 => 58
    | 6 => 43
    | 7 => 73
    | 8 => 54
    | 9 => 83
    | 10 => 48
    | 11 => 85
    | 12 => 79
    | 13 => 57
    | 14 => 64
    | 15 => 53
    | 16 => 47
    | 17 => 68
    | 18 => 38
    | 19 => 32
    | 20 => 20
    | 21 => 11
    | 22 => 29
    | 23 => 40
    | 24 => 17
    | 25 => 69
    | _ => 46
  point := fun i =>
    match i.val with
    | 0 => 465 / 4
    | 1 => 137006758154793 / 1600000000000
    | 2 => 44305170605769 / 320000000000
    | 3 => 39978230329851 / 1600000000000
    | 4 => 107387150069247 / 1600000000000
    | 5 => 291577002213699 / 1600000000000
    | 6 => 214774300138587 / 1600000000000
    | 7 => 368019423998151 / 1600000000000
    | 8 => 271081442042709 / 1600000000000
    | 9 => 415908643814907 / 1600000000000
    | 10 => 240124967464803 / 1600000000000
    | 11 => 426105968556927 / 1600000000000
    | 12 => 398123468838363 / 1600000000000
    | 13 => 284119693087179 / 1600000000000
    | 14 => 322161450207741 / 1600000000000
    | 15 => 268584630163629 / 1600000000000
    | 16 => 237302666104209 / 1600000000000
    | 17 => 68779561952691 / 320000000000
    | 18 => 190247888031177 / 1600000000000
    | 19 => 161275241621697 / 1600000000000
    | 20 => 100918557957291 / 1600000000000
    | 21 => 54274336109397 / 1600000000000
    | 22 => 147365380399191 / 1600000000000
    | 23 => 201214828281207 / 1600000000000
    | 24 => 85081442042709 / 1600000000000
    | 25 => 345851338323189 / 1600000000000
    | _ => 231012665843451 / 1600000000000
  state := fun i =>
    match i.val with
    | 0 => (orderedInterval (-52847558103 / 1000000000000) (-52847558102 / 1000000000000), orderedInterval (-51574572608 / 1000000000000) (-51574572607 / 1000000000000))
    | 1 => (orderedInterval (-86207276754 / 1000000000000) (-86207276715 / 1000000000000), orderedInterval (2172943867 / 1000000000000) (2172943906 / 1000000000000))
    | 2 => (orderedInterval (57353231884 / 1000000000000) (57353231885 / 1000000000000), orderedInterval (35968357641 / 1000000000000) (35968357642 / 1000000000000))
    | 3 => (orderedInterval (94551938497 / 1000000000000) (94551938498 / 1000000000000), orderedInterval (126717027110 / 1000000000000) (126717027111 / 1000000000000))
    | 4 => (orderedInterval (-91275312003 / 1000000000000) (-91275309331 / 1000000000000), orderedInterval (34648254236 / 1000000000000) (34648256908 / 1000000000000))
    | 5 => (orderedInterval (42725802324 / 1000000000000) (42725802325 / 1000000000000), orderedInterval (40722624013 / 1000000000000) (40722624014 / 1000000000000))
    | 6 => (orderedInterval (4822176235 / 1000000000000) (4822176250 / 1000000000000), orderedInterval (-68715802504 / 1000000000000) (-68715802489 / 1000000000000))
    | 7 => (orderedInterval (-52291155360 / 1000000000000) (-52291155343 / 1000000000000), orderedInterval (-5665140938 / 1000000000000) (-5665140921 / 1000000000000))
    | 8 => (orderedInterval (32797271477 / 1000000000000) (32797271478 / 1000000000000), orderedInterval (51689864881 / 1000000000000) (51689864882 / 1000000000000))
    | 9 => (orderedInterval (1205933607 / 1000000000000) (1205933610 / 1000000000000), orderedInterval (-49475804094 / 1000000000000) (-49475804091 / 1000000000000))
    | 10 => (orderedInterval (4309915798 / 1000000000000) (4309915800 / 1000000000000), orderedInterval (64973109392 / 1000000000000) (64973109394 / 1000000000000))
    | 11 => (orderedInterval (-3213994823 / 1000000000000) (-3213994822 / 1000000000000), orderedInterval (-48780643926 / 1000000000000) (-48780643925 / 1000000000000))
    | 12 => (orderedInterval (-50053848424 / 1000000000000) (-50053848413 / 1000000000000), orderedInterval (-7185645812 / 1000000000000) (-7185645801 / 1000000000000))
    | 13 => (orderedInterval (39086838517 / 1000000000000) (39086865267 / 1000000000000), orderedInterval (-45467531656 / 1000000000000) (-45467504906 / 1000000000000))
    | 14 => (orderedInterval (49425358118 / 1000000000000) (49425358119 / 1000000000000), orderedInterval (26689044179 / 1000000000000) (26689044180 / 1000000000000))
    | 15 => (orderedInterval (-51685064646 / 1000000000000) (-51685026047 / 1000000000000), orderedInterval (33636625504 / 1000000000000) (33636664103 / 1000000000000))
    | 16 => (orderedInterval (-64988962415 / 1000000000000) (-64988962409 / 1000000000000), orderedInterval (-8074551759 / 1000000000000) (-8074551752 / 1000000000000))
    | 17 => (orderedInterval (47179422537 / 1000000000000) (47179452125 / 1000000000000), orderedInterval (-27239061504 / 1000000000000) (-27239031917 / 1000000000000))
    | 18 => (orderedInterval (22234711161 / 1000000000000) (22234711162 / 1000000000000), orderedInterval (69617905769 / 1000000000000) (69617905770 / 1000000000000))
    | 19 => (orderedInterval (68944428036 / 1000000000000) (68944428037 / 1000000000000), orderedInterval (39186296606 / 1000000000000) (39186296607 / 1000000000000))
    | 20 => (orderedInterval (85901981656 / 1000000000000) (85901981657 / 1000000000000), orderedInterval (51414258718 / 1000000000000) (51414258719 / 1000000000000))
    | 21 => (orderedInterval (-19882457655 / 1000000000000) (-19882457654 / 1000000000000), orderedInterval (-135258101679 / 1000000000000) (-135258101678 / 1000000000000))
    | 22 => (orderedInterval (-81304153879 / 1000000000000) (-81304153320 / 1000000000000), orderedInterval (17806731633 / 1000000000000) (17806732192 / 1000000000000))
    | 23 => (orderedInterval (54835691094 / 1000000000000) (54835691095 / 1000000000000), orderedInterval (45116839790 / 1000000000000) (45116839791 / 1000000000000))
    | 24 => (orderedInterval (-57364028746 / 1000000000000) (-57364028745 / 1000000000000), orderedInterval (-92635592133 / 1000000000000) (-92635592132 / 1000000000000))
    | 25 => (orderedInterval (-9289082350 / 1000000000000) (-9289082349 / 1000000000000), orderedInterval (-53447123139 / 1000000000000) (-53447123138 / 1000000000000))
    | _ => (orderedInterval (40406512381 / 1000000000000) (40406512382 / 1000000000000), orderedInterval (52553208178 / 1000000000000) (52553208179 / 1000000000000))
  chunkTarget := fun r b =>
    match r.val with
    | 0 =>
      match b.val with
      | 0 => orderedInterval (-18384653550 / 1000000000000) (-18384653540 / 1000000000000)
      | 1 => orderedInterval (-7395804459 / 1000000000000) (-7395804347 / 1000000000000)
      | 2 => orderedInterval (2405513787 / 1000000000000) (2405513795 / 1000000000000)
      | 3 => orderedInterval (-351838872 / 1000000000000) (-351838824 / 1000000000000)
      | 4 => orderedInterval (4349669115 / 1000000000000) (4349671659 / 1000000000000)
      | 5 => orderedInterval (4330239860 / 1000000000000) (4330241075 / 1000000000000)
      | 6 => orderedInterval (-4660851581 / 1000000000000) (-4660851551 / 1000000000000)
      | 7 => orderedInterval (-1990877395 / 1000000000000) (-1990877368 / 1000000000000)
      | _ => orderedInterval (-7170994974 / 1000000000000) (-7170994940 / 1000000000000)
    | 1 =>
      match b.val with
      | 0 => orderedInterval (-17913641379 / 1000000000000) (-17913641368 / 1000000000000)
      | 1 => orderedInterval (-4103292454 / 1000000000000) (-4103292381 / 1000000000000)
      | 2 => orderedInterval (2166410939 / 1000000000000) (2166410952 / 1000000000000)
      | 3 => orderedInterval (9986559622 / 1000000000000) (9986559720 / 1000000000000)
      | 4 => orderedInterval (-6523924531 / 1000000000000) (-6523920644 / 1000000000000)
      | 5 => orderedInterval (-139065395 / 1000000000000) (-139063333 / 1000000000000)
      | 6 => orderedInterval (-12400549460 / 1000000000000) (-12400549432 / 1000000000000)
      | 7 => orderedInterval (-3331830708 / 1000000000000) (-3331830685 / 1000000000000)
      | _ => orderedInterval (-4412323587 / 1000000000000) (-4412323540 / 1000000000000)
    | 2 =>
      match b.val with
      | 0 => orderedInterval (16762891575 / 1000000000000) (16762891587 / 1000000000000)
      | 1 => orderedInterval (8657657044 / 1000000000000) (8657657100 / 1000000000000)
      | 2 => orderedInterval (-8016433685 / 1000000000000) (-8016433662 / 1000000000000)
      | 3 => orderedInterval (2851113216 / 1000000000000) (2851113425 / 1000000000000)
      | 4 => orderedInterval (-11957888627 / 1000000000000) (-11957882653 / 1000000000000)
      | 5 => orderedInterval (-8937409888 / 1000000000000) (-8937406326 / 1000000000000)
      | 6 => orderedInterval (5936568685 / 1000000000000) (5936568712 / 1000000000000)
      | 7 => orderedInterval (3757754848 / 1000000000000) (3757754869 / 1000000000000)
      | _ => orderedInterval (9190746140 / 1000000000000) (9190746208 / 1000000000000)
    | 3 =>
      match b.val with
      | 0 => orderedInterval (16722968534 / 1000000000000) (16722968548 / 1000000000000)
      | 1 => orderedInterval (10847674505 / 1000000000000) (10847674558 / 1000000000000)
      | 2 => orderedInterval (-5151663829 / 1000000000000) (-5151663787 / 1000000000000)
      | 3 => orderedInterval (-25297814848 / 1000000000000) (-25297814391 / 1000000000000)
      | 4 => orderedInterval (14856573979 / 1000000000000) (14856583111 / 1000000000000)
      | 5 => orderedInterval (2355814015 / 1000000000000) (2355820214 / 1000000000000)
      | 6 => orderedInterval (13038072941 / 1000000000000) (13038072967 / 1000000000000)
      | 7 => orderedInterval (4483815678 / 1000000000000) (4483815698 / 1000000000000)
      | _ => orderedInterval (-9104327628 / 1000000000000) (-9104327523 / 1000000000000)
    | _ =>
      match b.val with
      | 0 => orderedInterval (-14698080328 / 1000000000000) (-14698080313 / 1000000000000)
      | 1 => orderedInterval (-18900934835 / 1000000000000) (-18900934772 / 1000000000000)
      | 2 => orderedInterval (28383229655 / 1000000000000) (28383229732 / 1000000000000)
      | 3 => orderedInterval (-16618825270 / 1000000000000) (-16618824256 / 1000000000000)
      | 4 => orderedInterval (36583411990 / 1000000000000) (36583426031 / 1000000000000)
      | 5 => orderedInterval (21333930584 / 1000000000000) (21333941540 / 1000000000000)
      | 6 => orderedInterval (-6078375473 / 1000000000000) (-6078375447 / 1000000000000)
      | 7 => orderedInterval (-5103127216 / 1000000000000) (-5103127197 / 1000000000000)
      | _ => orderedInterval (-8859001435 / 1000000000000) (-8859001267 / 1000000000000)
  coefficientTarget := fun i =>
    match i.val with
    | 0 => orderedInterval (-28869598069 / 1000000000000) (-28869594041 / 1000000000000)
    | 1 => orderedInterval (-36671656953 / 1000000000000) (-36671650711 / 1000000000000)
    | 2 => orderedInterval (18244999308 / 1000000000000) (18245009260 / 1000000000000)
    | 3 => orderedInterval (22751113347 / 1000000000000) (22751129395 / 1000000000000)
    | _ => orderedInterval (16042227672 / 1000000000000) (16042254051 / 1000000000000)

theorem compactCertificate239_stateChecks0 :
    compactCertificate239.stateChecks 0 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 37 12 (465 / 4)) (orderedInterval (-52847558103 / 1000000000000) (-52847558102 / 1000000000000), orderedInterval (-51574572608 / 1000000000000) (-51574572607 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 27 12 (137006758154793 / 1600000000000)) (orderedInterval (-86207276754 / 1000000000000) (-86207276715 / 1000000000000), orderedInterval (2172943867 / 1000000000000) (2172943906 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 44 12 (44305170605769 / 320000000000)) (orderedInterval (57353231884 / 1000000000000) (57353231885 / 1000000000000), orderedInterval (35968357641 / 1000000000000) (35968357642 / 1000000000000))) = true
  norm_num [besselStateAtRationalPoint, besselIntervalStepZero,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, besselZeroTransition,
    besselInitial, besselGridStateAt, besselGridStateBlock00, besselGridStateBlock01,
    besselGridStateBlock02, besselGridStateBlock03, besselGridStateBlock04,
    besselGridStateBlock05, besselGridStateBlock06, besselGridStateBlock07,
    besselGridStateBlock08, besselGridStateBlock09, besselGridStateBlock10,
    besselGridStateBlock11, besselGridStateBlock12, besselGridStateBlock13,
    besselGridStateBlock14, besselGridState008, besselGridState011, besselGridState017, besselGridState020, besselGridState021, besselGridState027, besselGridState029, besselGridState032, besselGridState037, besselGridState038, besselGridState040, besselGridState043, besselGridState044, besselGridState046, besselGridState047, besselGridState048, besselGridState053, besselGridState054, besselGridState057, besselGridState058, besselGridState064, besselGridState068, besselGridState069, besselGridState073, besselGridState079, besselGridState083, besselGridState085, besselStateSubset, linearInterval, widenInterval,
    rationalErrorInterval, rationalIntervalSubset, orderedInterval, Finset.sum_range_succ,
    IntervalRat.add, IntervalRat.mul, IntervalRat.scale, IntervalRat.singleton]

theorem compactCertificate239_stateChecks1 :
    compactCertificate239.stateChecks 3 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 8 12 (39978230329851 / 1600000000000)) (orderedInterval (94551938497 / 1000000000000) (94551938498 / 1000000000000), orderedInterval (126717027110 / 1000000000000) (126717027111 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 21 12 (107387150069247 / 1600000000000)) (orderedInterval (-91275312003 / 1000000000000) (-91275309331 / 1000000000000), orderedInterval (34648254236 / 1000000000000) (34648256908 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 58 12 (291577002213699 / 1600000000000)) (orderedInterval (42725802324 / 1000000000000) (42725802325 / 1000000000000), orderedInterval (40722624013 / 1000000000000) (40722624014 / 1000000000000))) = true
  norm_num [besselStateAtRationalPoint, besselIntervalStepZero,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, besselZeroTransition,
    besselInitial, besselGridStateAt, besselGridStateBlock00, besselGridStateBlock01,
    besselGridStateBlock02, besselGridStateBlock03, besselGridStateBlock04,
    besselGridStateBlock05, besselGridStateBlock06, besselGridStateBlock07,
    besselGridStateBlock08, besselGridStateBlock09, besselGridStateBlock10,
    besselGridStateBlock11, besselGridStateBlock12, besselGridStateBlock13,
    besselGridStateBlock14, besselGridState008, besselGridState011, besselGridState017, besselGridState020, besselGridState021, besselGridState027, besselGridState029, besselGridState032, besselGridState037, besselGridState038, besselGridState040, besselGridState043, besselGridState044, besselGridState046, besselGridState047, besselGridState048, besselGridState053, besselGridState054, besselGridState057, besselGridState058, besselGridState064, besselGridState068, besselGridState069, besselGridState073, besselGridState079, besselGridState083, besselGridState085, besselStateSubset, linearInterval, widenInterval,
    rationalErrorInterval, rationalIntervalSubset, orderedInterval, Finset.sum_range_succ,
    IntervalRat.add, IntervalRat.mul, IntervalRat.scale, IntervalRat.singleton]

theorem compactCertificate239_stateChecks2 :
    compactCertificate239.stateChecks 6 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 43 12 (214774300138587 / 1600000000000)) (orderedInterval (4822176235 / 1000000000000) (4822176250 / 1000000000000), orderedInterval (-68715802504 / 1000000000000) (-68715802489 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 73 12 (368019423998151 / 1600000000000)) (orderedInterval (-52291155360 / 1000000000000) (-52291155343 / 1000000000000), orderedInterval (-5665140938 / 1000000000000) (-5665140921 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 54 12 (271081442042709 / 1600000000000)) (orderedInterval (32797271477 / 1000000000000) (32797271478 / 1000000000000), orderedInterval (51689864881 / 1000000000000) (51689864882 / 1000000000000))) = true
  norm_num [besselStateAtRationalPoint, besselIntervalStepZero,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, besselZeroTransition,
    besselInitial, besselGridStateAt, besselGridStateBlock00, besselGridStateBlock01,
    besselGridStateBlock02, besselGridStateBlock03, besselGridStateBlock04,
    besselGridStateBlock05, besselGridStateBlock06, besselGridStateBlock07,
    besselGridStateBlock08, besselGridStateBlock09, besselGridStateBlock10,
    besselGridStateBlock11, besselGridStateBlock12, besselGridStateBlock13,
    besselGridStateBlock14, besselGridState008, besselGridState011, besselGridState017, besselGridState020, besselGridState021, besselGridState027, besselGridState029, besselGridState032, besselGridState037, besselGridState038, besselGridState040, besselGridState043, besselGridState044, besselGridState046, besselGridState047, besselGridState048, besselGridState053, besselGridState054, besselGridState057, besselGridState058, besselGridState064, besselGridState068, besselGridState069, besselGridState073, besselGridState079, besselGridState083, besselGridState085, besselStateSubset, linearInterval, widenInterval,
    rationalErrorInterval, rationalIntervalSubset, orderedInterval, Finset.sum_range_succ,
    IntervalRat.add, IntervalRat.mul, IntervalRat.scale, IntervalRat.singleton]

theorem compactCertificate239_stateChecks3 :
    compactCertificate239.stateChecks 9 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 83 12 (415908643814907 / 1600000000000)) (orderedInterval (1205933607 / 1000000000000) (1205933610 / 1000000000000), orderedInterval (-49475804094 / 1000000000000) (-49475804091 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 48 12 (240124967464803 / 1600000000000)) (orderedInterval (4309915798 / 1000000000000) (4309915800 / 1000000000000), orderedInterval (64973109392 / 1000000000000) (64973109394 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 85 12 (426105968556927 / 1600000000000)) (orderedInterval (-3213994823 / 1000000000000) (-3213994822 / 1000000000000), orderedInterval (-48780643926 / 1000000000000) (-48780643925 / 1000000000000))) = true
  norm_num [besselStateAtRationalPoint, besselIntervalStepZero,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, besselZeroTransition,
    besselInitial, besselGridStateAt, besselGridStateBlock00, besselGridStateBlock01,
    besselGridStateBlock02, besselGridStateBlock03, besselGridStateBlock04,
    besselGridStateBlock05, besselGridStateBlock06, besselGridStateBlock07,
    besselGridStateBlock08, besselGridStateBlock09, besselGridStateBlock10,
    besselGridStateBlock11, besselGridStateBlock12, besselGridStateBlock13,
    besselGridStateBlock14, besselGridState008, besselGridState011, besselGridState017, besselGridState020, besselGridState021, besselGridState027, besselGridState029, besselGridState032, besselGridState037, besselGridState038, besselGridState040, besselGridState043, besselGridState044, besselGridState046, besselGridState047, besselGridState048, besselGridState053, besselGridState054, besselGridState057, besselGridState058, besselGridState064, besselGridState068, besselGridState069, besselGridState073, besselGridState079, besselGridState083, besselGridState085, besselStateSubset, linearInterval, widenInterval,
    rationalErrorInterval, rationalIntervalSubset, orderedInterval, Finset.sum_range_succ,
    IntervalRat.add, IntervalRat.mul, IntervalRat.scale, IntervalRat.singleton]

theorem compactCertificate239_stateChecks4 :
    compactCertificate239.stateChecks 12 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 79 12 (398123468838363 / 1600000000000)) (orderedInterval (-50053848424 / 1000000000000) (-50053848413 / 1000000000000), orderedInterval (-7185645812 / 1000000000000) (-7185645801 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 57 12 (284119693087179 / 1600000000000)) (orderedInterval (39086838517 / 1000000000000) (39086865267 / 1000000000000), orderedInterval (-45467531656 / 1000000000000) (-45467504906 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 64 12 (322161450207741 / 1600000000000)) (orderedInterval (49425358118 / 1000000000000) (49425358119 / 1000000000000), orderedInterval (26689044179 / 1000000000000) (26689044180 / 1000000000000))) = true
  norm_num [besselStateAtRationalPoint, besselIntervalStepZero,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, besselZeroTransition,
    besselInitial, besselGridStateAt, besselGridStateBlock00, besselGridStateBlock01,
    besselGridStateBlock02, besselGridStateBlock03, besselGridStateBlock04,
    besselGridStateBlock05, besselGridStateBlock06, besselGridStateBlock07,
    besselGridStateBlock08, besselGridStateBlock09, besselGridStateBlock10,
    besselGridStateBlock11, besselGridStateBlock12, besselGridStateBlock13,
    besselGridStateBlock14, besselGridState008, besselGridState011, besselGridState017, besselGridState020, besselGridState021, besselGridState027, besselGridState029, besselGridState032, besselGridState037, besselGridState038, besselGridState040, besselGridState043, besselGridState044, besselGridState046, besselGridState047, besselGridState048, besselGridState053, besselGridState054, besselGridState057, besselGridState058, besselGridState064, besselGridState068, besselGridState069, besselGridState073, besselGridState079, besselGridState083, besselGridState085, besselStateSubset, linearInterval, widenInterval,
    rationalErrorInterval, rationalIntervalSubset, orderedInterval, Finset.sum_range_succ,
    IntervalRat.add, IntervalRat.mul, IntervalRat.scale, IntervalRat.singleton]

theorem compactCertificate239_stateChecks5 :
    compactCertificate239.stateChecks 15 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 53 12 (268584630163629 / 1600000000000)) (orderedInterval (-51685064646 / 1000000000000) (-51685026047 / 1000000000000), orderedInterval (33636625504 / 1000000000000) (33636664103 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 47 12 (237302666104209 / 1600000000000)) (orderedInterval (-64988962415 / 1000000000000) (-64988962409 / 1000000000000), orderedInterval (-8074551759 / 1000000000000) (-8074551752 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 68 12 (68779561952691 / 320000000000)) (orderedInterval (47179422537 / 1000000000000) (47179452125 / 1000000000000), orderedInterval (-27239061504 / 1000000000000) (-27239031917 / 1000000000000))) = true
  norm_num [besselStateAtRationalPoint, besselIntervalStepZero,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, besselZeroTransition,
    besselInitial, besselGridStateAt, besselGridStateBlock00, besselGridStateBlock01,
    besselGridStateBlock02, besselGridStateBlock03, besselGridStateBlock04,
    besselGridStateBlock05, besselGridStateBlock06, besselGridStateBlock07,
    besselGridStateBlock08, besselGridStateBlock09, besselGridStateBlock10,
    besselGridStateBlock11, besselGridStateBlock12, besselGridStateBlock13,
    besselGridStateBlock14, besselGridState008, besselGridState011, besselGridState017, besselGridState020, besselGridState021, besselGridState027, besselGridState029, besselGridState032, besselGridState037, besselGridState038, besselGridState040, besselGridState043, besselGridState044, besselGridState046, besselGridState047, besselGridState048, besselGridState053, besselGridState054, besselGridState057, besselGridState058, besselGridState064, besselGridState068, besselGridState069, besselGridState073, besselGridState079, besselGridState083, besselGridState085, besselStateSubset, linearInterval, widenInterval,
    rationalErrorInterval, rationalIntervalSubset, orderedInterval, Finset.sum_range_succ,
    IntervalRat.add, IntervalRat.mul, IntervalRat.scale, IntervalRat.singleton]

theorem compactCertificate239_stateChecks6 :
    compactCertificate239.stateChecks 18 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 38 12 (190247888031177 / 1600000000000)) (orderedInterval (22234711161 / 1000000000000) (22234711162 / 1000000000000), orderedInterval (69617905769 / 1000000000000) (69617905770 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 32 12 (161275241621697 / 1600000000000)) (orderedInterval (68944428036 / 1000000000000) (68944428037 / 1000000000000), orderedInterval (39186296606 / 1000000000000) (39186296607 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 20 12 (100918557957291 / 1600000000000)) (orderedInterval (85901981656 / 1000000000000) (85901981657 / 1000000000000), orderedInterval (51414258718 / 1000000000000) (51414258719 / 1000000000000))) = true
  norm_num [besselStateAtRationalPoint, besselIntervalStepZero,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, besselZeroTransition,
    besselInitial, besselGridStateAt, besselGridStateBlock00, besselGridStateBlock01,
    besselGridStateBlock02, besselGridStateBlock03, besselGridStateBlock04,
    besselGridStateBlock05, besselGridStateBlock06, besselGridStateBlock07,
    besselGridStateBlock08, besselGridStateBlock09, besselGridStateBlock10,
    besselGridStateBlock11, besselGridStateBlock12, besselGridStateBlock13,
    besselGridStateBlock14, besselGridState008, besselGridState011, besselGridState017, besselGridState020, besselGridState021, besselGridState027, besselGridState029, besselGridState032, besselGridState037, besselGridState038, besselGridState040, besselGridState043, besselGridState044, besselGridState046, besselGridState047, besselGridState048, besselGridState053, besselGridState054, besselGridState057, besselGridState058, besselGridState064, besselGridState068, besselGridState069, besselGridState073, besselGridState079, besselGridState083, besselGridState085, besselStateSubset, linearInterval, widenInterval,
    rationalErrorInterval, rationalIntervalSubset, orderedInterval, Finset.sum_range_succ,
    IntervalRat.add, IntervalRat.mul, IntervalRat.scale, IntervalRat.singleton]

theorem compactCertificate239_stateChecks7 :
    compactCertificate239.stateChecks 21 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 11 12 (54274336109397 / 1600000000000)) (orderedInterval (-19882457655 / 1000000000000) (-19882457654 / 1000000000000), orderedInterval (-135258101679 / 1000000000000) (-135258101678 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 29 12 (147365380399191 / 1600000000000)) (orderedInterval (-81304153879 / 1000000000000) (-81304153320 / 1000000000000), orderedInterval (17806731633 / 1000000000000) (17806732192 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 40 12 (201214828281207 / 1600000000000)) (orderedInterval (54835691094 / 1000000000000) (54835691095 / 1000000000000), orderedInterval (45116839790 / 1000000000000) (45116839791 / 1000000000000))) = true
  norm_num [besselStateAtRationalPoint, besselIntervalStepZero,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, besselZeroTransition,
    besselInitial, besselGridStateAt, besselGridStateBlock00, besselGridStateBlock01,
    besselGridStateBlock02, besselGridStateBlock03, besselGridStateBlock04,
    besselGridStateBlock05, besselGridStateBlock06, besselGridStateBlock07,
    besselGridStateBlock08, besselGridStateBlock09, besselGridStateBlock10,
    besselGridStateBlock11, besselGridStateBlock12, besselGridStateBlock13,
    besselGridStateBlock14, besselGridState008, besselGridState011, besselGridState017, besselGridState020, besselGridState021, besselGridState027, besselGridState029, besselGridState032, besselGridState037, besselGridState038, besselGridState040, besselGridState043, besselGridState044, besselGridState046, besselGridState047, besselGridState048, besselGridState053, besselGridState054, besselGridState057, besselGridState058, besselGridState064, besselGridState068, besselGridState069, besselGridState073, besselGridState079, besselGridState083, besselGridState085, besselStateSubset, linearInterval, widenInterval,
    rationalErrorInterval, rationalIntervalSubset, orderedInterval, Finset.sum_range_succ,
    IntervalRat.add, IntervalRat.mul, IntervalRat.scale, IntervalRat.singleton]

theorem compactCertificate239_stateChecks8 :
    compactCertificate239.stateChecks 24 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 17 12 (85081442042709 / 1600000000000)) (orderedInterval (-57364028746 / 1000000000000) (-57364028745 / 1000000000000), orderedInterval (-92635592133 / 1000000000000) (-92635592132 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 69 12 (345851338323189 / 1600000000000)) (orderedInterval (-9289082350 / 1000000000000) (-9289082349 / 1000000000000), orderedInterval (-53447123139 / 1000000000000) (-53447123138 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 46 12 (231012665843451 / 1600000000000)) (orderedInterval (40406512381 / 1000000000000) (40406512382 / 1000000000000), orderedInterval (52553208178 / 1000000000000) (52553208179 / 1000000000000))) = true
  norm_num [besselStateAtRationalPoint, besselIntervalStepZero,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, besselZeroTransition,
    besselInitial, besselGridStateAt, besselGridStateBlock00, besselGridStateBlock01,
    besselGridStateBlock02, besselGridStateBlock03, besselGridStateBlock04,
    besselGridStateBlock05, besselGridStateBlock06, besselGridStateBlock07,
    besselGridStateBlock08, besselGridStateBlock09, besselGridStateBlock10,
    besselGridStateBlock11, besselGridStateBlock12, besselGridStateBlock13,
    besselGridStateBlock14, besselGridState008, besselGridState011, besselGridState017, besselGridState020, besselGridState021, besselGridState027, besselGridState029, besselGridState032, besselGridState037, besselGridState038, besselGridState040, besselGridState043, besselGridState044, besselGridState046, besselGridState047, besselGridState048, besselGridState053, besselGridState054, besselGridState057, besselGridState058, besselGridState064, besselGridState068, besselGridState069, besselGridState073, besselGridState079, besselGridState083, besselGridState085, besselStateSubset, linearInterval, widenInterval,
    rationalErrorInterval, rationalIntervalSubset, orderedInterval, Finset.sum_range_succ,
    IntervalRat.add, IntervalRat.mul, IntervalRat.scale, IntervalRat.singleton]

theorem compactCertificate239_states : ∀ j,
    BesselStateValid (compactCertificate239.point j) (compactCertificate239.state j) :=
  compactCertificate239.statesValid_of_checks3 compactCertificate239_stateChecks0
    compactCertificate239_stateChecks1 compactCertificate239_stateChecks2
    compactCertificate239_stateChecks3 compactCertificate239_stateChecks4
    compactCertificate239_stateChecks5 compactCertificate239_stateChecks6
    compactCertificate239_stateChecks7 compactCertificate239_stateChecks8

theorem compactCertificate239_chunkChecks0_0 :
    compactCertificate239.chunkChecks (0 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 0) <| besselDerivativeNearFromState (465 / 4) 0 (IntervalRat.scale (465 / 4) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-52847558103 / 1000000000000) (-52847558102 / 1000000000000), orderedInterval (-51574572608 / 1000000000000) (-51574572607 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 0) <| besselDerivativeNearFromState (137006758154793 / 1600000000000) 0 (IntervalRat.scale (465 / 4) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-86207276754 / 1000000000000) (-86207276715 / 1000000000000), orderedInterval (2172943867 / 1000000000000) (2172943906 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 0) <| besselDerivativeNearFromState (44305170605769 / 320000000000) 0 (IntervalRat.scale (465 / 4) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (57353231884 / 1000000000000) (57353231885 / 1000000000000), orderedInterval (35968357641 / 1000000000000) (35968357642 / 1000000000000)))) (orderedInterval (-18384653550 / 1000000000000) (-18384653540 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 0) <| besselDerivativeNearFromState (39978230329851 / 1600000000000) 0 (IntervalRat.scale (465 / 4) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (94551938497 / 1000000000000) (94551938498 / 1000000000000), orderedInterval (126717027110 / 1000000000000) (126717027111 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 0) <| besselDerivativeNearFromState (107387150069247 / 1600000000000) 0 (IntervalRat.scale (465 / 4) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-91275312003 / 1000000000000) (-91275309331 / 1000000000000), orderedInterval (34648254236 / 1000000000000) (34648256908 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 0) <| besselDerivativeNearFromState (291577002213699 / 1600000000000) 0 (IntervalRat.scale (465 / 4) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (42725802324 / 1000000000000) (42725802325 / 1000000000000), orderedInterval (40722624013 / 1000000000000) (40722624014 / 1000000000000)))) (orderedInterval (-7395804459 / 1000000000000) (-7395804347 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 0) <| besselDerivativeNearFromState (214774300138587 / 1600000000000) 0 (IntervalRat.scale (465 / 4) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (4822176235 / 1000000000000) (4822176250 / 1000000000000), orderedInterval (-68715802504 / 1000000000000) (-68715802489 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 0) <| besselDerivativeNearFromState (368019423998151 / 1600000000000) 0 (IntervalRat.scale (465 / 4) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-52291155360 / 1000000000000) (-52291155343 / 1000000000000), orderedInterval (-5665140938 / 1000000000000) (-5665140921 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 0) <| besselDerivativeNearFromState (271081442042709 / 1600000000000) 0 (IntervalRat.scale (465 / 4) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (32797271477 / 1000000000000) (32797271478 / 1000000000000), orderedInterval (51689864881 / 1000000000000) (51689864882 / 1000000000000)))) (orderedInterval (2405513787 / 1000000000000) (2405513795 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate239_chunkChecks0_1 :
    compactCertificate239.chunkChecks (0 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 0) <| besselDerivativeNearFromState (415908643814907 / 1600000000000) 0 (IntervalRat.scale (465 / 4) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (1205933607 / 1000000000000) (1205933610 / 1000000000000), orderedInterval (-49475804094 / 1000000000000) (-49475804091 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 0) <| besselDerivativeNearFromState (240124967464803 / 1600000000000) 0 (IntervalRat.scale (465 / 4) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (4309915798 / 1000000000000) (4309915800 / 1000000000000), orderedInterval (64973109392 / 1000000000000) (64973109394 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 0) <| besselDerivativeNearFromState (426105968556927 / 1600000000000) 0 (IntervalRat.scale (465 / 4) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-3213994823 / 1000000000000) (-3213994822 / 1000000000000), orderedInterval (-48780643926 / 1000000000000) (-48780643925 / 1000000000000)))) (orderedInterval (-351838872 / 1000000000000) (-351838824 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 0) <| besselDerivativeNearFromState (398123468838363 / 1600000000000) 0 (IntervalRat.scale (465 / 4) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-50053848424 / 1000000000000) (-50053848413 / 1000000000000), orderedInterval (-7185645812 / 1000000000000) (-7185645801 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 0) <| besselDerivativeNearFromState (284119693087179 / 1600000000000) 0 (IntervalRat.scale (465 / 4) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (39086838517 / 1000000000000) (39086865267 / 1000000000000), orderedInterval (-45467531656 / 1000000000000) (-45467504906 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 0) <| besselDerivativeNearFromState (322161450207741 / 1600000000000) 0 (IntervalRat.scale (465 / 4) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (49425358118 / 1000000000000) (49425358119 / 1000000000000), orderedInterval (26689044179 / 1000000000000) (26689044180 / 1000000000000)))) (orderedInterval (4349669115 / 1000000000000) (4349671659 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 0) <| besselDerivativeNearFromState (268584630163629 / 1600000000000) 0 (IntervalRat.scale (465 / 4) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-51685064646 / 1000000000000) (-51685026047 / 1000000000000), orderedInterval (33636625504 / 1000000000000) (33636664103 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 0) <| besselDerivativeNearFromState (237302666104209 / 1600000000000) 0 (IntervalRat.scale (465 / 4) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-64988962415 / 1000000000000) (-64988962409 / 1000000000000), orderedInterval (-8074551759 / 1000000000000) (-8074551752 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 0) <| besselDerivativeNearFromState (68779561952691 / 320000000000) 0 (IntervalRat.scale (465 / 4) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (47179422537 / 1000000000000) (47179452125 / 1000000000000), orderedInterval (-27239061504 / 1000000000000) (-27239031917 / 1000000000000)))) (orderedInterval (4330239860 / 1000000000000) (4330241075 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate239_chunkChecks0_2 :
    compactCertificate239.chunkChecks (0 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 0) <| besselDerivativeNearFromState (190247888031177 / 1600000000000) 0 (IntervalRat.scale (465 / 4) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (22234711161 / 1000000000000) (22234711162 / 1000000000000), orderedInterval (69617905769 / 1000000000000) (69617905770 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 0) <| besselDerivativeNearFromState (161275241621697 / 1600000000000) 0 (IntervalRat.scale (465 / 4) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (68944428036 / 1000000000000) (68944428037 / 1000000000000), orderedInterval (39186296606 / 1000000000000) (39186296607 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 0) <| besselDerivativeNearFromState (100918557957291 / 1600000000000) 0 (IntervalRat.scale (465 / 4) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (85901981656 / 1000000000000) (85901981657 / 1000000000000), orderedInterval (51414258718 / 1000000000000) (51414258719 / 1000000000000)))) (orderedInterval (-4660851581 / 1000000000000) (-4660851551 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 0) <| besselDerivativeNearFromState (54274336109397 / 1600000000000) 0 (IntervalRat.scale (465 / 4) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-19882457655 / 1000000000000) (-19882457654 / 1000000000000), orderedInterval (-135258101679 / 1000000000000) (-135258101678 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 0) <| besselDerivativeNearFromState (147365380399191 / 1600000000000) 0 (IntervalRat.scale (465 / 4) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-81304153879 / 1000000000000) (-81304153320 / 1000000000000), orderedInterval (17806731633 / 1000000000000) (17806732192 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 0) <| besselDerivativeNearFromState (201214828281207 / 1600000000000) 0 (IntervalRat.scale (465 / 4) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (54835691094 / 1000000000000) (54835691095 / 1000000000000), orderedInterval (45116839790 / 1000000000000) (45116839791 / 1000000000000)))) (orderedInterval (-1990877395 / 1000000000000) (-1990877368 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 0) <| besselDerivativeNearFromState (85081442042709 / 1600000000000) 0 (IntervalRat.scale (465 / 4) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-57364028746 / 1000000000000) (-57364028745 / 1000000000000), orderedInterval (-92635592133 / 1000000000000) (-92635592132 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 0) <| besselDerivativeNearFromState (345851338323189 / 1600000000000) 0 (IntervalRat.scale (465 / 4) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-9289082350 / 1000000000000) (-9289082349 / 1000000000000), orderedInterval (-53447123139 / 1000000000000) (-53447123138 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 0) <| besselDerivativeNearFromState (231012665843451 / 1600000000000) 0 (IntervalRat.scale (465 / 4) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (40406512381 / 1000000000000) (40406512382 / 1000000000000), orderedInterval (52553208178 / 1000000000000) (52553208179 / 1000000000000)))) (orderedInterval (-7170994974 / 1000000000000) (-7170994940 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate239_chunkChecks0 :
    compactCertificate239.chunkChecks (0 : Fin 5) 0 9 = true :=
  compactCertificate239.chunkChecks_nine_of_three (0 : Fin 5) compactCertificate239_chunkChecks0_0
    compactCertificate239_chunkChecks0_1 compactCertificate239_chunkChecks0_2

theorem compactCertificate239_chunkChecks1_0 :
    compactCertificate239.chunkChecks (1 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 1) <| besselDerivativeNearFromState (465 / 4) 1 (IntervalRat.scale (465 / 4) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-52847558103 / 1000000000000) (-52847558102 / 1000000000000), orderedInterval (-51574572608 / 1000000000000) (-51574572607 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 1) <| besselDerivativeNearFromState (137006758154793 / 1600000000000) 1 (IntervalRat.scale (465 / 4) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-86207276754 / 1000000000000) (-86207276715 / 1000000000000), orderedInterval (2172943867 / 1000000000000) (2172943906 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 1) <| besselDerivativeNearFromState (44305170605769 / 320000000000) 1 (IntervalRat.scale (465 / 4) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (57353231884 / 1000000000000) (57353231885 / 1000000000000), orderedInterval (35968357641 / 1000000000000) (35968357642 / 1000000000000)))) (orderedInterval (-17913641379 / 1000000000000) (-17913641368 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 1) <| besselDerivativeNearFromState (39978230329851 / 1600000000000) 1 (IntervalRat.scale (465 / 4) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (94551938497 / 1000000000000) (94551938498 / 1000000000000), orderedInterval (126717027110 / 1000000000000) (126717027111 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 1) <| besselDerivativeNearFromState (107387150069247 / 1600000000000) 1 (IntervalRat.scale (465 / 4) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-91275312003 / 1000000000000) (-91275309331 / 1000000000000), orderedInterval (34648254236 / 1000000000000) (34648256908 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 1) <| besselDerivativeNearFromState (291577002213699 / 1600000000000) 1 (IntervalRat.scale (465 / 4) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (42725802324 / 1000000000000) (42725802325 / 1000000000000), orderedInterval (40722624013 / 1000000000000) (40722624014 / 1000000000000)))) (orderedInterval (-4103292454 / 1000000000000) (-4103292381 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 1) <| besselDerivativeNearFromState (214774300138587 / 1600000000000) 1 (IntervalRat.scale (465 / 4) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (4822176235 / 1000000000000) (4822176250 / 1000000000000), orderedInterval (-68715802504 / 1000000000000) (-68715802489 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 1) <| besselDerivativeNearFromState (368019423998151 / 1600000000000) 1 (IntervalRat.scale (465 / 4) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-52291155360 / 1000000000000) (-52291155343 / 1000000000000), orderedInterval (-5665140938 / 1000000000000) (-5665140921 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 1) <| besselDerivativeNearFromState (271081442042709 / 1600000000000) 1 (IntervalRat.scale (465 / 4) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (32797271477 / 1000000000000) (32797271478 / 1000000000000), orderedInterval (51689864881 / 1000000000000) (51689864882 / 1000000000000)))) (orderedInterval (2166410939 / 1000000000000) (2166410952 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate239_chunkChecks1_1 :
    compactCertificate239.chunkChecks (1 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 1) <| besselDerivativeNearFromState (415908643814907 / 1600000000000) 1 (IntervalRat.scale (465 / 4) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (1205933607 / 1000000000000) (1205933610 / 1000000000000), orderedInterval (-49475804094 / 1000000000000) (-49475804091 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 1) <| besselDerivativeNearFromState (240124967464803 / 1600000000000) 1 (IntervalRat.scale (465 / 4) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (4309915798 / 1000000000000) (4309915800 / 1000000000000), orderedInterval (64973109392 / 1000000000000) (64973109394 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 1) <| besselDerivativeNearFromState (426105968556927 / 1600000000000) 1 (IntervalRat.scale (465 / 4) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-3213994823 / 1000000000000) (-3213994822 / 1000000000000), orderedInterval (-48780643926 / 1000000000000) (-48780643925 / 1000000000000)))) (orderedInterval (9986559622 / 1000000000000) (9986559720 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 1) <| besselDerivativeNearFromState (398123468838363 / 1600000000000) 1 (IntervalRat.scale (465 / 4) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-50053848424 / 1000000000000) (-50053848413 / 1000000000000), orderedInterval (-7185645812 / 1000000000000) (-7185645801 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 1) <| besselDerivativeNearFromState (284119693087179 / 1600000000000) 1 (IntervalRat.scale (465 / 4) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (39086838517 / 1000000000000) (39086865267 / 1000000000000), orderedInterval (-45467531656 / 1000000000000) (-45467504906 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 1) <| besselDerivativeNearFromState (322161450207741 / 1600000000000) 1 (IntervalRat.scale (465 / 4) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (49425358118 / 1000000000000) (49425358119 / 1000000000000), orderedInterval (26689044179 / 1000000000000) (26689044180 / 1000000000000)))) (orderedInterval (-6523924531 / 1000000000000) (-6523920644 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 1) <| besselDerivativeNearFromState (268584630163629 / 1600000000000) 1 (IntervalRat.scale (465 / 4) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-51685064646 / 1000000000000) (-51685026047 / 1000000000000), orderedInterval (33636625504 / 1000000000000) (33636664103 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 1) <| besselDerivativeNearFromState (237302666104209 / 1600000000000) 1 (IntervalRat.scale (465 / 4) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-64988962415 / 1000000000000) (-64988962409 / 1000000000000), orderedInterval (-8074551759 / 1000000000000) (-8074551752 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 1) <| besselDerivativeNearFromState (68779561952691 / 320000000000) 1 (IntervalRat.scale (465 / 4) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (47179422537 / 1000000000000) (47179452125 / 1000000000000), orderedInterval (-27239061504 / 1000000000000) (-27239031917 / 1000000000000)))) (orderedInterval (-139065395 / 1000000000000) (-139063333 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate239_chunkChecks1_2 :
    compactCertificate239.chunkChecks (1 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 1) <| besselDerivativeNearFromState (190247888031177 / 1600000000000) 1 (IntervalRat.scale (465 / 4) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (22234711161 / 1000000000000) (22234711162 / 1000000000000), orderedInterval (69617905769 / 1000000000000) (69617905770 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 1) <| besselDerivativeNearFromState (161275241621697 / 1600000000000) 1 (IntervalRat.scale (465 / 4) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (68944428036 / 1000000000000) (68944428037 / 1000000000000), orderedInterval (39186296606 / 1000000000000) (39186296607 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 1) <| besselDerivativeNearFromState (100918557957291 / 1600000000000) 1 (IntervalRat.scale (465 / 4) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (85901981656 / 1000000000000) (85901981657 / 1000000000000), orderedInterval (51414258718 / 1000000000000) (51414258719 / 1000000000000)))) (orderedInterval (-12400549460 / 1000000000000) (-12400549432 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 1) <| besselDerivativeNearFromState (54274336109397 / 1600000000000) 1 (IntervalRat.scale (465 / 4) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-19882457655 / 1000000000000) (-19882457654 / 1000000000000), orderedInterval (-135258101679 / 1000000000000) (-135258101678 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 1) <| besselDerivativeNearFromState (147365380399191 / 1600000000000) 1 (IntervalRat.scale (465 / 4) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-81304153879 / 1000000000000) (-81304153320 / 1000000000000), orderedInterval (17806731633 / 1000000000000) (17806732192 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 1) <| besselDerivativeNearFromState (201214828281207 / 1600000000000) 1 (IntervalRat.scale (465 / 4) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (54835691094 / 1000000000000) (54835691095 / 1000000000000), orderedInterval (45116839790 / 1000000000000) (45116839791 / 1000000000000)))) (orderedInterval (-3331830708 / 1000000000000) (-3331830685 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 1) <| besselDerivativeNearFromState (85081442042709 / 1600000000000) 1 (IntervalRat.scale (465 / 4) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-57364028746 / 1000000000000) (-57364028745 / 1000000000000), orderedInterval (-92635592133 / 1000000000000) (-92635592132 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 1) <| besselDerivativeNearFromState (345851338323189 / 1600000000000) 1 (IntervalRat.scale (465 / 4) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-9289082350 / 1000000000000) (-9289082349 / 1000000000000), orderedInterval (-53447123139 / 1000000000000) (-53447123138 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 1) <| besselDerivativeNearFromState (231012665843451 / 1600000000000) 1 (IntervalRat.scale (465 / 4) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (40406512381 / 1000000000000) (40406512382 / 1000000000000), orderedInterval (52553208178 / 1000000000000) (52553208179 / 1000000000000)))) (orderedInterval (-4412323587 / 1000000000000) (-4412323540 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate239_chunkChecks1 :
    compactCertificate239.chunkChecks (1 : Fin 5) 0 9 = true :=
  compactCertificate239.chunkChecks_nine_of_three (1 : Fin 5) compactCertificate239_chunkChecks1_0
    compactCertificate239_chunkChecks1_1 compactCertificate239_chunkChecks1_2

theorem compactCertificate239_chunkChecks2_0 :
    compactCertificate239.chunkChecks (2 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 2) <| besselDerivativeNearFromState (465 / 4) 2 (IntervalRat.scale (465 / 4) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-52847558103 / 1000000000000) (-52847558102 / 1000000000000), orderedInterval (-51574572608 / 1000000000000) (-51574572607 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 2) <| besselDerivativeNearFromState (137006758154793 / 1600000000000) 2 (IntervalRat.scale (465 / 4) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-86207276754 / 1000000000000) (-86207276715 / 1000000000000), orderedInterval (2172943867 / 1000000000000) (2172943906 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 2) <| besselDerivativeNearFromState (44305170605769 / 320000000000) 2 (IntervalRat.scale (465 / 4) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (57353231884 / 1000000000000) (57353231885 / 1000000000000), orderedInterval (35968357641 / 1000000000000) (35968357642 / 1000000000000)))) (orderedInterval (16762891575 / 1000000000000) (16762891587 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 2) <| besselDerivativeNearFromState (39978230329851 / 1600000000000) 2 (IntervalRat.scale (465 / 4) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (94551938497 / 1000000000000) (94551938498 / 1000000000000), orderedInterval (126717027110 / 1000000000000) (126717027111 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 2) <| besselDerivativeNearFromState (107387150069247 / 1600000000000) 2 (IntervalRat.scale (465 / 4) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-91275312003 / 1000000000000) (-91275309331 / 1000000000000), orderedInterval (34648254236 / 1000000000000) (34648256908 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 2) <| besselDerivativeNearFromState (291577002213699 / 1600000000000) 2 (IntervalRat.scale (465 / 4) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (42725802324 / 1000000000000) (42725802325 / 1000000000000), orderedInterval (40722624013 / 1000000000000) (40722624014 / 1000000000000)))) (orderedInterval (8657657044 / 1000000000000) (8657657100 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 2) <| besselDerivativeNearFromState (214774300138587 / 1600000000000) 2 (IntervalRat.scale (465 / 4) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (4822176235 / 1000000000000) (4822176250 / 1000000000000), orderedInterval (-68715802504 / 1000000000000) (-68715802489 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 2) <| besselDerivativeNearFromState (368019423998151 / 1600000000000) 2 (IntervalRat.scale (465 / 4) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-52291155360 / 1000000000000) (-52291155343 / 1000000000000), orderedInterval (-5665140938 / 1000000000000) (-5665140921 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 2) <| besselDerivativeNearFromState (271081442042709 / 1600000000000) 2 (IntervalRat.scale (465 / 4) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (32797271477 / 1000000000000) (32797271478 / 1000000000000), orderedInterval (51689864881 / 1000000000000) (51689864882 / 1000000000000)))) (orderedInterval (-8016433685 / 1000000000000) (-8016433662 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate239_chunkChecks2_1 :
    compactCertificate239.chunkChecks (2 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 2) <| besselDerivativeNearFromState (415908643814907 / 1600000000000) 2 (IntervalRat.scale (465 / 4) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (1205933607 / 1000000000000) (1205933610 / 1000000000000), orderedInterval (-49475804094 / 1000000000000) (-49475804091 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 2) <| besselDerivativeNearFromState (240124967464803 / 1600000000000) 2 (IntervalRat.scale (465 / 4) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (4309915798 / 1000000000000) (4309915800 / 1000000000000), orderedInterval (64973109392 / 1000000000000) (64973109394 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 2) <| besselDerivativeNearFromState (426105968556927 / 1600000000000) 2 (IntervalRat.scale (465 / 4) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-3213994823 / 1000000000000) (-3213994822 / 1000000000000), orderedInterval (-48780643926 / 1000000000000) (-48780643925 / 1000000000000)))) (orderedInterval (2851113216 / 1000000000000) (2851113425 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 2) <| besselDerivativeNearFromState (398123468838363 / 1600000000000) 2 (IntervalRat.scale (465 / 4) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-50053848424 / 1000000000000) (-50053848413 / 1000000000000), orderedInterval (-7185645812 / 1000000000000) (-7185645801 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 2) <| besselDerivativeNearFromState (284119693087179 / 1600000000000) 2 (IntervalRat.scale (465 / 4) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (39086838517 / 1000000000000) (39086865267 / 1000000000000), orderedInterval (-45467531656 / 1000000000000) (-45467504906 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 2) <| besselDerivativeNearFromState (322161450207741 / 1600000000000) 2 (IntervalRat.scale (465 / 4) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (49425358118 / 1000000000000) (49425358119 / 1000000000000), orderedInterval (26689044179 / 1000000000000) (26689044180 / 1000000000000)))) (orderedInterval (-11957888627 / 1000000000000) (-11957882653 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 2) <| besselDerivativeNearFromState (268584630163629 / 1600000000000) 2 (IntervalRat.scale (465 / 4) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-51685064646 / 1000000000000) (-51685026047 / 1000000000000), orderedInterval (33636625504 / 1000000000000) (33636664103 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 2) <| besselDerivativeNearFromState (237302666104209 / 1600000000000) 2 (IntervalRat.scale (465 / 4) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-64988962415 / 1000000000000) (-64988962409 / 1000000000000), orderedInterval (-8074551759 / 1000000000000) (-8074551752 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 2) <| besselDerivativeNearFromState (68779561952691 / 320000000000) 2 (IntervalRat.scale (465 / 4) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (47179422537 / 1000000000000) (47179452125 / 1000000000000), orderedInterval (-27239061504 / 1000000000000) (-27239031917 / 1000000000000)))) (orderedInterval (-8937409888 / 1000000000000) (-8937406326 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate239_chunkChecks2_2 :
    compactCertificate239.chunkChecks (2 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 2) <| besselDerivativeNearFromState (190247888031177 / 1600000000000) 2 (IntervalRat.scale (465 / 4) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (22234711161 / 1000000000000) (22234711162 / 1000000000000), orderedInterval (69617905769 / 1000000000000) (69617905770 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 2) <| besselDerivativeNearFromState (161275241621697 / 1600000000000) 2 (IntervalRat.scale (465 / 4) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (68944428036 / 1000000000000) (68944428037 / 1000000000000), orderedInterval (39186296606 / 1000000000000) (39186296607 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 2) <| besselDerivativeNearFromState (100918557957291 / 1600000000000) 2 (IntervalRat.scale (465 / 4) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (85901981656 / 1000000000000) (85901981657 / 1000000000000), orderedInterval (51414258718 / 1000000000000) (51414258719 / 1000000000000)))) (orderedInterval (5936568685 / 1000000000000) (5936568712 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 2) <| besselDerivativeNearFromState (54274336109397 / 1600000000000) 2 (IntervalRat.scale (465 / 4) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-19882457655 / 1000000000000) (-19882457654 / 1000000000000), orderedInterval (-135258101679 / 1000000000000) (-135258101678 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 2) <| besselDerivativeNearFromState (147365380399191 / 1600000000000) 2 (IntervalRat.scale (465 / 4) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-81304153879 / 1000000000000) (-81304153320 / 1000000000000), orderedInterval (17806731633 / 1000000000000) (17806732192 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 2) <| besselDerivativeNearFromState (201214828281207 / 1600000000000) 2 (IntervalRat.scale (465 / 4) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (54835691094 / 1000000000000) (54835691095 / 1000000000000), orderedInterval (45116839790 / 1000000000000) (45116839791 / 1000000000000)))) (orderedInterval (3757754848 / 1000000000000) (3757754869 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 2) <| besselDerivativeNearFromState (85081442042709 / 1600000000000) 2 (IntervalRat.scale (465 / 4) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-57364028746 / 1000000000000) (-57364028745 / 1000000000000), orderedInterval (-92635592133 / 1000000000000) (-92635592132 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 2) <| besselDerivativeNearFromState (345851338323189 / 1600000000000) 2 (IntervalRat.scale (465 / 4) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-9289082350 / 1000000000000) (-9289082349 / 1000000000000), orderedInterval (-53447123139 / 1000000000000) (-53447123138 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 2) <| besselDerivativeNearFromState (231012665843451 / 1600000000000) 2 (IntervalRat.scale (465 / 4) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (40406512381 / 1000000000000) (40406512382 / 1000000000000), orderedInterval (52553208178 / 1000000000000) (52553208179 / 1000000000000)))) (orderedInterval (9190746140 / 1000000000000) (9190746208 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate239_chunkChecks2 :
    compactCertificate239.chunkChecks (2 : Fin 5) 0 9 = true :=
  compactCertificate239.chunkChecks_nine_of_three (2 : Fin 5) compactCertificate239_chunkChecks2_0
    compactCertificate239_chunkChecks2_1 compactCertificate239_chunkChecks2_2

theorem compactCertificate239_chunkChecks3_0 :
    compactCertificate239.chunkChecks (3 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 3) <| besselDerivativeNearFromState (465 / 4) 3 (IntervalRat.scale (465 / 4) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-52847558103 / 1000000000000) (-52847558102 / 1000000000000), orderedInterval (-51574572608 / 1000000000000) (-51574572607 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 3) <| besselDerivativeNearFromState (137006758154793 / 1600000000000) 3 (IntervalRat.scale (465 / 4) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-86207276754 / 1000000000000) (-86207276715 / 1000000000000), orderedInterval (2172943867 / 1000000000000) (2172943906 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 3) <| besselDerivativeNearFromState (44305170605769 / 320000000000) 3 (IntervalRat.scale (465 / 4) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (57353231884 / 1000000000000) (57353231885 / 1000000000000), orderedInterval (35968357641 / 1000000000000) (35968357642 / 1000000000000)))) (orderedInterval (16722968534 / 1000000000000) (16722968548 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 3) <| besselDerivativeNearFromState (39978230329851 / 1600000000000) 3 (IntervalRat.scale (465 / 4) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (94551938497 / 1000000000000) (94551938498 / 1000000000000), orderedInterval (126717027110 / 1000000000000) (126717027111 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 3) <| besselDerivativeNearFromState (107387150069247 / 1600000000000) 3 (IntervalRat.scale (465 / 4) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-91275312003 / 1000000000000) (-91275309331 / 1000000000000), orderedInterval (34648254236 / 1000000000000) (34648256908 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 3) <| besselDerivativeNearFromState (291577002213699 / 1600000000000) 3 (IntervalRat.scale (465 / 4) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (42725802324 / 1000000000000) (42725802325 / 1000000000000), orderedInterval (40722624013 / 1000000000000) (40722624014 / 1000000000000)))) (orderedInterval (10847674505 / 1000000000000) (10847674558 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 3) <| besselDerivativeNearFromState (214774300138587 / 1600000000000) 3 (IntervalRat.scale (465 / 4) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (4822176235 / 1000000000000) (4822176250 / 1000000000000), orderedInterval (-68715802504 / 1000000000000) (-68715802489 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 3) <| besselDerivativeNearFromState (368019423998151 / 1600000000000) 3 (IntervalRat.scale (465 / 4) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-52291155360 / 1000000000000) (-52291155343 / 1000000000000), orderedInterval (-5665140938 / 1000000000000) (-5665140921 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 3) <| besselDerivativeNearFromState (271081442042709 / 1600000000000) 3 (IntervalRat.scale (465 / 4) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (32797271477 / 1000000000000) (32797271478 / 1000000000000), orderedInterval (51689864881 / 1000000000000) (51689864882 / 1000000000000)))) (orderedInterval (-5151663829 / 1000000000000) (-5151663787 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate239_chunkChecks3_1 :
    compactCertificate239.chunkChecks (3 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 3) <| besselDerivativeNearFromState (415908643814907 / 1600000000000) 3 (IntervalRat.scale (465 / 4) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (1205933607 / 1000000000000) (1205933610 / 1000000000000), orderedInterval (-49475804094 / 1000000000000) (-49475804091 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 3) <| besselDerivativeNearFromState (240124967464803 / 1600000000000) 3 (IntervalRat.scale (465 / 4) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (4309915798 / 1000000000000) (4309915800 / 1000000000000), orderedInterval (64973109392 / 1000000000000) (64973109394 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 3) <| besselDerivativeNearFromState (426105968556927 / 1600000000000) 3 (IntervalRat.scale (465 / 4) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-3213994823 / 1000000000000) (-3213994822 / 1000000000000), orderedInterval (-48780643926 / 1000000000000) (-48780643925 / 1000000000000)))) (orderedInterval (-25297814848 / 1000000000000) (-25297814391 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 3) <| besselDerivativeNearFromState (398123468838363 / 1600000000000) 3 (IntervalRat.scale (465 / 4) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-50053848424 / 1000000000000) (-50053848413 / 1000000000000), orderedInterval (-7185645812 / 1000000000000) (-7185645801 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 3) <| besselDerivativeNearFromState (284119693087179 / 1600000000000) 3 (IntervalRat.scale (465 / 4) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (39086838517 / 1000000000000) (39086865267 / 1000000000000), orderedInterval (-45467531656 / 1000000000000) (-45467504906 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 3) <| besselDerivativeNearFromState (322161450207741 / 1600000000000) 3 (IntervalRat.scale (465 / 4) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (49425358118 / 1000000000000) (49425358119 / 1000000000000), orderedInterval (26689044179 / 1000000000000) (26689044180 / 1000000000000)))) (orderedInterval (14856573979 / 1000000000000) (14856583111 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 3) <| besselDerivativeNearFromState (268584630163629 / 1600000000000) 3 (IntervalRat.scale (465 / 4) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-51685064646 / 1000000000000) (-51685026047 / 1000000000000), orderedInterval (33636625504 / 1000000000000) (33636664103 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 3) <| besselDerivativeNearFromState (237302666104209 / 1600000000000) 3 (IntervalRat.scale (465 / 4) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-64988962415 / 1000000000000) (-64988962409 / 1000000000000), orderedInterval (-8074551759 / 1000000000000) (-8074551752 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 3) <| besselDerivativeNearFromState (68779561952691 / 320000000000) 3 (IntervalRat.scale (465 / 4) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (47179422537 / 1000000000000) (47179452125 / 1000000000000), orderedInterval (-27239061504 / 1000000000000) (-27239031917 / 1000000000000)))) (orderedInterval (2355814015 / 1000000000000) (2355820214 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate239_chunkChecks3_2 :
    compactCertificate239.chunkChecks (3 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 3) <| besselDerivativeNearFromState (190247888031177 / 1600000000000) 3 (IntervalRat.scale (465 / 4) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (22234711161 / 1000000000000) (22234711162 / 1000000000000), orderedInterval (69617905769 / 1000000000000) (69617905770 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 3) <| besselDerivativeNearFromState (161275241621697 / 1600000000000) 3 (IntervalRat.scale (465 / 4) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (68944428036 / 1000000000000) (68944428037 / 1000000000000), orderedInterval (39186296606 / 1000000000000) (39186296607 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 3) <| besselDerivativeNearFromState (100918557957291 / 1600000000000) 3 (IntervalRat.scale (465 / 4) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (85901981656 / 1000000000000) (85901981657 / 1000000000000), orderedInterval (51414258718 / 1000000000000) (51414258719 / 1000000000000)))) (orderedInterval (13038072941 / 1000000000000) (13038072967 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 3) <| besselDerivativeNearFromState (54274336109397 / 1600000000000) 3 (IntervalRat.scale (465 / 4) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-19882457655 / 1000000000000) (-19882457654 / 1000000000000), orderedInterval (-135258101679 / 1000000000000) (-135258101678 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 3) <| besselDerivativeNearFromState (147365380399191 / 1600000000000) 3 (IntervalRat.scale (465 / 4) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-81304153879 / 1000000000000) (-81304153320 / 1000000000000), orderedInterval (17806731633 / 1000000000000) (17806732192 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 3) <| besselDerivativeNearFromState (201214828281207 / 1600000000000) 3 (IntervalRat.scale (465 / 4) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (54835691094 / 1000000000000) (54835691095 / 1000000000000), orderedInterval (45116839790 / 1000000000000) (45116839791 / 1000000000000)))) (orderedInterval (4483815678 / 1000000000000) (4483815698 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 3) <| besselDerivativeNearFromState (85081442042709 / 1600000000000) 3 (IntervalRat.scale (465 / 4) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-57364028746 / 1000000000000) (-57364028745 / 1000000000000), orderedInterval (-92635592133 / 1000000000000) (-92635592132 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 3) <| besselDerivativeNearFromState (345851338323189 / 1600000000000) 3 (IntervalRat.scale (465 / 4) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-9289082350 / 1000000000000) (-9289082349 / 1000000000000), orderedInterval (-53447123139 / 1000000000000) (-53447123138 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 3) <| besselDerivativeNearFromState (231012665843451 / 1600000000000) 3 (IntervalRat.scale (465 / 4) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (40406512381 / 1000000000000) (40406512382 / 1000000000000), orderedInterval (52553208178 / 1000000000000) (52553208179 / 1000000000000)))) (orderedInterval (-9104327628 / 1000000000000) (-9104327523 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate239_chunkChecks3 :
    compactCertificate239.chunkChecks (3 : Fin 5) 0 9 = true :=
  compactCertificate239.chunkChecks_nine_of_three (3 : Fin 5) compactCertificate239_chunkChecks3_0
    compactCertificate239_chunkChecks3_1 compactCertificate239_chunkChecks3_2

theorem compactCertificate239_chunkChecks4_0 :
    compactCertificate239.chunkChecks (4 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 4) <| besselDerivativeNearFromState (465 / 4) 4 (IntervalRat.scale (465 / 4) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-52847558103 / 1000000000000) (-52847558102 / 1000000000000), orderedInterval (-51574572608 / 1000000000000) (-51574572607 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 4) <| besselDerivativeNearFromState (137006758154793 / 1600000000000) 4 (IntervalRat.scale (465 / 4) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-86207276754 / 1000000000000) (-86207276715 / 1000000000000), orderedInterval (2172943867 / 1000000000000) (2172943906 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 4) <| besselDerivativeNearFromState (44305170605769 / 320000000000) 4 (IntervalRat.scale (465 / 4) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (57353231884 / 1000000000000) (57353231885 / 1000000000000), orderedInterval (35968357641 / 1000000000000) (35968357642 / 1000000000000)))) (orderedInterval (-14698080328 / 1000000000000) (-14698080313 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 4) <| besselDerivativeNearFromState (39978230329851 / 1600000000000) 4 (IntervalRat.scale (465 / 4) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (94551938497 / 1000000000000) (94551938498 / 1000000000000), orderedInterval (126717027110 / 1000000000000) (126717027111 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 4) <| besselDerivativeNearFromState (107387150069247 / 1600000000000) 4 (IntervalRat.scale (465 / 4) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-91275312003 / 1000000000000) (-91275309331 / 1000000000000), orderedInterval (34648254236 / 1000000000000) (34648256908 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 4) <| besselDerivativeNearFromState (291577002213699 / 1600000000000) 4 (IntervalRat.scale (465 / 4) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (42725802324 / 1000000000000) (42725802325 / 1000000000000), orderedInterval (40722624013 / 1000000000000) (40722624014 / 1000000000000)))) (orderedInterval (-18900934835 / 1000000000000) (-18900934772 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 4) <| besselDerivativeNearFromState (214774300138587 / 1600000000000) 4 (IntervalRat.scale (465 / 4) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (4822176235 / 1000000000000) (4822176250 / 1000000000000), orderedInterval (-68715802504 / 1000000000000) (-68715802489 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 4) <| besselDerivativeNearFromState (368019423998151 / 1600000000000) 4 (IntervalRat.scale (465 / 4) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-52291155360 / 1000000000000) (-52291155343 / 1000000000000), orderedInterval (-5665140938 / 1000000000000) (-5665140921 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 4) <| besselDerivativeNearFromState (271081442042709 / 1600000000000) 4 (IntervalRat.scale (465 / 4) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (32797271477 / 1000000000000) (32797271478 / 1000000000000), orderedInterval (51689864881 / 1000000000000) (51689864882 / 1000000000000)))) (orderedInterval (28383229655 / 1000000000000) (28383229732 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate239_chunkChecks4_1 :
    compactCertificate239.chunkChecks (4 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 4) <| besselDerivativeNearFromState (415908643814907 / 1600000000000) 4 (IntervalRat.scale (465 / 4) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (1205933607 / 1000000000000) (1205933610 / 1000000000000), orderedInterval (-49475804094 / 1000000000000) (-49475804091 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 4) <| besselDerivativeNearFromState (240124967464803 / 1600000000000) 4 (IntervalRat.scale (465 / 4) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (4309915798 / 1000000000000) (4309915800 / 1000000000000), orderedInterval (64973109392 / 1000000000000) (64973109394 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 4) <| besselDerivativeNearFromState (426105968556927 / 1600000000000) 4 (IntervalRat.scale (465 / 4) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-3213994823 / 1000000000000) (-3213994822 / 1000000000000), orderedInterval (-48780643926 / 1000000000000) (-48780643925 / 1000000000000)))) (orderedInterval (-16618825270 / 1000000000000) (-16618824256 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 4) <| besselDerivativeNearFromState (398123468838363 / 1600000000000) 4 (IntervalRat.scale (465 / 4) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-50053848424 / 1000000000000) (-50053848413 / 1000000000000), orderedInterval (-7185645812 / 1000000000000) (-7185645801 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 4) <| besselDerivativeNearFromState (284119693087179 / 1600000000000) 4 (IntervalRat.scale (465 / 4) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (39086838517 / 1000000000000) (39086865267 / 1000000000000), orderedInterval (-45467531656 / 1000000000000) (-45467504906 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 4) <| besselDerivativeNearFromState (322161450207741 / 1600000000000) 4 (IntervalRat.scale (465 / 4) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (49425358118 / 1000000000000) (49425358119 / 1000000000000), orderedInterval (26689044179 / 1000000000000) (26689044180 / 1000000000000)))) (orderedInterval (36583411990 / 1000000000000) (36583426031 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 4) <| besselDerivativeNearFromState (268584630163629 / 1600000000000) 4 (IntervalRat.scale (465 / 4) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-51685064646 / 1000000000000) (-51685026047 / 1000000000000), orderedInterval (33636625504 / 1000000000000) (33636664103 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 4) <| besselDerivativeNearFromState (237302666104209 / 1600000000000) 4 (IntervalRat.scale (465 / 4) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-64988962415 / 1000000000000) (-64988962409 / 1000000000000), orderedInterval (-8074551759 / 1000000000000) (-8074551752 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 4) <| besselDerivativeNearFromState (68779561952691 / 320000000000) 4 (IntervalRat.scale (465 / 4) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (47179422537 / 1000000000000) (47179452125 / 1000000000000), orderedInterval (-27239061504 / 1000000000000) (-27239031917 / 1000000000000)))) (orderedInterval (21333930584 / 1000000000000) (21333941540 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate239_chunkChecks4_2 :
    compactCertificate239.chunkChecks (4 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 4) <| besselDerivativeNearFromState (190247888031177 / 1600000000000) 4 (IntervalRat.scale (465 / 4) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (22234711161 / 1000000000000) (22234711162 / 1000000000000), orderedInterval (69617905769 / 1000000000000) (69617905770 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 4) <| besselDerivativeNearFromState (161275241621697 / 1600000000000) 4 (IntervalRat.scale (465 / 4) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (68944428036 / 1000000000000) (68944428037 / 1000000000000), orderedInterval (39186296606 / 1000000000000) (39186296607 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 4) <| besselDerivativeNearFromState (100918557957291 / 1600000000000) 4 (IntervalRat.scale (465 / 4) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (85901981656 / 1000000000000) (85901981657 / 1000000000000), orderedInterval (51414258718 / 1000000000000) (51414258719 / 1000000000000)))) (orderedInterval (-6078375473 / 1000000000000) (-6078375447 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 4) <| besselDerivativeNearFromState (54274336109397 / 1600000000000) 4 (IntervalRat.scale (465 / 4) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-19882457655 / 1000000000000) (-19882457654 / 1000000000000), orderedInterval (-135258101679 / 1000000000000) (-135258101678 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 4) <| besselDerivativeNearFromState (147365380399191 / 1600000000000) 4 (IntervalRat.scale (465 / 4) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-81304153879 / 1000000000000) (-81304153320 / 1000000000000), orderedInterval (17806731633 / 1000000000000) (17806732192 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 4) <| besselDerivativeNearFromState (201214828281207 / 1600000000000) 4 (IntervalRat.scale (465 / 4) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (54835691094 / 1000000000000) (54835691095 / 1000000000000), orderedInterval (45116839790 / 1000000000000) (45116839791 / 1000000000000)))) (orderedInterval (-5103127216 / 1000000000000) (-5103127197 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 4) <| besselDerivativeNearFromState (85081442042709 / 1600000000000) 4 (IntervalRat.scale (465 / 4) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-57364028746 / 1000000000000) (-57364028745 / 1000000000000), orderedInterval (-92635592133 / 1000000000000) (-92635592132 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 4) <| besselDerivativeNearFromState (345851338323189 / 1600000000000) 4 (IntervalRat.scale (465 / 4) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-9289082350 / 1000000000000) (-9289082349 / 1000000000000), orderedInterval (-53447123139 / 1000000000000) (-53447123138 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 4) <| besselDerivativeNearFromState (231012665843451 / 1600000000000) 4 (IntervalRat.scale (465 / 4) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (40406512381 / 1000000000000) (40406512382 / 1000000000000), orderedInterval (52553208178 / 1000000000000) (52553208179 / 1000000000000)))) (orderedInterval (-8859001435 / 1000000000000) (-8859001267 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate239_chunkChecks4 :
    compactCertificate239.chunkChecks (4 : Fin 5) 0 9 = true :=
  compactCertificate239.chunkChecks_nine_of_three (4 : Fin 5) compactCertificate239_chunkChecks4_0
    compactCertificate239_chunkChecks4_1 compactCertificate239_chunkChecks4_2

theorem compactCertificate239_chunks :
    ∀ r : Fin 5, ∀ b, compactCertificate239.chunkCheck r b = true :=
  compactCertificate239.chunkChecks_all (by
    intro r
    fin_cases r
    · exact compactCertificate239_chunkChecks0
    · exact compactCertificate239_chunkChecks1
    · exact compactCertificate239_chunkChecks2
    · exact compactCertificate239_chunkChecks3
    · exact compactCertificate239_chunkChecks4)

theorem compactCertificate239_coefficient0 :
    compactCertificate239.coefficientCheck (0 : Fin 5) = true := by
  norm_num [CompactCertificate.coefficientCheck, intervalFinSumHull,
    compactCertificate239, rationalIntervalSubset, orderedInterval, Fin.sum_univ_succ]

theorem compactCertificate239_coefficient1 :
    compactCertificate239.coefficientCheck (1 : Fin 5) = true := by
  norm_num [CompactCertificate.coefficientCheck, intervalFinSumHull,
    compactCertificate239, rationalIntervalSubset, orderedInterval, Fin.sum_univ_succ]

theorem compactCertificate239_coefficient2 :
    compactCertificate239.coefficientCheck (2 : Fin 5) = true := by
  norm_num [CompactCertificate.coefficientCheck, intervalFinSumHull,
    compactCertificate239, rationalIntervalSubset, orderedInterval, Fin.sum_univ_succ]

theorem compactCertificate239_coefficient3 :
    compactCertificate239.coefficientCheck (3 : Fin 5) = true := by
  norm_num [CompactCertificate.coefficientCheck, intervalFinSumHull,
    compactCertificate239, rationalIntervalSubset, orderedInterval, Fin.sum_univ_succ]

theorem compactCertificate239_coefficient4 :
    compactCertificate239.coefficientCheck (4 : Fin 5) = true := by
  norm_num [CompactCertificate.coefficientCheck, intervalFinSumHull,
    compactCertificate239, rationalIntervalSubset, orderedInterval, Fin.sum_univ_succ]

theorem compactCertificate239_coefficients : ∀ r : Fin 5,
    compactCertificate239.coefficientCheck r = true := by
  intro r
  fin_cases r
  · exact compactCertificate239_coefficient0
  · exact compactCertificate239_coefficient1
  · exact compactCertificate239_coefficient2
  · exact compactCertificate239_coefficient3
  · exact compactCertificate239_coefficient4

theorem compactCertificate239_lower : (1 : ℚ) ≤ compactCertificate239.output.lo := by
  norm_num [CompactCertificate.output, CompactCertificate.interval,
    CompactCertificate.coefficientTargetNat, compactCertificate239, dualConstant,
    intervalTaylorSum, intervalPow, intervalSub, intervalMaxAbs, widenInterval,
    rationalErrorInterval, orderedInterval, IntervalRat.add, IntervalRat.mul, IntervalRat.scale,
    IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4]

theorem compactCertificate239_proves {t : ℝ} (ht : t ∈ compactCertificate239.interval) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t :=
  compactCertificate239.proves compactCertificate239_states compactCertificate239_chunks
    compactCertificate239_coefficients compactCertificate239_lower ht

end Erdos232
