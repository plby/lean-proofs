/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, OpenAI Codex
-/
import ErdosProblems.Erdos232.CompactBase

open LeanCert.Core
namespace Erdos232

def compactCertificate220 : CompactCertificate where
  left := 99
  right := 100
  center := 199 / 2
  grid := fun i =>
    match i.val with
    | 0 => 32
    | 1 => 23
    | 2 => 38
    | 3 => 7
    | 4 => 18
    | 5 => 50
    | 6 => 37
    | 7 => 63
    | 8 => 46
    | 9 => 71
    | 10 => 41
    | 11 => 73
    | 12 => 68
    | 13 => 48
    | 14 => 55
    | 15 => 46
    | 16 => 40
    | 17 => 59
    | 18 => 32
    | 19 => 27
    | 20 => 17
    | 21 => 9
    | 22 => 25
    | 23 => 34
    | 24 => 14
    | 25 => 59
    | _ => 39
  point := fun i =>
    match i.val with
    | 0 => 199 / 2
    | 1 => 293164998632299 / 4000000000000
    | 2 => 94803537102667 / 800000000000
    | 3 => 85544815436993 / 4000000000000
    | 4 => 229785407137421 / 4000000000000
    | 5 => 623912080005657 / 4000000000000
    | 6 => 459570814275041 / 4000000000000
    | 7 => 787482423393893 / 4000000000000
    | 8 => 580055988887087 / 4000000000000
    | 9 => 889955055044801 / 4000000000000
    | 10 => 513815790596729 / 4000000000000
    | 11 => 911775137019661 / 4000000000000
    | 12 => 851898605363809 / 4000000000000
    | 13 => 607955042197297 / 4000000000000
    | 14 => 689356221412263 / 4000000000000
    | 15 => 574713348414647 / 4000000000000
    | 16 => 507776672631587 / 4000000000000
    | 17 => 147173471275113 / 800000000000
    | 18 => 407089566862411 / 4000000000000
    | 19 => 345094334222771 / 4000000000000
    | 20 => 215944011112913 / 4000000000000
    | 21 => 116135407373871 / 4000000000000
    | 22 => 315330222574613 / 4000000000000
    | 23 => 430556460515701 / 4000000000000
    | 24 => 182055988887087 / 4000000000000
    | 25 => 740047487379727 / 4000000000000
    | _ => 494317424761793 / 4000000000000
  state := fun i =>
    match i.val with
    | 0 => (orderedInterval (-19543066524 / 1000000000000) (-19543066276 / 1000000000000), orderedInterval (77663198113 / 1000000000000) (77663198361 / 1000000000000))
    | 1 => (orderedInterval (-90358206787 / 1000000000000) (-90358206000 / 1000000000000), orderedInterval (23450153596 / 1000000000000) (23450154383 / 1000000000000))
    | 2 => (orderedInterval (-6715774085 / 1000000000000) (-6715774061 / 1000000000000), orderedInterval (73015071504 / 1000000000000) (73015071528 / 1000000000000))
    | 3 => (orderedInterval (-29970005138 / 1000000000000) (-29970005136 / 1000000000000), orderedInterval (-169232610155 / 1000000000000) (-169232610153 / 1000000000000))
    | 4 => (orderedInterval (104631517667 / 1000000000000) (104631517787 / 1000000000000), orderedInterval (-12478849449 / 1000000000000) (-12478849329 / 1000000000000))
    | 5 => (orderedInterval (-19915416439 / 1000000000000) (-19915416012 / 1000000000000), orderedInterval (60766921338 / 1000000000000) (60766921765 / 1000000000000))
    | 6 => (orderedInterval (39660830969 / 1000000000000) (39660839532 / 1000000000000), orderedInterval (-63164938915 / 1000000000000) (-63164930352 / 1000000000000))
    | 7 => (orderedInterval (14891852253 / 1000000000000) (14891852418 / 1000000000000), orderedInterval (-54918948681 / 1000000000000) (-54918948516 / 1000000000000))
    | 8 => (orderedInterval (63574812634 / 1000000000000) (63574812635 / 1000000000000), orderedInterval (18443025508 / 1000000000000) (18443025509 / 1000000000000))
    | 9 => (orderedInterval (-11700680896 / 1000000000000) (-11700680895 / 1000000000000), orderedInterval (-52170041783 / 1000000000000) (-52170041782 / 1000000000000))
    | 10 => (orderedInterval (-29543728065 / 1000000000000) (-29543728064 / 1000000000000), orderedInterval (-63784989370 / 1000000000000) (-63784989369 / 1000000000000))
    | 11 => (orderedInterval (30171934459 / 1000000000000) (30171942112 / 1000000000000), orderedInterval (-43454399694 / 1000000000000) (-43454392041 / 1000000000000))
    | 12 => (orderedInterval (7150527176 / 1000000000000) (7150527177 / 1000000000000), orderedInterval (54187076841 / 1000000000000) (54187076842 / 1000000000000))
    | 13 => (orderedInterval (59455671969 / 1000000000000) (59455679060 / 1000000000000), orderedInterval (-25761288141 / 1000000000000) (-25761281049 / 1000000000000))
    | 14 => (orderedInterval (-20046952242 / 1000000000000) (-20046952241 / 1000000000000), orderedInterval (-57318906124 / 1000000000000) (-57318906123 / 1000000000000))
    | 15 => (orderedInterval (-3353219572 / 1000000000000) (-3353219561 / 1000000000000), orderedInterval (66492123257 / 1000000000000) (66492123267 / 1000000000000))
    | 16 => (orderedInterval (62346892800 / 1000000000000) (62346907820 / 1000000000000), orderedInterval (-33828325555 / 1000000000000) (-33828310535 / 1000000000000))
    | 17 => (orderedInterval (33332518163 / 1000000000000) (33332527247 / 1000000000000), orderedInterval (-48561838700 / 1000000000000) (-48561829616 / 1000000000000))
    | 18 => (orderedInterval (71050536919 / 1000000000000) (71050545933 / 1000000000000), orderedInterval (-35092449226 / 1000000000000) (-35092440212 / 1000000000000))
    | 19 => (orderedInterval (-67663854350 / 1000000000000) (-67663795229 / 1000000000000), orderedInterval (53313344392 / 1000000000000) (53313403513 / 1000000000000))
    | 20 => (orderedInterval (-106231872649 / 1000000000000) (-106231872648 / 1000000000000), orderedInterval (-21524841365 / 1000000000000) (-21524841364 / 1000000000000))
    | 21 => (orderedInterval (-147998646167 / 1000000000000) (-147998646155 / 1000000000000), orderedInterval (-1921069822 / 1000000000000) (-1921069810 / 1000000000000))
    | 22 => (orderedInterval (-79109222384 / 1000000000000) (-79109222383 / 1000000000000), orderedInterval (-42127320950 / 1000000000000) (-42127320949 / 1000000000000))
    | 23 => (orderedInterval (76847950965 / 1000000000000) (76847951026 / 1000000000000), orderedInterval (-3309831076 / 1000000000000) (-3309831015 / 1000000000000))
    | 24 => (orderedInterval (87050440617 / 1000000000000) (87050539611 / 1000000000000), orderedInterval (-81015471860 / 1000000000000) (-81015372867 / 1000000000000))
    | 25 => (orderedInterval (-25124838659 / 1000000000000) (-25124838658 / 1000000000000), orderedInterval (-52938869093 / 1000000000000) (-52938869092 / 1000000000000))
    | _ => (orderedInterval (-69157428814 / 1000000000000) (-69157427422 / 1000000000000), orderedInterval (19481883122 / 1000000000000) (19481884514 / 1000000000000))
  chunkTarget := fun r b =>
    match r.val with
    | 0 =>
      match b.val with
      | 0 => orderedInterval (-8982239901 / 1000000000000) (-8982239787 / 1000000000000)
      | 1 => orderedInterval (5561212472 / 1000000000000) (5561212519 / 1000000000000)
      | 2 => orderedInterval (1077153474 / 1000000000000) (1077153486 / 1000000000000)
      | 3 => orderedInterval (4179240823 / 1000000000000) (4179241951 / 1000000000000)
      | 4 => orderedInterval (5594658778 / 1000000000000) (5594659462 / 1000000000000)
      | 5 => orderedInterval (-2753184106 / 1000000000000) (-2753183003 / 1000000000000)
      | 6 => orderedInterval (-10989084878 / 1000000000000) (-10989080064 / 1000000000000)
      | 7 => orderedInterval (-1361987807 / 1000000000000) (-1361987789 / 1000000000000)
      | _ => orderedInterval (15545743031 / 1000000000000) (15545743918 / 1000000000000)
    | 1 =>
      match b.val with
      | 0 => orderedInterval (36046890709 / 1000000000000) (36046890823 / 1000000000000)
      | 1 => orderedInterval (-6640371735 / 1000000000000) (-6640371670 / 1000000000000)
      | 2 => orderedInterval (4001209934 / 1000000000000) (4001209955 / 1000000000000)
      | 3 => orderedInterval (475627399 / 1000000000000) (475629974 / 1000000000000)
      | 4 => orderedInterval (-5312615854 / 1000000000000) (-5312614809 / 1000000000000)
      | 5 => orderedInterval (1279694106 / 1000000000000) (1279695648 / 1000000000000)
      | 6 => orderedInterval (2742535797 / 1000000000000) (2742540196 / 1000000000000)
      | 7 => orderedInterval (1041979906 / 1000000000000) (1041979922 / 1000000000000)
      | _ => orderedInterval (3249493688 / 1000000000000) (3249494325 / 1000000000000)
    | 2 =>
      match b.val with
      | 0 => orderedInterval (8399740825 / 1000000000000) (8399740940 / 1000000000000)
      | 1 => orderedInterval (-4700886110 / 1000000000000) (-4700886014 / 1000000000000)
      | 2 => orderedInterval (-1505648384 / 1000000000000) (-1505648346 / 1000000000000)
      | 3 => orderedInterval (-29261986409 / 1000000000000) (-29261980497 / 1000000000000)
      | 4 => orderedInterval (-12778228581 / 1000000000000) (-12778226974 / 1000000000000)
      | 5 => orderedInterval (2957944163 / 1000000000000) (2957946395 / 1000000000000)
      | 6 => orderedInterval (9996542869 / 1000000000000) (9996546959 / 1000000000000)
      | 7 => orderedInterval (5522727713 / 1000000000000) (5522727730 / 1000000000000)
      | _ => orderedInterval (-27229681439 / 1000000000000) (-27229680847 / 1000000000000)
    | 3 =>
      match b.val with
      | 0 => orderedInterval (-38189528859 / 1000000000000) (-38189528744 / 1000000000000)
      | 1 => orderedInterval (16757606708 / 1000000000000) (16757606855 / 1000000000000)
      | 2 => orderedInterval (-14485301364 / 1000000000000) (-14485301292 / 1000000000000)
      | 3 => orderedInterval (-18908999314 / 1000000000000) (-18908985790 / 1000000000000)
      | 4 => orderedInterval (16896486182 / 1000000000000) (16896488643 / 1000000000000)
      | 5 => orderedInterval (1497009316 / 1000000000000) (1497012625 / 1000000000000)
      | 6 => orderedInterval (-4025508652 / 1000000000000) (-4025504867 / 1000000000000)
      | 7 => orderedInterval (-852741835 / 1000000000000) (-852741817 / 1000000000000)
      | _ => orderedInterval (-20379827925 / 1000000000000) (-20379827273 / 1000000000000)
    | _ =>
      match b.val with
      | 0 => orderedInterval (-8018548836 / 1000000000000) (-8018548717 / 1000000000000)
      | 1 => orderedInterval (8637685442 / 1000000000000) (8637685673 / 1000000000000)
      | 2 => orderedInterval (183604001 / 1000000000000) (183604138 / 1000000000000)
      | 3 => orderedInterval (164410668799 / 1000000000000) (164410699884 / 1000000000000)
      | 4 => orderedInterval (28472799117 / 1000000000000) (28472802910 / 1000000000000)
      | 5 => orderedInterval (322144110 / 1000000000000) (322149222 / 1000000000000)
      | 6 => orderedInterval (-10487470742 / 1000000000000) (-10487467177 / 1000000000000)
      | 7 => orderedInterval (-7321517850 / 1000000000000) (-7321517831 / 1000000000000)
      | _ => orderedInterval (55754103808 / 1000000000000) (55754104610 / 1000000000000)
  coefficientTarget := fun i =>
    match i.val with
    | 0 => orderedInterval (7871511886 / 1000000000000) (7871520693 / 1000000000000)
    | 1 => orderedInterval (36884443950 / 1000000000000) (36884454364 / 1000000000000)
    | 2 => orderedInterval (-48599475353 / 1000000000000) (-48599460654 / 1000000000000)
    | 3 => orderedInterval (-61690805743 / 1000000000000) (-61690781660 / 1000000000000)
    | _ => orderedInterval (231953467849 / 1000000000000) (231953512712 / 1000000000000)

theorem compactCertificate220_stateChecks0 :
    compactCertificate220.stateChecks 0 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 32 12 (199 / 2)) (orderedInterval (-19543066524 / 1000000000000) (-19543066276 / 1000000000000), orderedInterval (77663198113 / 1000000000000) (77663198361 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 23 12 (293164998632299 / 4000000000000)) (orderedInterval (-90358206787 / 1000000000000) (-90358206000 / 1000000000000), orderedInterval (23450153596 / 1000000000000) (23450154383 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 38 12 (94803537102667 / 800000000000)) (orderedInterval (-6715774085 / 1000000000000) (-6715774061 / 1000000000000), orderedInterval (73015071504 / 1000000000000) (73015071528 / 1000000000000))) = true
  norm_num [besselStateAtRationalPoint, besselIntervalStepZero,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, besselZeroTransition,
    besselInitial, besselGridStateAt, besselGridStateBlock00, besselGridStateBlock01,
    besselGridStateBlock02, besselGridStateBlock03, besselGridStateBlock04,
    besselGridStateBlock05, besselGridStateBlock06, besselGridStateBlock07,
    besselGridStateBlock08, besselGridStateBlock09, besselGridStateBlock10,
    besselGridStateBlock11, besselGridStateBlock12, besselGridStateBlock13,
    besselGridStateBlock14, besselGridState007, besselGridState009, besselGridState014, besselGridState017, besselGridState018, besselGridState023, besselGridState025, besselGridState027, besselGridState032, besselGridState034, besselGridState037, besselGridState038, besselGridState039, besselGridState040, besselGridState041, besselGridState046, besselGridState048, besselGridState050, besselGridState055, besselGridState059, besselGridState063, besselGridState068, besselGridState071, besselGridState073, besselStateSubset, linearInterval, widenInterval,
    rationalErrorInterval, rationalIntervalSubset, orderedInterval, Finset.sum_range_succ,
    IntervalRat.add, IntervalRat.mul, IntervalRat.scale, IntervalRat.singleton]

theorem compactCertificate220_stateChecks1 :
    compactCertificate220.stateChecks 3 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 7 12 (85544815436993 / 4000000000000)) (orderedInterval (-29970005138 / 1000000000000) (-29970005136 / 1000000000000), orderedInterval (-169232610155 / 1000000000000) (-169232610153 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 18 12 (229785407137421 / 4000000000000)) (orderedInterval (104631517667 / 1000000000000) (104631517787 / 1000000000000), orderedInterval (-12478849449 / 1000000000000) (-12478849329 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 50 12 (623912080005657 / 4000000000000)) (orderedInterval (-19915416439 / 1000000000000) (-19915416012 / 1000000000000), orderedInterval (60766921338 / 1000000000000) (60766921765 / 1000000000000))) = true
  norm_num [besselStateAtRationalPoint, besselIntervalStepZero,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, besselZeroTransition,
    besselInitial, besselGridStateAt, besselGridStateBlock00, besselGridStateBlock01,
    besselGridStateBlock02, besselGridStateBlock03, besselGridStateBlock04,
    besselGridStateBlock05, besselGridStateBlock06, besselGridStateBlock07,
    besselGridStateBlock08, besselGridStateBlock09, besselGridStateBlock10,
    besselGridStateBlock11, besselGridStateBlock12, besselGridStateBlock13,
    besselGridStateBlock14, besselGridState007, besselGridState009, besselGridState014, besselGridState017, besselGridState018, besselGridState023, besselGridState025, besselGridState027, besselGridState032, besselGridState034, besselGridState037, besselGridState038, besselGridState039, besselGridState040, besselGridState041, besselGridState046, besselGridState048, besselGridState050, besselGridState055, besselGridState059, besselGridState063, besselGridState068, besselGridState071, besselGridState073, besselStateSubset, linearInterval, widenInterval,
    rationalErrorInterval, rationalIntervalSubset, orderedInterval, Finset.sum_range_succ,
    IntervalRat.add, IntervalRat.mul, IntervalRat.scale, IntervalRat.singleton]

theorem compactCertificate220_stateChecks2 :
    compactCertificate220.stateChecks 6 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 37 12 (459570814275041 / 4000000000000)) (orderedInterval (39660830969 / 1000000000000) (39660839532 / 1000000000000), orderedInterval (-63164938915 / 1000000000000) (-63164930352 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 63 12 (787482423393893 / 4000000000000)) (orderedInterval (14891852253 / 1000000000000) (14891852418 / 1000000000000), orderedInterval (-54918948681 / 1000000000000) (-54918948516 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 46 12 (580055988887087 / 4000000000000)) (orderedInterval (63574812634 / 1000000000000) (63574812635 / 1000000000000), orderedInterval (18443025508 / 1000000000000) (18443025509 / 1000000000000))) = true
  norm_num [besselStateAtRationalPoint, besselIntervalStepZero,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, besselZeroTransition,
    besselInitial, besselGridStateAt, besselGridStateBlock00, besselGridStateBlock01,
    besselGridStateBlock02, besselGridStateBlock03, besselGridStateBlock04,
    besselGridStateBlock05, besselGridStateBlock06, besselGridStateBlock07,
    besselGridStateBlock08, besselGridStateBlock09, besselGridStateBlock10,
    besselGridStateBlock11, besselGridStateBlock12, besselGridStateBlock13,
    besselGridStateBlock14, besselGridState007, besselGridState009, besselGridState014, besselGridState017, besselGridState018, besselGridState023, besselGridState025, besselGridState027, besselGridState032, besselGridState034, besselGridState037, besselGridState038, besselGridState039, besselGridState040, besselGridState041, besselGridState046, besselGridState048, besselGridState050, besselGridState055, besselGridState059, besselGridState063, besselGridState068, besselGridState071, besselGridState073, besselStateSubset, linearInterval, widenInterval,
    rationalErrorInterval, rationalIntervalSubset, orderedInterval, Finset.sum_range_succ,
    IntervalRat.add, IntervalRat.mul, IntervalRat.scale, IntervalRat.singleton]

theorem compactCertificate220_stateChecks3 :
    compactCertificate220.stateChecks 9 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 71 12 (889955055044801 / 4000000000000)) (orderedInterval (-11700680896 / 1000000000000) (-11700680895 / 1000000000000), orderedInterval (-52170041783 / 1000000000000) (-52170041782 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 41 12 (513815790596729 / 4000000000000)) (orderedInterval (-29543728065 / 1000000000000) (-29543728064 / 1000000000000), orderedInterval (-63784989370 / 1000000000000) (-63784989369 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 73 12 (911775137019661 / 4000000000000)) (orderedInterval (30171934459 / 1000000000000) (30171942112 / 1000000000000), orderedInterval (-43454399694 / 1000000000000) (-43454392041 / 1000000000000))) = true
  norm_num [besselStateAtRationalPoint, besselIntervalStepZero,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, besselZeroTransition,
    besselInitial, besselGridStateAt, besselGridStateBlock00, besselGridStateBlock01,
    besselGridStateBlock02, besselGridStateBlock03, besselGridStateBlock04,
    besselGridStateBlock05, besselGridStateBlock06, besselGridStateBlock07,
    besselGridStateBlock08, besselGridStateBlock09, besselGridStateBlock10,
    besselGridStateBlock11, besselGridStateBlock12, besselGridStateBlock13,
    besselGridStateBlock14, besselGridState007, besselGridState009, besselGridState014, besselGridState017, besselGridState018, besselGridState023, besselGridState025, besselGridState027, besselGridState032, besselGridState034, besselGridState037, besselGridState038, besselGridState039, besselGridState040, besselGridState041, besselGridState046, besselGridState048, besselGridState050, besselGridState055, besselGridState059, besselGridState063, besselGridState068, besselGridState071, besselGridState073, besselStateSubset, linearInterval, widenInterval,
    rationalErrorInterval, rationalIntervalSubset, orderedInterval, Finset.sum_range_succ,
    IntervalRat.add, IntervalRat.mul, IntervalRat.scale, IntervalRat.singleton]

theorem compactCertificate220_stateChecks4 :
    compactCertificate220.stateChecks 12 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 68 12 (851898605363809 / 4000000000000)) (orderedInterval (7150527176 / 1000000000000) (7150527177 / 1000000000000), orderedInterval (54187076841 / 1000000000000) (54187076842 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 48 12 (607955042197297 / 4000000000000)) (orderedInterval (59455671969 / 1000000000000) (59455679060 / 1000000000000), orderedInterval (-25761288141 / 1000000000000) (-25761281049 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 55 12 (689356221412263 / 4000000000000)) (orderedInterval (-20046952242 / 1000000000000) (-20046952241 / 1000000000000), orderedInterval (-57318906124 / 1000000000000) (-57318906123 / 1000000000000))) = true
  norm_num [besselStateAtRationalPoint, besselIntervalStepZero,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, besselZeroTransition,
    besselInitial, besselGridStateAt, besselGridStateBlock00, besselGridStateBlock01,
    besselGridStateBlock02, besselGridStateBlock03, besselGridStateBlock04,
    besselGridStateBlock05, besselGridStateBlock06, besselGridStateBlock07,
    besselGridStateBlock08, besselGridStateBlock09, besselGridStateBlock10,
    besselGridStateBlock11, besselGridStateBlock12, besselGridStateBlock13,
    besselGridStateBlock14, besselGridState007, besselGridState009, besselGridState014, besselGridState017, besselGridState018, besselGridState023, besselGridState025, besselGridState027, besselGridState032, besselGridState034, besselGridState037, besselGridState038, besselGridState039, besselGridState040, besselGridState041, besselGridState046, besselGridState048, besselGridState050, besselGridState055, besselGridState059, besselGridState063, besselGridState068, besselGridState071, besselGridState073, besselStateSubset, linearInterval, widenInterval,
    rationalErrorInterval, rationalIntervalSubset, orderedInterval, Finset.sum_range_succ,
    IntervalRat.add, IntervalRat.mul, IntervalRat.scale, IntervalRat.singleton]

theorem compactCertificate220_stateChecks5 :
    compactCertificate220.stateChecks 15 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 46 12 (574713348414647 / 4000000000000)) (orderedInterval (-3353219572 / 1000000000000) (-3353219561 / 1000000000000), orderedInterval (66492123257 / 1000000000000) (66492123267 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 40 12 (507776672631587 / 4000000000000)) (orderedInterval (62346892800 / 1000000000000) (62346907820 / 1000000000000), orderedInterval (-33828325555 / 1000000000000) (-33828310535 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 59 12 (147173471275113 / 800000000000)) (orderedInterval (33332518163 / 1000000000000) (33332527247 / 1000000000000), orderedInterval (-48561838700 / 1000000000000) (-48561829616 / 1000000000000))) = true
  norm_num [besselStateAtRationalPoint, besselIntervalStepZero,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, besselZeroTransition,
    besselInitial, besselGridStateAt, besselGridStateBlock00, besselGridStateBlock01,
    besselGridStateBlock02, besselGridStateBlock03, besselGridStateBlock04,
    besselGridStateBlock05, besselGridStateBlock06, besselGridStateBlock07,
    besselGridStateBlock08, besselGridStateBlock09, besselGridStateBlock10,
    besselGridStateBlock11, besselGridStateBlock12, besselGridStateBlock13,
    besselGridStateBlock14, besselGridState007, besselGridState009, besselGridState014, besselGridState017, besselGridState018, besselGridState023, besselGridState025, besselGridState027, besselGridState032, besselGridState034, besselGridState037, besselGridState038, besselGridState039, besselGridState040, besselGridState041, besselGridState046, besselGridState048, besselGridState050, besselGridState055, besselGridState059, besselGridState063, besselGridState068, besselGridState071, besselGridState073, besselStateSubset, linearInterval, widenInterval,
    rationalErrorInterval, rationalIntervalSubset, orderedInterval, Finset.sum_range_succ,
    IntervalRat.add, IntervalRat.mul, IntervalRat.scale, IntervalRat.singleton]

theorem compactCertificate220_stateChecks6 :
    compactCertificate220.stateChecks 18 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 32 12 (407089566862411 / 4000000000000)) (orderedInterval (71050536919 / 1000000000000) (71050545933 / 1000000000000), orderedInterval (-35092449226 / 1000000000000) (-35092440212 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 27 12 (345094334222771 / 4000000000000)) (orderedInterval (-67663854350 / 1000000000000) (-67663795229 / 1000000000000), orderedInterval (53313344392 / 1000000000000) (53313403513 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 17 12 (215944011112913 / 4000000000000)) (orderedInterval (-106231872649 / 1000000000000) (-106231872648 / 1000000000000), orderedInterval (-21524841365 / 1000000000000) (-21524841364 / 1000000000000))) = true
  norm_num [besselStateAtRationalPoint, besselIntervalStepZero,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, besselZeroTransition,
    besselInitial, besselGridStateAt, besselGridStateBlock00, besselGridStateBlock01,
    besselGridStateBlock02, besselGridStateBlock03, besselGridStateBlock04,
    besselGridStateBlock05, besselGridStateBlock06, besselGridStateBlock07,
    besselGridStateBlock08, besselGridStateBlock09, besselGridStateBlock10,
    besselGridStateBlock11, besselGridStateBlock12, besselGridStateBlock13,
    besselGridStateBlock14, besselGridState007, besselGridState009, besselGridState014, besselGridState017, besselGridState018, besselGridState023, besselGridState025, besselGridState027, besselGridState032, besselGridState034, besselGridState037, besselGridState038, besselGridState039, besselGridState040, besselGridState041, besselGridState046, besselGridState048, besselGridState050, besselGridState055, besselGridState059, besselGridState063, besselGridState068, besselGridState071, besselGridState073, besselStateSubset, linearInterval, widenInterval,
    rationalErrorInterval, rationalIntervalSubset, orderedInterval, Finset.sum_range_succ,
    IntervalRat.add, IntervalRat.mul, IntervalRat.scale, IntervalRat.singleton]

theorem compactCertificate220_stateChecks7 :
    compactCertificate220.stateChecks 21 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 9 12 (116135407373871 / 4000000000000)) (orderedInterval (-147998646167 / 1000000000000) (-147998646155 / 1000000000000), orderedInterval (-1921069822 / 1000000000000) (-1921069810 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 25 12 (315330222574613 / 4000000000000)) (orderedInterval (-79109222384 / 1000000000000) (-79109222383 / 1000000000000), orderedInterval (-42127320950 / 1000000000000) (-42127320949 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 34 12 (430556460515701 / 4000000000000)) (orderedInterval (76847950965 / 1000000000000) (76847951026 / 1000000000000), orderedInterval (-3309831076 / 1000000000000) (-3309831015 / 1000000000000))) = true
  norm_num [besselStateAtRationalPoint, besselIntervalStepZero,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, besselZeroTransition,
    besselInitial, besselGridStateAt, besselGridStateBlock00, besselGridStateBlock01,
    besselGridStateBlock02, besselGridStateBlock03, besselGridStateBlock04,
    besselGridStateBlock05, besselGridStateBlock06, besselGridStateBlock07,
    besselGridStateBlock08, besselGridStateBlock09, besselGridStateBlock10,
    besselGridStateBlock11, besselGridStateBlock12, besselGridStateBlock13,
    besselGridStateBlock14, besselGridState007, besselGridState009, besselGridState014, besselGridState017, besselGridState018, besselGridState023, besselGridState025, besselGridState027, besselGridState032, besselGridState034, besselGridState037, besselGridState038, besselGridState039, besselGridState040, besselGridState041, besselGridState046, besselGridState048, besselGridState050, besselGridState055, besselGridState059, besselGridState063, besselGridState068, besselGridState071, besselGridState073, besselStateSubset, linearInterval, widenInterval,
    rationalErrorInterval, rationalIntervalSubset, orderedInterval, Finset.sum_range_succ,
    IntervalRat.add, IntervalRat.mul, IntervalRat.scale, IntervalRat.singleton]

theorem compactCertificate220_stateChecks8 :
    compactCertificate220.stateChecks 24 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 14 12 (182055988887087 / 4000000000000)) (orderedInterval (87050440617 / 1000000000000) (87050539611 / 1000000000000), orderedInterval (-81015471860 / 1000000000000) (-81015372867 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 59 12 (740047487379727 / 4000000000000)) (orderedInterval (-25124838659 / 1000000000000) (-25124838658 / 1000000000000), orderedInterval (-52938869093 / 1000000000000) (-52938869092 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 39 12 (494317424761793 / 4000000000000)) (orderedInterval (-69157428814 / 1000000000000) (-69157427422 / 1000000000000), orderedInterval (19481883122 / 1000000000000) (19481884514 / 1000000000000))) = true
  norm_num [besselStateAtRationalPoint, besselIntervalStepZero,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, besselZeroTransition,
    besselInitial, besselGridStateAt, besselGridStateBlock00, besselGridStateBlock01,
    besselGridStateBlock02, besselGridStateBlock03, besselGridStateBlock04,
    besselGridStateBlock05, besselGridStateBlock06, besselGridStateBlock07,
    besselGridStateBlock08, besselGridStateBlock09, besselGridStateBlock10,
    besselGridStateBlock11, besselGridStateBlock12, besselGridStateBlock13,
    besselGridStateBlock14, besselGridState007, besselGridState009, besselGridState014, besselGridState017, besselGridState018, besselGridState023, besselGridState025, besselGridState027, besselGridState032, besselGridState034, besselGridState037, besselGridState038, besselGridState039, besselGridState040, besselGridState041, besselGridState046, besselGridState048, besselGridState050, besselGridState055, besselGridState059, besselGridState063, besselGridState068, besselGridState071, besselGridState073, besselStateSubset, linearInterval, widenInterval,
    rationalErrorInterval, rationalIntervalSubset, orderedInterval, Finset.sum_range_succ,
    IntervalRat.add, IntervalRat.mul, IntervalRat.scale, IntervalRat.singleton]

theorem compactCertificate220_states : ∀ j,
    BesselStateValid (compactCertificate220.point j) (compactCertificate220.state j) :=
  compactCertificate220.statesValid_of_checks3 compactCertificate220_stateChecks0
    compactCertificate220_stateChecks1 compactCertificate220_stateChecks2
    compactCertificate220_stateChecks3 compactCertificate220_stateChecks4
    compactCertificate220_stateChecks5 compactCertificate220_stateChecks6
    compactCertificate220_stateChecks7 compactCertificate220_stateChecks8

theorem compactCertificate220_chunkChecks0_0 :
    compactCertificate220.chunkChecks (0 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 0) <| besselDerivativeNearFromState (199 / 2) 0 (IntervalRat.scale (199 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-19543066524 / 1000000000000) (-19543066276 / 1000000000000), orderedInterval (77663198113 / 1000000000000) (77663198361 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 0) <| besselDerivativeNearFromState (293164998632299 / 4000000000000) 0 (IntervalRat.scale (199 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-90358206787 / 1000000000000) (-90358206000 / 1000000000000), orderedInterval (23450153596 / 1000000000000) (23450154383 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 0) <| besselDerivativeNearFromState (94803537102667 / 800000000000) 0 (IntervalRat.scale (199 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-6715774085 / 1000000000000) (-6715774061 / 1000000000000), orderedInterval (73015071504 / 1000000000000) (73015071528 / 1000000000000)))) (orderedInterval (-8982239901 / 1000000000000) (-8982239787 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 0) <| besselDerivativeNearFromState (85544815436993 / 4000000000000) 0 (IntervalRat.scale (199 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-29970005138 / 1000000000000) (-29970005136 / 1000000000000), orderedInterval (-169232610155 / 1000000000000) (-169232610153 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 0) <| besselDerivativeNearFromState (229785407137421 / 4000000000000) 0 (IntervalRat.scale (199 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (104631517667 / 1000000000000) (104631517787 / 1000000000000), orderedInterval (-12478849449 / 1000000000000) (-12478849329 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 0) <| besselDerivativeNearFromState (623912080005657 / 4000000000000) 0 (IntervalRat.scale (199 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-19915416439 / 1000000000000) (-19915416012 / 1000000000000), orderedInterval (60766921338 / 1000000000000) (60766921765 / 1000000000000)))) (orderedInterval (5561212472 / 1000000000000) (5561212519 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 0) <| besselDerivativeNearFromState (459570814275041 / 4000000000000) 0 (IntervalRat.scale (199 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (39660830969 / 1000000000000) (39660839532 / 1000000000000), orderedInterval (-63164938915 / 1000000000000) (-63164930352 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 0) <| besselDerivativeNearFromState (787482423393893 / 4000000000000) 0 (IntervalRat.scale (199 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (14891852253 / 1000000000000) (14891852418 / 1000000000000), orderedInterval (-54918948681 / 1000000000000) (-54918948516 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 0) <| besselDerivativeNearFromState (580055988887087 / 4000000000000) 0 (IntervalRat.scale (199 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (63574812634 / 1000000000000) (63574812635 / 1000000000000), orderedInterval (18443025508 / 1000000000000) (18443025509 / 1000000000000)))) (orderedInterval (1077153474 / 1000000000000) (1077153486 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate220_chunkChecks0_1 :
    compactCertificate220.chunkChecks (0 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 0) <| besselDerivativeNearFromState (889955055044801 / 4000000000000) 0 (IntervalRat.scale (199 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-11700680896 / 1000000000000) (-11700680895 / 1000000000000), orderedInterval (-52170041783 / 1000000000000) (-52170041782 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 0) <| besselDerivativeNearFromState (513815790596729 / 4000000000000) 0 (IntervalRat.scale (199 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-29543728065 / 1000000000000) (-29543728064 / 1000000000000), orderedInterval (-63784989370 / 1000000000000) (-63784989369 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 0) <| besselDerivativeNearFromState (911775137019661 / 4000000000000) 0 (IntervalRat.scale (199 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (30171934459 / 1000000000000) (30171942112 / 1000000000000), orderedInterval (-43454399694 / 1000000000000) (-43454392041 / 1000000000000)))) (orderedInterval (4179240823 / 1000000000000) (4179241951 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 0) <| besselDerivativeNearFromState (851898605363809 / 4000000000000) 0 (IntervalRat.scale (199 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (7150527176 / 1000000000000) (7150527177 / 1000000000000), orderedInterval (54187076841 / 1000000000000) (54187076842 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 0) <| besselDerivativeNearFromState (607955042197297 / 4000000000000) 0 (IntervalRat.scale (199 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (59455671969 / 1000000000000) (59455679060 / 1000000000000), orderedInterval (-25761288141 / 1000000000000) (-25761281049 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 0) <| besselDerivativeNearFromState (689356221412263 / 4000000000000) 0 (IntervalRat.scale (199 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-20046952242 / 1000000000000) (-20046952241 / 1000000000000), orderedInterval (-57318906124 / 1000000000000) (-57318906123 / 1000000000000)))) (orderedInterval (5594658778 / 1000000000000) (5594659462 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 0) <| besselDerivativeNearFromState (574713348414647 / 4000000000000) 0 (IntervalRat.scale (199 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-3353219572 / 1000000000000) (-3353219561 / 1000000000000), orderedInterval (66492123257 / 1000000000000) (66492123267 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 0) <| besselDerivativeNearFromState (507776672631587 / 4000000000000) 0 (IntervalRat.scale (199 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (62346892800 / 1000000000000) (62346907820 / 1000000000000), orderedInterval (-33828325555 / 1000000000000) (-33828310535 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 0) <| besselDerivativeNearFromState (147173471275113 / 800000000000) 0 (IntervalRat.scale (199 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (33332518163 / 1000000000000) (33332527247 / 1000000000000), orderedInterval (-48561838700 / 1000000000000) (-48561829616 / 1000000000000)))) (orderedInterval (-2753184106 / 1000000000000) (-2753183003 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate220_chunkChecks0_2 :
    compactCertificate220.chunkChecks (0 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 0) <| besselDerivativeNearFromState (407089566862411 / 4000000000000) 0 (IntervalRat.scale (199 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (71050536919 / 1000000000000) (71050545933 / 1000000000000), orderedInterval (-35092449226 / 1000000000000) (-35092440212 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 0) <| besselDerivativeNearFromState (345094334222771 / 4000000000000) 0 (IntervalRat.scale (199 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-67663854350 / 1000000000000) (-67663795229 / 1000000000000), orderedInterval (53313344392 / 1000000000000) (53313403513 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 0) <| besselDerivativeNearFromState (215944011112913 / 4000000000000) 0 (IntervalRat.scale (199 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-106231872649 / 1000000000000) (-106231872648 / 1000000000000), orderedInterval (-21524841365 / 1000000000000) (-21524841364 / 1000000000000)))) (orderedInterval (-10989084878 / 1000000000000) (-10989080064 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 0) <| besselDerivativeNearFromState (116135407373871 / 4000000000000) 0 (IntervalRat.scale (199 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-147998646167 / 1000000000000) (-147998646155 / 1000000000000), orderedInterval (-1921069822 / 1000000000000) (-1921069810 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 0) <| besselDerivativeNearFromState (315330222574613 / 4000000000000) 0 (IntervalRat.scale (199 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-79109222384 / 1000000000000) (-79109222383 / 1000000000000), orderedInterval (-42127320950 / 1000000000000) (-42127320949 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 0) <| besselDerivativeNearFromState (430556460515701 / 4000000000000) 0 (IntervalRat.scale (199 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (76847950965 / 1000000000000) (76847951026 / 1000000000000), orderedInterval (-3309831076 / 1000000000000) (-3309831015 / 1000000000000)))) (orderedInterval (-1361987807 / 1000000000000) (-1361987789 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 0) <| besselDerivativeNearFromState (182055988887087 / 4000000000000) 0 (IntervalRat.scale (199 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (87050440617 / 1000000000000) (87050539611 / 1000000000000), orderedInterval (-81015471860 / 1000000000000) (-81015372867 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 0) <| besselDerivativeNearFromState (740047487379727 / 4000000000000) 0 (IntervalRat.scale (199 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-25124838659 / 1000000000000) (-25124838658 / 1000000000000), orderedInterval (-52938869093 / 1000000000000) (-52938869092 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 0) <| besselDerivativeNearFromState (494317424761793 / 4000000000000) 0 (IntervalRat.scale (199 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-69157428814 / 1000000000000) (-69157427422 / 1000000000000), orderedInterval (19481883122 / 1000000000000) (19481884514 / 1000000000000)))) (orderedInterval (15545743031 / 1000000000000) (15545743918 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate220_chunkChecks0 :
    compactCertificate220.chunkChecks (0 : Fin 5) 0 9 = true :=
  compactCertificate220.chunkChecks_nine_of_three (0 : Fin 5) compactCertificate220_chunkChecks0_0
    compactCertificate220_chunkChecks0_1 compactCertificate220_chunkChecks0_2

theorem compactCertificate220_chunkChecks1_0 :
    compactCertificate220.chunkChecks (1 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 1) <| besselDerivativeNearFromState (199 / 2) 1 (IntervalRat.scale (199 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-19543066524 / 1000000000000) (-19543066276 / 1000000000000), orderedInterval (77663198113 / 1000000000000) (77663198361 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 1) <| besselDerivativeNearFromState (293164998632299 / 4000000000000) 1 (IntervalRat.scale (199 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-90358206787 / 1000000000000) (-90358206000 / 1000000000000), orderedInterval (23450153596 / 1000000000000) (23450154383 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 1) <| besselDerivativeNearFromState (94803537102667 / 800000000000) 1 (IntervalRat.scale (199 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-6715774085 / 1000000000000) (-6715774061 / 1000000000000), orderedInterval (73015071504 / 1000000000000) (73015071528 / 1000000000000)))) (orderedInterval (36046890709 / 1000000000000) (36046890823 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 1) <| besselDerivativeNearFromState (85544815436993 / 4000000000000) 1 (IntervalRat.scale (199 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-29970005138 / 1000000000000) (-29970005136 / 1000000000000), orderedInterval (-169232610155 / 1000000000000) (-169232610153 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 1) <| besselDerivativeNearFromState (229785407137421 / 4000000000000) 1 (IntervalRat.scale (199 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (104631517667 / 1000000000000) (104631517787 / 1000000000000), orderedInterval (-12478849449 / 1000000000000) (-12478849329 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 1) <| besselDerivativeNearFromState (623912080005657 / 4000000000000) 1 (IntervalRat.scale (199 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-19915416439 / 1000000000000) (-19915416012 / 1000000000000), orderedInterval (60766921338 / 1000000000000) (60766921765 / 1000000000000)))) (orderedInterval (-6640371735 / 1000000000000) (-6640371670 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 1) <| besselDerivativeNearFromState (459570814275041 / 4000000000000) 1 (IntervalRat.scale (199 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (39660830969 / 1000000000000) (39660839532 / 1000000000000), orderedInterval (-63164938915 / 1000000000000) (-63164930352 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 1) <| besselDerivativeNearFromState (787482423393893 / 4000000000000) 1 (IntervalRat.scale (199 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (14891852253 / 1000000000000) (14891852418 / 1000000000000), orderedInterval (-54918948681 / 1000000000000) (-54918948516 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 1) <| besselDerivativeNearFromState (580055988887087 / 4000000000000) 1 (IntervalRat.scale (199 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (63574812634 / 1000000000000) (63574812635 / 1000000000000), orderedInterval (18443025508 / 1000000000000) (18443025509 / 1000000000000)))) (orderedInterval (4001209934 / 1000000000000) (4001209955 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate220_chunkChecks1_1 :
    compactCertificate220.chunkChecks (1 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 1) <| besselDerivativeNearFromState (889955055044801 / 4000000000000) 1 (IntervalRat.scale (199 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-11700680896 / 1000000000000) (-11700680895 / 1000000000000), orderedInterval (-52170041783 / 1000000000000) (-52170041782 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 1) <| besselDerivativeNearFromState (513815790596729 / 4000000000000) 1 (IntervalRat.scale (199 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-29543728065 / 1000000000000) (-29543728064 / 1000000000000), orderedInterval (-63784989370 / 1000000000000) (-63784989369 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 1) <| besselDerivativeNearFromState (911775137019661 / 4000000000000) 1 (IntervalRat.scale (199 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (30171934459 / 1000000000000) (30171942112 / 1000000000000), orderedInterval (-43454399694 / 1000000000000) (-43454392041 / 1000000000000)))) (orderedInterval (475627399 / 1000000000000) (475629974 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 1) <| besselDerivativeNearFromState (851898605363809 / 4000000000000) 1 (IntervalRat.scale (199 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (7150527176 / 1000000000000) (7150527177 / 1000000000000), orderedInterval (54187076841 / 1000000000000) (54187076842 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 1) <| besselDerivativeNearFromState (607955042197297 / 4000000000000) 1 (IntervalRat.scale (199 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (59455671969 / 1000000000000) (59455679060 / 1000000000000), orderedInterval (-25761288141 / 1000000000000) (-25761281049 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 1) <| besselDerivativeNearFromState (689356221412263 / 4000000000000) 1 (IntervalRat.scale (199 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-20046952242 / 1000000000000) (-20046952241 / 1000000000000), orderedInterval (-57318906124 / 1000000000000) (-57318906123 / 1000000000000)))) (orderedInterval (-5312615854 / 1000000000000) (-5312614809 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 1) <| besselDerivativeNearFromState (574713348414647 / 4000000000000) 1 (IntervalRat.scale (199 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-3353219572 / 1000000000000) (-3353219561 / 1000000000000), orderedInterval (66492123257 / 1000000000000) (66492123267 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 1) <| besselDerivativeNearFromState (507776672631587 / 4000000000000) 1 (IntervalRat.scale (199 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (62346892800 / 1000000000000) (62346907820 / 1000000000000), orderedInterval (-33828325555 / 1000000000000) (-33828310535 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 1) <| besselDerivativeNearFromState (147173471275113 / 800000000000) 1 (IntervalRat.scale (199 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (33332518163 / 1000000000000) (33332527247 / 1000000000000), orderedInterval (-48561838700 / 1000000000000) (-48561829616 / 1000000000000)))) (orderedInterval (1279694106 / 1000000000000) (1279695648 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate220_chunkChecks1_2 :
    compactCertificate220.chunkChecks (1 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 1) <| besselDerivativeNearFromState (407089566862411 / 4000000000000) 1 (IntervalRat.scale (199 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (71050536919 / 1000000000000) (71050545933 / 1000000000000), orderedInterval (-35092449226 / 1000000000000) (-35092440212 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 1) <| besselDerivativeNearFromState (345094334222771 / 4000000000000) 1 (IntervalRat.scale (199 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-67663854350 / 1000000000000) (-67663795229 / 1000000000000), orderedInterval (53313344392 / 1000000000000) (53313403513 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 1) <| besselDerivativeNearFromState (215944011112913 / 4000000000000) 1 (IntervalRat.scale (199 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-106231872649 / 1000000000000) (-106231872648 / 1000000000000), orderedInterval (-21524841365 / 1000000000000) (-21524841364 / 1000000000000)))) (orderedInterval (2742535797 / 1000000000000) (2742540196 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 1) <| besselDerivativeNearFromState (116135407373871 / 4000000000000) 1 (IntervalRat.scale (199 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-147998646167 / 1000000000000) (-147998646155 / 1000000000000), orderedInterval (-1921069822 / 1000000000000) (-1921069810 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 1) <| besselDerivativeNearFromState (315330222574613 / 4000000000000) 1 (IntervalRat.scale (199 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-79109222384 / 1000000000000) (-79109222383 / 1000000000000), orderedInterval (-42127320950 / 1000000000000) (-42127320949 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 1) <| besselDerivativeNearFromState (430556460515701 / 4000000000000) 1 (IntervalRat.scale (199 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (76847950965 / 1000000000000) (76847951026 / 1000000000000), orderedInterval (-3309831076 / 1000000000000) (-3309831015 / 1000000000000)))) (orderedInterval (1041979906 / 1000000000000) (1041979922 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 1) <| besselDerivativeNearFromState (182055988887087 / 4000000000000) 1 (IntervalRat.scale (199 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (87050440617 / 1000000000000) (87050539611 / 1000000000000), orderedInterval (-81015471860 / 1000000000000) (-81015372867 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 1) <| besselDerivativeNearFromState (740047487379727 / 4000000000000) 1 (IntervalRat.scale (199 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-25124838659 / 1000000000000) (-25124838658 / 1000000000000), orderedInterval (-52938869093 / 1000000000000) (-52938869092 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 1) <| besselDerivativeNearFromState (494317424761793 / 4000000000000) 1 (IntervalRat.scale (199 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-69157428814 / 1000000000000) (-69157427422 / 1000000000000), orderedInterval (19481883122 / 1000000000000) (19481884514 / 1000000000000)))) (orderedInterval (3249493688 / 1000000000000) (3249494325 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate220_chunkChecks1 :
    compactCertificate220.chunkChecks (1 : Fin 5) 0 9 = true :=
  compactCertificate220.chunkChecks_nine_of_three (1 : Fin 5) compactCertificate220_chunkChecks1_0
    compactCertificate220_chunkChecks1_1 compactCertificate220_chunkChecks1_2

theorem compactCertificate220_chunkChecks2_0 :
    compactCertificate220.chunkChecks (2 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 2) <| besselDerivativeNearFromState (199 / 2) 2 (IntervalRat.scale (199 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-19543066524 / 1000000000000) (-19543066276 / 1000000000000), orderedInterval (77663198113 / 1000000000000) (77663198361 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 2) <| besselDerivativeNearFromState (293164998632299 / 4000000000000) 2 (IntervalRat.scale (199 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-90358206787 / 1000000000000) (-90358206000 / 1000000000000), orderedInterval (23450153596 / 1000000000000) (23450154383 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 2) <| besselDerivativeNearFromState (94803537102667 / 800000000000) 2 (IntervalRat.scale (199 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-6715774085 / 1000000000000) (-6715774061 / 1000000000000), orderedInterval (73015071504 / 1000000000000) (73015071528 / 1000000000000)))) (orderedInterval (8399740825 / 1000000000000) (8399740940 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 2) <| besselDerivativeNearFromState (85544815436993 / 4000000000000) 2 (IntervalRat.scale (199 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-29970005138 / 1000000000000) (-29970005136 / 1000000000000), orderedInterval (-169232610155 / 1000000000000) (-169232610153 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 2) <| besselDerivativeNearFromState (229785407137421 / 4000000000000) 2 (IntervalRat.scale (199 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (104631517667 / 1000000000000) (104631517787 / 1000000000000), orderedInterval (-12478849449 / 1000000000000) (-12478849329 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 2) <| besselDerivativeNearFromState (623912080005657 / 4000000000000) 2 (IntervalRat.scale (199 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-19915416439 / 1000000000000) (-19915416012 / 1000000000000), orderedInterval (60766921338 / 1000000000000) (60766921765 / 1000000000000)))) (orderedInterval (-4700886110 / 1000000000000) (-4700886014 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 2) <| besselDerivativeNearFromState (459570814275041 / 4000000000000) 2 (IntervalRat.scale (199 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (39660830969 / 1000000000000) (39660839532 / 1000000000000), orderedInterval (-63164938915 / 1000000000000) (-63164930352 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 2) <| besselDerivativeNearFromState (787482423393893 / 4000000000000) 2 (IntervalRat.scale (199 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (14891852253 / 1000000000000) (14891852418 / 1000000000000), orderedInterval (-54918948681 / 1000000000000) (-54918948516 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 2) <| besselDerivativeNearFromState (580055988887087 / 4000000000000) 2 (IntervalRat.scale (199 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (63574812634 / 1000000000000) (63574812635 / 1000000000000), orderedInterval (18443025508 / 1000000000000) (18443025509 / 1000000000000)))) (orderedInterval (-1505648384 / 1000000000000) (-1505648346 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate220_chunkChecks2_1 :
    compactCertificate220.chunkChecks (2 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 2) <| besselDerivativeNearFromState (889955055044801 / 4000000000000) 2 (IntervalRat.scale (199 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-11700680896 / 1000000000000) (-11700680895 / 1000000000000), orderedInterval (-52170041783 / 1000000000000) (-52170041782 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 2) <| besselDerivativeNearFromState (513815790596729 / 4000000000000) 2 (IntervalRat.scale (199 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-29543728065 / 1000000000000) (-29543728064 / 1000000000000), orderedInterval (-63784989370 / 1000000000000) (-63784989369 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 2) <| besselDerivativeNearFromState (911775137019661 / 4000000000000) 2 (IntervalRat.scale (199 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (30171934459 / 1000000000000) (30171942112 / 1000000000000), orderedInterval (-43454399694 / 1000000000000) (-43454392041 / 1000000000000)))) (orderedInterval (-29261986409 / 1000000000000) (-29261980497 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 2) <| besselDerivativeNearFromState (851898605363809 / 4000000000000) 2 (IntervalRat.scale (199 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (7150527176 / 1000000000000) (7150527177 / 1000000000000), orderedInterval (54187076841 / 1000000000000) (54187076842 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 2) <| besselDerivativeNearFromState (607955042197297 / 4000000000000) 2 (IntervalRat.scale (199 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (59455671969 / 1000000000000) (59455679060 / 1000000000000), orderedInterval (-25761288141 / 1000000000000) (-25761281049 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 2) <| besselDerivativeNearFromState (689356221412263 / 4000000000000) 2 (IntervalRat.scale (199 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-20046952242 / 1000000000000) (-20046952241 / 1000000000000), orderedInterval (-57318906124 / 1000000000000) (-57318906123 / 1000000000000)))) (orderedInterval (-12778228581 / 1000000000000) (-12778226974 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 2) <| besselDerivativeNearFromState (574713348414647 / 4000000000000) 2 (IntervalRat.scale (199 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-3353219572 / 1000000000000) (-3353219561 / 1000000000000), orderedInterval (66492123257 / 1000000000000) (66492123267 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 2) <| besselDerivativeNearFromState (507776672631587 / 4000000000000) 2 (IntervalRat.scale (199 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (62346892800 / 1000000000000) (62346907820 / 1000000000000), orderedInterval (-33828325555 / 1000000000000) (-33828310535 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 2) <| besselDerivativeNearFromState (147173471275113 / 800000000000) 2 (IntervalRat.scale (199 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (33332518163 / 1000000000000) (33332527247 / 1000000000000), orderedInterval (-48561838700 / 1000000000000) (-48561829616 / 1000000000000)))) (orderedInterval (2957944163 / 1000000000000) (2957946395 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate220_chunkChecks2_2 :
    compactCertificate220.chunkChecks (2 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 2) <| besselDerivativeNearFromState (407089566862411 / 4000000000000) 2 (IntervalRat.scale (199 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (71050536919 / 1000000000000) (71050545933 / 1000000000000), orderedInterval (-35092449226 / 1000000000000) (-35092440212 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 2) <| besselDerivativeNearFromState (345094334222771 / 4000000000000) 2 (IntervalRat.scale (199 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-67663854350 / 1000000000000) (-67663795229 / 1000000000000), orderedInterval (53313344392 / 1000000000000) (53313403513 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 2) <| besselDerivativeNearFromState (215944011112913 / 4000000000000) 2 (IntervalRat.scale (199 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-106231872649 / 1000000000000) (-106231872648 / 1000000000000), orderedInterval (-21524841365 / 1000000000000) (-21524841364 / 1000000000000)))) (orderedInterval (9996542869 / 1000000000000) (9996546959 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 2) <| besselDerivativeNearFromState (116135407373871 / 4000000000000) 2 (IntervalRat.scale (199 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-147998646167 / 1000000000000) (-147998646155 / 1000000000000), orderedInterval (-1921069822 / 1000000000000) (-1921069810 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 2) <| besselDerivativeNearFromState (315330222574613 / 4000000000000) 2 (IntervalRat.scale (199 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-79109222384 / 1000000000000) (-79109222383 / 1000000000000), orderedInterval (-42127320950 / 1000000000000) (-42127320949 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 2) <| besselDerivativeNearFromState (430556460515701 / 4000000000000) 2 (IntervalRat.scale (199 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (76847950965 / 1000000000000) (76847951026 / 1000000000000), orderedInterval (-3309831076 / 1000000000000) (-3309831015 / 1000000000000)))) (orderedInterval (5522727713 / 1000000000000) (5522727730 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 2) <| besselDerivativeNearFromState (182055988887087 / 4000000000000) 2 (IntervalRat.scale (199 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (87050440617 / 1000000000000) (87050539611 / 1000000000000), orderedInterval (-81015471860 / 1000000000000) (-81015372867 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 2) <| besselDerivativeNearFromState (740047487379727 / 4000000000000) 2 (IntervalRat.scale (199 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-25124838659 / 1000000000000) (-25124838658 / 1000000000000), orderedInterval (-52938869093 / 1000000000000) (-52938869092 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 2) <| besselDerivativeNearFromState (494317424761793 / 4000000000000) 2 (IntervalRat.scale (199 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-69157428814 / 1000000000000) (-69157427422 / 1000000000000), orderedInterval (19481883122 / 1000000000000) (19481884514 / 1000000000000)))) (orderedInterval (-27229681439 / 1000000000000) (-27229680847 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate220_chunkChecks2 :
    compactCertificate220.chunkChecks (2 : Fin 5) 0 9 = true :=
  compactCertificate220.chunkChecks_nine_of_three (2 : Fin 5) compactCertificate220_chunkChecks2_0
    compactCertificate220_chunkChecks2_1 compactCertificate220_chunkChecks2_2

theorem compactCertificate220_chunkChecks3_0 :
    compactCertificate220.chunkChecks (3 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 3) <| besselDerivativeNearFromState (199 / 2) 3 (IntervalRat.scale (199 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-19543066524 / 1000000000000) (-19543066276 / 1000000000000), orderedInterval (77663198113 / 1000000000000) (77663198361 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 3) <| besselDerivativeNearFromState (293164998632299 / 4000000000000) 3 (IntervalRat.scale (199 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-90358206787 / 1000000000000) (-90358206000 / 1000000000000), orderedInterval (23450153596 / 1000000000000) (23450154383 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 3) <| besselDerivativeNearFromState (94803537102667 / 800000000000) 3 (IntervalRat.scale (199 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-6715774085 / 1000000000000) (-6715774061 / 1000000000000), orderedInterval (73015071504 / 1000000000000) (73015071528 / 1000000000000)))) (orderedInterval (-38189528859 / 1000000000000) (-38189528744 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 3) <| besselDerivativeNearFromState (85544815436993 / 4000000000000) 3 (IntervalRat.scale (199 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-29970005138 / 1000000000000) (-29970005136 / 1000000000000), orderedInterval (-169232610155 / 1000000000000) (-169232610153 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 3) <| besselDerivativeNearFromState (229785407137421 / 4000000000000) 3 (IntervalRat.scale (199 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (104631517667 / 1000000000000) (104631517787 / 1000000000000), orderedInterval (-12478849449 / 1000000000000) (-12478849329 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 3) <| besselDerivativeNearFromState (623912080005657 / 4000000000000) 3 (IntervalRat.scale (199 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-19915416439 / 1000000000000) (-19915416012 / 1000000000000), orderedInterval (60766921338 / 1000000000000) (60766921765 / 1000000000000)))) (orderedInterval (16757606708 / 1000000000000) (16757606855 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 3) <| besselDerivativeNearFromState (459570814275041 / 4000000000000) 3 (IntervalRat.scale (199 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (39660830969 / 1000000000000) (39660839532 / 1000000000000), orderedInterval (-63164938915 / 1000000000000) (-63164930352 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 3) <| besselDerivativeNearFromState (787482423393893 / 4000000000000) 3 (IntervalRat.scale (199 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (14891852253 / 1000000000000) (14891852418 / 1000000000000), orderedInterval (-54918948681 / 1000000000000) (-54918948516 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 3) <| besselDerivativeNearFromState (580055988887087 / 4000000000000) 3 (IntervalRat.scale (199 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (63574812634 / 1000000000000) (63574812635 / 1000000000000), orderedInterval (18443025508 / 1000000000000) (18443025509 / 1000000000000)))) (orderedInterval (-14485301364 / 1000000000000) (-14485301292 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate220_chunkChecks3_1 :
    compactCertificate220.chunkChecks (3 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 3) <| besselDerivativeNearFromState (889955055044801 / 4000000000000) 3 (IntervalRat.scale (199 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-11700680896 / 1000000000000) (-11700680895 / 1000000000000), orderedInterval (-52170041783 / 1000000000000) (-52170041782 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 3) <| besselDerivativeNearFromState (513815790596729 / 4000000000000) 3 (IntervalRat.scale (199 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-29543728065 / 1000000000000) (-29543728064 / 1000000000000), orderedInterval (-63784989370 / 1000000000000) (-63784989369 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 3) <| besselDerivativeNearFromState (911775137019661 / 4000000000000) 3 (IntervalRat.scale (199 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (30171934459 / 1000000000000) (30171942112 / 1000000000000), orderedInterval (-43454399694 / 1000000000000) (-43454392041 / 1000000000000)))) (orderedInterval (-18908999314 / 1000000000000) (-18908985790 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 3) <| besselDerivativeNearFromState (851898605363809 / 4000000000000) 3 (IntervalRat.scale (199 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (7150527176 / 1000000000000) (7150527177 / 1000000000000), orderedInterval (54187076841 / 1000000000000) (54187076842 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 3) <| besselDerivativeNearFromState (607955042197297 / 4000000000000) 3 (IntervalRat.scale (199 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (59455671969 / 1000000000000) (59455679060 / 1000000000000), orderedInterval (-25761288141 / 1000000000000) (-25761281049 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 3) <| besselDerivativeNearFromState (689356221412263 / 4000000000000) 3 (IntervalRat.scale (199 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-20046952242 / 1000000000000) (-20046952241 / 1000000000000), orderedInterval (-57318906124 / 1000000000000) (-57318906123 / 1000000000000)))) (orderedInterval (16896486182 / 1000000000000) (16896488643 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 3) <| besselDerivativeNearFromState (574713348414647 / 4000000000000) 3 (IntervalRat.scale (199 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-3353219572 / 1000000000000) (-3353219561 / 1000000000000), orderedInterval (66492123257 / 1000000000000) (66492123267 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 3) <| besselDerivativeNearFromState (507776672631587 / 4000000000000) 3 (IntervalRat.scale (199 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (62346892800 / 1000000000000) (62346907820 / 1000000000000), orderedInterval (-33828325555 / 1000000000000) (-33828310535 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 3) <| besselDerivativeNearFromState (147173471275113 / 800000000000) 3 (IntervalRat.scale (199 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (33332518163 / 1000000000000) (33332527247 / 1000000000000), orderedInterval (-48561838700 / 1000000000000) (-48561829616 / 1000000000000)))) (orderedInterval (1497009316 / 1000000000000) (1497012625 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate220_chunkChecks3_2 :
    compactCertificate220.chunkChecks (3 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 3) <| besselDerivativeNearFromState (407089566862411 / 4000000000000) 3 (IntervalRat.scale (199 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (71050536919 / 1000000000000) (71050545933 / 1000000000000), orderedInterval (-35092449226 / 1000000000000) (-35092440212 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 3) <| besselDerivativeNearFromState (345094334222771 / 4000000000000) 3 (IntervalRat.scale (199 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-67663854350 / 1000000000000) (-67663795229 / 1000000000000), orderedInterval (53313344392 / 1000000000000) (53313403513 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 3) <| besselDerivativeNearFromState (215944011112913 / 4000000000000) 3 (IntervalRat.scale (199 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-106231872649 / 1000000000000) (-106231872648 / 1000000000000), orderedInterval (-21524841365 / 1000000000000) (-21524841364 / 1000000000000)))) (orderedInterval (-4025508652 / 1000000000000) (-4025504867 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 3) <| besselDerivativeNearFromState (116135407373871 / 4000000000000) 3 (IntervalRat.scale (199 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-147998646167 / 1000000000000) (-147998646155 / 1000000000000), orderedInterval (-1921069822 / 1000000000000) (-1921069810 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 3) <| besselDerivativeNearFromState (315330222574613 / 4000000000000) 3 (IntervalRat.scale (199 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-79109222384 / 1000000000000) (-79109222383 / 1000000000000), orderedInterval (-42127320950 / 1000000000000) (-42127320949 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 3) <| besselDerivativeNearFromState (430556460515701 / 4000000000000) 3 (IntervalRat.scale (199 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (76847950965 / 1000000000000) (76847951026 / 1000000000000), orderedInterval (-3309831076 / 1000000000000) (-3309831015 / 1000000000000)))) (orderedInterval (-852741835 / 1000000000000) (-852741817 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 3) <| besselDerivativeNearFromState (182055988887087 / 4000000000000) 3 (IntervalRat.scale (199 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (87050440617 / 1000000000000) (87050539611 / 1000000000000), orderedInterval (-81015471860 / 1000000000000) (-81015372867 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 3) <| besselDerivativeNearFromState (740047487379727 / 4000000000000) 3 (IntervalRat.scale (199 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-25124838659 / 1000000000000) (-25124838658 / 1000000000000), orderedInterval (-52938869093 / 1000000000000) (-52938869092 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 3) <| besselDerivativeNearFromState (494317424761793 / 4000000000000) 3 (IntervalRat.scale (199 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-69157428814 / 1000000000000) (-69157427422 / 1000000000000), orderedInterval (19481883122 / 1000000000000) (19481884514 / 1000000000000)))) (orderedInterval (-20379827925 / 1000000000000) (-20379827273 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate220_chunkChecks3 :
    compactCertificate220.chunkChecks (3 : Fin 5) 0 9 = true :=
  compactCertificate220.chunkChecks_nine_of_three (3 : Fin 5) compactCertificate220_chunkChecks3_0
    compactCertificate220_chunkChecks3_1 compactCertificate220_chunkChecks3_2

theorem compactCertificate220_chunkChecks4_0 :
    compactCertificate220.chunkChecks (4 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 4) <| besselDerivativeNearFromState (199 / 2) 4 (IntervalRat.scale (199 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-19543066524 / 1000000000000) (-19543066276 / 1000000000000), orderedInterval (77663198113 / 1000000000000) (77663198361 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 4) <| besselDerivativeNearFromState (293164998632299 / 4000000000000) 4 (IntervalRat.scale (199 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-90358206787 / 1000000000000) (-90358206000 / 1000000000000), orderedInterval (23450153596 / 1000000000000) (23450154383 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 4) <| besselDerivativeNearFromState (94803537102667 / 800000000000) 4 (IntervalRat.scale (199 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-6715774085 / 1000000000000) (-6715774061 / 1000000000000), orderedInterval (73015071504 / 1000000000000) (73015071528 / 1000000000000)))) (orderedInterval (-8018548836 / 1000000000000) (-8018548717 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 4) <| besselDerivativeNearFromState (85544815436993 / 4000000000000) 4 (IntervalRat.scale (199 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-29970005138 / 1000000000000) (-29970005136 / 1000000000000), orderedInterval (-169232610155 / 1000000000000) (-169232610153 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 4) <| besselDerivativeNearFromState (229785407137421 / 4000000000000) 4 (IntervalRat.scale (199 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (104631517667 / 1000000000000) (104631517787 / 1000000000000), orderedInterval (-12478849449 / 1000000000000) (-12478849329 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 4) <| besselDerivativeNearFromState (623912080005657 / 4000000000000) 4 (IntervalRat.scale (199 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-19915416439 / 1000000000000) (-19915416012 / 1000000000000), orderedInterval (60766921338 / 1000000000000) (60766921765 / 1000000000000)))) (orderedInterval (8637685442 / 1000000000000) (8637685673 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 4) <| besselDerivativeNearFromState (459570814275041 / 4000000000000) 4 (IntervalRat.scale (199 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (39660830969 / 1000000000000) (39660839532 / 1000000000000), orderedInterval (-63164938915 / 1000000000000) (-63164930352 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 4) <| besselDerivativeNearFromState (787482423393893 / 4000000000000) 4 (IntervalRat.scale (199 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (14891852253 / 1000000000000) (14891852418 / 1000000000000), orderedInterval (-54918948681 / 1000000000000) (-54918948516 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 4) <| besselDerivativeNearFromState (580055988887087 / 4000000000000) 4 (IntervalRat.scale (199 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (63574812634 / 1000000000000) (63574812635 / 1000000000000), orderedInterval (18443025508 / 1000000000000) (18443025509 / 1000000000000)))) (orderedInterval (183604001 / 1000000000000) (183604138 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate220_chunkChecks4_1 :
    compactCertificate220.chunkChecks (4 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 4) <| besselDerivativeNearFromState (889955055044801 / 4000000000000) 4 (IntervalRat.scale (199 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-11700680896 / 1000000000000) (-11700680895 / 1000000000000), orderedInterval (-52170041783 / 1000000000000) (-52170041782 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 4) <| besselDerivativeNearFromState (513815790596729 / 4000000000000) 4 (IntervalRat.scale (199 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-29543728065 / 1000000000000) (-29543728064 / 1000000000000), orderedInterval (-63784989370 / 1000000000000) (-63784989369 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 4) <| besselDerivativeNearFromState (911775137019661 / 4000000000000) 4 (IntervalRat.scale (199 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (30171934459 / 1000000000000) (30171942112 / 1000000000000), orderedInterval (-43454399694 / 1000000000000) (-43454392041 / 1000000000000)))) (orderedInterval (164410668799 / 1000000000000) (164410699884 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 4) <| besselDerivativeNearFromState (851898605363809 / 4000000000000) 4 (IntervalRat.scale (199 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (7150527176 / 1000000000000) (7150527177 / 1000000000000), orderedInterval (54187076841 / 1000000000000) (54187076842 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 4) <| besselDerivativeNearFromState (607955042197297 / 4000000000000) 4 (IntervalRat.scale (199 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (59455671969 / 1000000000000) (59455679060 / 1000000000000), orderedInterval (-25761288141 / 1000000000000) (-25761281049 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 4) <| besselDerivativeNearFromState (689356221412263 / 4000000000000) 4 (IntervalRat.scale (199 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-20046952242 / 1000000000000) (-20046952241 / 1000000000000), orderedInterval (-57318906124 / 1000000000000) (-57318906123 / 1000000000000)))) (orderedInterval (28472799117 / 1000000000000) (28472802910 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 4) <| besselDerivativeNearFromState (574713348414647 / 4000000000000) 4 (IntervalRat.scale (199 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-3353219572 / 1000000000000) (-3353219561 / 1000000000000), orderedInterval (66492123257 / 1000000000000) (66492123267 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 4) <| besselDerivativeNearFromState (507776672631587 / 4000000000000) 4 (IntervalRat.scale (199 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (62346892800 / 1000000000000) (62346907820 / 1000000000000), orderedInterval (-33828325555 / 1000000000000) (-33828310535 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 4) <| besselDerivativeNearFromState (147173471275113 / 800000000000) 4 (IntervalRat.scale (199 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (33332518163 / 1000000000000) (33332527247 / 1000000000000), orderedInterval (-48561838700 / 1000000000000) (-48561829616 / 1000000000000)))) (orderedInterval (322144110 / 1000000000000) (322149222 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate220_chunkChecks4_2 :
    compactCertificate220.chunkChecks (4 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 4) <| besselDerivativeNearFromState (407089566862411 / 4000000000000) 4 (IntervalRat.scale (199 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (71050536919 / 1000000000000) (71050545933 / 1000000000000), orderedInterval (-35092449226 / 1000000000000) (-35092440212 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 4) <| besselDerivativeNearFromState (345094334222771 / 4000000000000) 4 (IntervalRat.scale (199 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-67663854350 / 1000000000000) (-67663795229 / 1000000000000), orderedInterval (53313344392 / 1000000000000) (53313403513 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 4) <| besselDerivativeNearFromState (215944011112913 / 4000000000000) 4 (IntervalRat.scale (199 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-106231872649 / 1000000000000) (-106231872648 / 1000000000000), orderedInterval (-21524841365 / 1000000000000) (-21524841364 / 1000000000000)))) (orderedInterval (-10487470742 / 1000000000000) (-10487467177 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 4) <| besselDerivativeNearFromState (116135407373871 / 4000000000000) 4 (IntervalRat.scale (199 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-147998646167 / 1000000000000) (-147998646155 / 1000000000000), orderedInterval (-1921069822 / 1000000000000) (-1921069810 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 4) <| besselDerivativeNearFromState (315330222574613 / 4000000000000) 4 (IntervalRat.scale (199 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-79109222384 / 1000000000000) (-79109222383 / 1000000000000), orderedInterval (-42127320950 / 1000000000000) (-42127320949 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 4) <| besselDerivativeNearFromState (430556460515701 / 4000000000000) 4 (IntervalRat.scale (199 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (76847950965 / 1000000000000) (76847951026 / 1000000000000), orderedInterval (-3309831076 / 1000000000000) (-3309831015 / 1000000000000)))) (orderedInterval (-7321517850 / 1000000000000) (-7321517831 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 4) <| besselDerivativeNearFromState (182055988887087 / 4000000000000) 4 (IntervalRat.scale (199 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (87050440617 / 1000000000000) (87050539611 / 1000000000000), orderedInterval (-81015471860 / 1000000000000) (-81015372867 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 4) <| besselDerivativeNearFromState (740047487379727 / 4000000000000) 4 (IntervalRat.scale (199 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-25124838659 / 1000000000000) (-25124838658 / 1000000000000), orderedInterval (-52938869093 / 1000000000000) (-52938869092 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 4) <| besselDerivativeNearFromState (494317424761793 / 4000000000000) 4 (IntervalRat.scale (199 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-69157428814 / 1000000000000) (-69157427422 / 1000000000000), orderedInterval (19481883122 / 1000000000000) (19481884514 / 1000000000000)))) (orderedInterval (55754103808 / 1000000000000) (55754104610 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate220_chunkChecks4 :
    compactCertificate220.chunkChecks (4 : Fin 5) 0 9 = true :=
  compactCertificate220.chunkChecks_nine_of_three (4 : Fin 5) compactCertificate220_chunkChecks4_0
    compactCertificate220_chunkChecks4_1 compactCertificate220_chunkChecks4_2

theorem compactCertificate220_chunks :
    ∀ r : Fin 5, ∀ b, compactCertificate220.chunkCheck r b = true :=
  compactCertificate220.chunkChecks_all (by
    intro r
    fin_cases r
    · exact compactCertificate220_chunkChecks0
    · exact compactCertificate220_chunkChecks1
    · exact compactCertificate220_chunkChecks2
    · exact compactCertificate220_chunkChecks3
    · exact compactCertificate220_chunkChecks4)

theorem compactCertificate220_coefficient0 :
    compactCertificate220.coefficientCheck (0 : Fin 5) = true := by
  norm_num [CompactCertificate.coefficientCheck, intervalFinSumHull,
    compactCertificate220, rationalIntervalSubset, orderedInterval, Fin.sum_univ_succ]

theorem compactCertificate220_coefficient1 :
    compactCertificate220.coefficientCheck (1 : Fin 5) = true := by
  norm_num [CompactCertificate.coefficientCheck, intervalFinSumHull,
    compactCertificate220, rationalIntervalSubset, orderedInterval, Fin.sum_univ_succ]

theorem compactCertificate220_coefficient2 :
    compactCertificate220.coefficientCheck (2 : Fin 5) = true := by
  norm_num [CompactCertificate.coefficientCheck, intervalFinSumHull,
    compactCertificate220, rationalIntervalSubset, orderedInterval, Fin.sum_univ_succ]

theorem compactCertificate220_coefficient3 :
    compactCertificate220.coefficientCheck (3 : Fin 5) = true := by
  norm_num [CompactCertificate.coefficientCheck, intervalFinSumHull,
    compactCertificate220, rationalIntervalSubset, orderedInterval, Fin.sum_univ_succ]

theorem compactCertificate220_coefficient4 :
    compactCertificate220.coefficientCheck (4 : Fin 5) = true := by
  norm_num [CompactCertificate.coefficientCheck, intervalFinSumHull,
    compactCertificate220, rationalIntervalSubset, orderedInterval, Fin.sum_univ_succ]

theorem compactCertificate220_coefficients : ∀ r : Fin 5,
    compactCertificate220.coefficientCheck r = true := by
  intro r
  fin_cases r
  · exact compactCertificate220_coefficient0
  · exact compactCertificate220_coefficient1
  · exact compactCertificate220_coefficient2
  · exact compactCertificate220_coefficient3
  · exact compactCertificate220_coefficient4

theorem compactCertificate220_lower : (1 : ℚ) ≤ compactCertificate220.output.lo := by
  norm_num [CompactCertificate.output, CompactCertificate.interval,
    CompactCertificate.coefficientTargetNat, compactCertificate220, dualConstant,
    intervalTaylorSum, intervalPow, intervalSub, intervalMaxAbs, widenInterval,
    rationalErrorInterval, orderedInterval, IntervalRat.add, IntervalRat.mul, IntervalRat.scale,
    IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4]

theorem compactCertificate220_proves {t : ℝ} (ht : t ∈ compactCertificate220.interval) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t :=
  compactCertificate220.proves compactCertificate220_states compactCertificate220_chunks
    compactCertificate220_coefficients compactCertificate220_lower ht

end Erdos232
