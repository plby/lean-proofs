/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, OpenAI Codex
-/
import ErdosProblems.Erdos232.CompactBase

open LeanCert.Core
namespace Erdos232

def compactCertificate242 : CompactCertificate where
  left := 235 / 2
  right := 118
  center := 471 / 4
  grid := fun i =>
    match i.val with
    | 0 => 38
    | 1 => 28
    | 2 => 45
    | 3 => 8
    | 4 => 22
    | 5 => 59
    | 6 => 43
    | 7 => 74
    | 8 => 55
    | 9 => 84
    | 10 => 48
    | 11 => 86
    | 12 => 80
    | 13 => 57
    | 14 => 65
    | 15 => 54
    | 16 => 48
    | 17 => 69
    | 18 => 38
    | 19 => 33
    | 20 => 20
    | 21 => 11
    | 22 => 30
    | 23 => 41
    | 24 => 17
    | 25 => 70
    | _ => 47
  point := fun i =>
    match i.val with
    | 0 => 471 / 4
    | 1 => 693872936461371 / 8000000000000
    | 2 => 224384251132443 / 1600000000000
    | 3 => 202470392315697 / 8000000000000
    | 4 => 543863953576509 / 8000000000000
    | 5 => 1476696430566153 / 8000000000000
    | 6 => 1087727907153489 / 8000000000000
    | 7 => 1863840308635797 / 8000000000000
    | 8 => 1372896335506623 / 8000000000000
    | 9 => 2106376034804529 / 8000000000000
    | 10 => 1216116770708841 / 8000000000000
    | 11 => 2158020550433469 / 8000000000000
    | 12 => 2016302729278161 / 8000000000000
    | 13 => 1438928768215713 / 8000000000000
    | 14 => 1631591860729527 / 8000000000000
    | 15 => 1360251191473863 / 8000000000000
    | 16 => 1201823179947123 / 8000000000000
    | 17 => 348335200857177 / 1600000000000
    | 18 => 963513497448219 / 8000000000000
    | 19 => 816781062406659 / 8000000000000
    | 20 => 511103664493377 / 8000000000000
    | 21 => 274873250618559 / 8000000000000
    | 22 => 746334345892677 / 8000000000000
    | 23 => 1019055743230629 / 8000000000000
    | 24 => 430896335506623 / 8000000000000
    | 25 => 1751569681185183 / 8000000000000
    | _ => 1169967372174897 / 8000000000000
  state := fun i =>
    match i.val with
    | 0 => (orderedInterval (-55055247493 / 1000000000000) (-55055134397 / 1000000000000), orderedInterval (48972377235 / 1000000000000) (48972490332 / 1000000000000))
    | 1 => (orderedInterval (-36995917054 / 1000000000000) (-36995914106 / 1000000000000), orderedInterval (77487314554 / 1000000000000) (77487317501 / 1000000000000))
    | 2 => (orderedInterval (22913315189 / 1000000000000) (22913315874 / 1000000000000), orderedInterval (-63441767793 / 1000000000000) (-63441767108 / 1000000000000))
    | 3 => (orderedInterval (129594261474 / 1000000000000) (129594261475 / 1000000000000), orderedInterval (88861590651 / 1000000000000) (88861590652 / 1000000000000))
    | 4 => (orderedInterval (-33043910842 / 1000000000000) (-33043909771 / 1000000000000), orderedInterval (91197354480 / 1000000000000) (91197355552 / 1000000000000))
    | 5 => (orderedInterval (-1045771554 / 1000000000000) (-1045771551 / 1000000000000), orderedInterval (-58715182985 / 1000000000000) (-58715182982 / 1000000000000))
    | 6 => (orderedInterval (-68142075508 / 1000000000000) (-68142075351 / 1000000000000), orderedInterval (6481561522 / 1000000000000) (6481561679 / 1000000000000))
    | 7 => (orderedInterval (50183010574 / 1000000000000) (50183010575 / 1000000000000), orderedInterval (14526780268 / 1000000000000) (14526780270 / 1000000000000))
    | 8 => (orderedInterval (23205833286 / 1000000000000) (23205834248 / 1000000000000), orderedInterval (-56380536569 / 1000000000000) (-56380535607 / 1000000000000))
    | 9 => (orderedInterval (9196950030 / 1000000000000) (9196950031 / 1000000000000), orderedInterval (48286749915 / 1000000000000) (48286749916 / 1000000000000))
    | 10 => (orderedInterval (58770397584 / 1000000000000) (58770406800 / 1000000000000), orderedInterval (-27284097554 / 1000000000000) (-27284088338 / 1000000000000))
    | 11 => (orderedInterval (17137796738 / 1000000000000) (17137796739 / 1000000000000), orderedInterval (45424946947 / 1000000000000) (45424946948 / 1000000000000))
    | 12 => (orderedInterval (50115137790 / 1000000000000) (50115137823 / 1000000000000), orderedInterval (3689734867 / 1000000000000) (3689734900 / 1000000000000))
    | 13 => (orderedInterval (-59490292231 / 1000000000000) (-59490292163 / 1000000000000), orderedInterval (713989364 / 1000000000000) (713989431 / 1000000000000))
    | 14 => (orderedInterval (-28255973289 / 1000000000000) (-28255973288 / 1000000000000), orderedInterval (-48128968335 / 1000000000000) (-48128968334 / 1000000000000))
    | 15 => (orderedInterval (56341364652 / 1000000000000) (56341364653 / 1000000000000), orderedInterval (23704178006 / 1000000000000) (23704178007 / 1000000000000))
    | 16 => (orderedInterval (13952984279 / 1000000000000) (13952984280 / 1000000000000), orderedInterval (63538378183 / 1000000000000) (63538378184 / 1000000000000))
    | 17 => (orderedInterval (-53438593604 / 1000000000000) (-53438593001 / 1000000000000), orderedInterval (8398006473 / 1000000000000) (8398007076 / 1000000000000))
    | 18 => (orderedInterval (70025923689 / 1000000000000) (70025925078 / 1000000000000), orderedInterval (-19839368376 / 1000000000000) (-19839366987 / 1000000000000))
    | 19 => (orderedInterval (56134073787 / 1000000000000) (56134149559 / 1000000000000), orderedInterval (-55811969255 / 1000000000000) (-55811893483 / 1000000000000))
    | 20 => (orderedInterval (96238208621 / 1000000000000) (96238209583 / 1000000000000), orderedInterval (-27259239855 / 1000000000000) (-27259238893 / 1000000000000))
    | 21 => (orderedInterval (-74979074979 / 1000000000000) (-74979074978 / 1000000000000), orderedInterval (-112519405524 / 1000000000000) (-112519405523 / 1000000000000))
    | 22 => (orderedInterval (-14132538535 / 1000000000000) (-14132538442 / 1000000000000), orderedInterval (81465709573 / 1000000000000) (81465709665 / 1000000000000))
    | 23 => (orderedInterval (42156700887 / 1000000000000) (42156718050 / 1000000000000), orderedInterval (-56915331966 / 1000000000000) (-56915314802 / 1000000000000))
    | 24 => (orderedInterval (-102751628195 / 1000000000000) (-102751628194 / 1000000000000), orderedInterval (-34558966864 / 1000000000000) (-34558966862 / 1000000000000))
    | 25 => (orderedInterval (-9677523716 / 1000000000000) (-9677523674 / 1000000000000), orderedInterval (53069309199 / 1000000000000) (53069309241 / 1000000000000))
    | _ => (orderedInterval (38570682413 / 1000000000000) (38570696032 / 1000000000000), orderedInterval (-53661184564 / 1000000000000) (-53661170946 / 1000000000000))
  chunkTarget := fun r b =>
    match r.val with
    | 0 =>
      match b.val with
      | 0 => orderedInterval (-20822123510 / 1000000000000) (-20822078606 / 1000000000000)
      | 1 => orderedInterval (-2538153218 / 1000000000000) (-2538153163 / 1000000000000)
      | 2 => orderedInterval (-987005627 / 1000000000000) (-987005596 / 1000000000000)
      | 3 => orderedInterval (5156454621 / 1000000000000) (5156455352 / 1000000000000)
      | 4 => orderedInterval (-6387313933 / 1000000000000) (-6387313911 / 1000000000000)
      | 5 => orderedInterval (-1516110523 / 1000000000000) (-1516110495 / 1000000000000)
      | 6 => orderedInterval (-11240745612 / 1000000000000) (-11240741040 / 1000000000000)
      | 7 => orderedInterval (-1525722900 / 1000000000000) (-1525721568 / 1000000000000)
      | _ => orderedInterval (-7068538650 / 1000000000000) (-7068536058 / 1000000000000)
    | 1 =>
      match b.val with
      | 0 => orderedInterval (15508887200 / 1000000000000) (15508932106 / 1000000000000)
      | 1 => orderedInterval (8258532412 / 1000000000000) (8258532452 / 1000000000000)
      | 2 => orderedInterval (-2872438465 / 1000000000000) (-2872438419 / 1000000000000)
      | 3 => orderedInterval (-7001919350 / 1000000000000) (-7001918370 / 1000000000000)
      | 4 => orderedInterval (382414895 / 1000000000000) (382414930 / 1000000000000)
      | 5 => orderedInterval (-3846178109 / 1000000000000) (-3846178064 / 1000000000000)
      | 6 => orderedInterval (5502149709 / 1000000000000) (5502153700 / 1000000000000)
      | 7 => orderedInterval (3860688715 / 1000000000000) (3860690154 / 1000000000000)
      | _ => orderedInterval (4376959421 / 1000000000000) (4376962648 / 1000000000000)
    | 2 =>
      match b.val with
      | 0 => orderedInterval (19970000573 / 1000000000000) (19970045865 / 1000000000000)
      | 1 => orderedInterval (214288023 / 1000000000000) (214288060 / 1000000000000)
      | 2 => orderedInterval (4892706108 / 1000000000000) (4892706179 / 1000000000000)
      | 3 => orderedInterval (-11812778194 / 1000000000000) (-11812776839 / 1000000000000)
      | 4 => orderedInterval (16839166328 / 1000000000000) (16839166385 / 1000000000000)
      | 5 => orderedInterval (4653046357 / 1000000000000) (4653046436 / 1000000000000)
      | 6 => orderedInterval (13133468310 / 1000000000000) (13133471836 / 1000000000000)
      | 7 => orderedInterval (3429094743 / 1000000000000) (3429096309 / 1000000000000)
      | _ => orderedInterval (8532206261 / 1000000000000) (8532210310 / 1000000000000)
    | 3 =>
      match b.val with
      | 0 => orderedInterval (-13578638195 / 1000000000000) (-13578592900 / 1000000000000)
      | 1 => orderedInterval (-16712157985 / 1000000000000) (-16712157943 / 1000000000000)
      | 2 => orderedInterval (7647148812 / 1000000000000) (7647148923 / 1000000000000)
      | 3 => orderedInterval (22738639456 / 1000000000000) (22738641394 / 1000000000000)
      | 4 => orderedInterval (-995979628 / 1000000000000) (-995979534 / 1000000000000)
      | 5 => orderedInterval (5327967799 / 1000000000000) (5327967936 / 1000000000000)
      | 6 => orderedInterval (-5423143306 / 1000000000000) (-5423140212 / 1000000000000)
      | 7 => orderedInterval (-4683585444 / 1000000000000) (-4683583751 / 1000000000000)
      | _ => orderedInterval (8430184955 / 1000000000000) (8430190011 / 1000000000000)
    | _ =>
      match b.val with
      | 0 => orderedInterval (-18985985733 / 1000000000000) (-18985940049 / 1000000000000)
      | 1 => orderedInterval (595770065 / 1000000000000) (595770123 / 1000000000000)
      | 2 => orderedInterval (-21321552455 / 1000000000000) (-21321552279 / 1000000000000)
      | 3 => orderedInterval (37956297891 / 1000000000000) (37956300831 / 1000000000000)
      | 4 => orderedInterval (-48313707793 / 1000000000000) (-48313707633 / 1000000000000)
      | 5 => orderedInterval (-15366204487 / 1000000000000) (-15366204244 / 1000000000000)
      | 6 => orderedInterval (-13686271867 / 1000000000000) (-13686269121 / 1000000000000)
      | 7 => orderedInterval (-4208736993 / 1000000000000) (-4208735149 / 1000000000000)
      | _ => orderedInterval (-7973270826 / 1000000000000) (-7973264454 / 1000000000000)
  coefficientTarget := fun i =>
    match i.val with
    | 0 => orderedInterval (-46929259352 / 1000000000000) (-46929205085 / 1000000000000)
    | 1 => orderedInterval (24169096428 / 1000000000000) (24169151137 / 1000000000000)
    | 2 => orderedInterval (59851198509 / 1000000000000) (59851254541 / 1000000000000)
    | 3 => orderedInterval (2750436464 / 1000000000000) (2750493924 / 1000000000000)
    | _ => orderedInterval (-91303662198 / 1000000000000) (-91303601975 / 1000000000000)

theorem compactCertificate242_stateChecks0 :
    compactCertificate242.stateChecks 0 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 38 12 (471 / 4)) (orderedInterval (-55055247493 / 1000000000000) (-55055134397 / 1000000000000), orderedInterval (48972377235 / 1000000000000) (48972490332 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 28 12 (693872936461371 / 8000000000000)) (orderedInterval (-36995917054 / 1000000000000) (-36995914106 / 1000000000000), orderedInterval (77487314554 / 1000000000000) (77487317501 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 45 12 (224384251132443 / 1600000000000)) (orderedInterval (22913315189 / 1000000000000) (22913315874 / 1000000000000), orderedInterval (-63441767793 / 1000000000000) (-63441767108 / 1000000000000))) = true
  norm_num [besselStateAtRationalPoint, besselIntervalStepZero,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, besselZeroTransition,
    besselInitial, besselGridStateAt, besselGridStateBlock00, besselGridStateBlock01,
    besselGridStateBlock02, besselGridStateBlock03, besselGridStateBlock04,
    besselGridStateBlock05, besselGridStateBlock06, besselGridStateBlock07,
    besselGridStateBlock08, besselGridStateBlock09, besselGridStateBlock10,
    besselGridStateBlock11, besselGridStateBlock12, besselGridStateBlock13,
    besselGridStateBlock14, besselGridState008, besselGridState011, besselGridState017, besselGridState020, besselGridState022, besselGridState028, besselGridState030, besselGridState033, besselGridState038, besselGridState041, besselGridState043, besselGridState045, besselGridState047, besselGridState048, besselGridState054, besselGridState055, besselGridState057, besselGridState059, besselGridState065, besselGridState069, besselGridState070, besselGridState074, besselGridState080, besselGridState084, besselGridState086, besselStateSubset, linearInterval, widenInterval,
    rationalErrorInterval, rationalIntervalSubset, orderedInterval, Finset.sum_range_succ,
    IntervalRat.add, IntervalRat.mul, IntervalRat.scale, IntervalRat.singleton]

theorem compactCertificate242_stateChecks1 :
    compactCertificate242.stateChecks 3 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 8 12 (202470392315697 / 8000000000000)) (orderedInterval (129594261474 / 1000000000000) (129594261475 / 1000000000000), orderedInterval (88861590651 / 1000000000000) (88861590652 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 22 12 (543863953576509 / 8000000000000)) (orderedInterval (-33043910842 / 1000000000000) (-33043909771 / 1000000000000), orderedInterval (91197354480 / 1000000000000) (91197355552 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 59 12 (1476696430566153 / 8000000000000)) (orderedInterval (-1045771554 / 1000000000000) (-1045771551 / 1000000000000), orderedInterval (-58715182985 / 1000000000000) (-58715182982 / 1000000000000))) = true
  norm_num [besselStateAtRationalPoint, besselIntervalStepZero,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, besselZeroTransition,
    besselInitial, besselGridStateAt, besselGridStateBlock00, besselGridStateBlock01,
    besselGridStateBlock02, besselGridStateBlock03, besselGridStateBlock04,
    besselGridStateBlock05, besselGridStateBlock06, besselGridStateBlock07,
    besselGridStateBlock08, besselGridStateBlock09, besselGridStateBlock10,
    besselGridStateBlock11, besselGridStateBlock12, besselGridStateBlock13,
    besselGridStateBlock14, besselGridState008, besselGridState011, besselGridState017, besselGridState020, besselGridState022, besselGridState028, besselGridState030, besselGridState033, besselGridState038, besselGridState041, besselGridState043, besselGridState045, besselGridState047, besselGridState048, besselGridState054, besselGridState055, besselGridState057, besselGridState059, besselGridState065, besselGridState069, besselGridState070, besselGridState074, besselGridState080, besselGridState084, besselGridState086, besselStateSubset, linearInterval, widenInterval,
    rationalErrorInterval, rationalIntervalSubset, orderedInterval, Finset.sum_range_succ,
    IntervalRat.add, IntervalRat.mul, IntervalRat.scale, IntervalRat.singleton]

theorem compactCertificate242_stateChecks2 :
    compactCertificate242.stateChecks 6 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 43 12 (1087727907153489 / 8000000000000)) (orderedInterval (-68142075508 / 1000000000000) (-68142075351 / 1000000000000), orderedInterval (6481561522 / 1000000000000) (6481561679 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 74 12 (1863840308635797 / 8000000000000)) (orderedInterval (50183010574 / 1000000000000) (50183010575 / 1000000000000), orderedInterval (14526780268 / 1000000000000) (14526780270 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 55 12 (1372896335506623 / 8000000000000)) (orderedInterval (23205833286 / 1000000000000) (23205834248 / 1000000000000), orderedInterval (-56380536569 / 1000000000000) (-56380535607 / 1000000000000))) = true
  norm_num [besselStateAtRationalPoint, besselIntervalStepZero,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, besselZeroTransition,
    besselInitial, besselGridStateAt, besselGridStateBlock00, besselGridStateBlock01,
    besselGridStateBlock02, besselGridStateBlock03, besselGridStateBlock04,
    besselGridStateBlock05, besselGridStateBlock06, besselGridStateBlock07,
    besselGridStateBlock08, besselGridStateBlock09, besselGridStateBlock10,
    besselGridStateBlock11, besselGridStateBlock12, besselGridStateBlock13,
    besselGridStateBlock14, besselGridState008, besselGridState011, besselGridState017, besselGridState020, besselGridState022, besselGridState028, besselGridState030, besselGridState033, besselGridState038, besselGridState041, besselGridState043, besselGridState045, besselGridState047, besselGridState048, besselGridState054, besselGridState055, besselGridState057, besselGridState059, besselGridState065, besselGridState069, besselGridState070, besselGridState074, besselGridState080, besselGridState084, besselGridState086, besselStateSubset, linearInterval, widenInterval,
    rationalErrorInterval, rationalIntervalSubset, orderedInterval, Finset.sum_range_succ,
    IntervalRat.add, IntervalRat.mul, IntervalRat.scale, IntervalRat.singleton]

theorem compactCertificate242_stateChecks3 :
    compactCertificate242.stateChecks 9 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 84 12 (2106376034804529 / 8000000000000)) (orderedInterval (9196950030 / 1000000000000) (9196950031 / 1000000000000), orderedInterval (48286749915 / 1000000000000) (48286749916 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 48 12 (1216116770708841 / 8000000000000)) (orderedInterval (58770397584 / 1000000000000) (58770406800 / 1000000000000), orderedInterval (-27284097554 / 1000000000000) (-27284088338 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 86 12 (2158020550433469 / 8000000000000)) (orderedInterval (17137796738 / 1000000000000) (17137796739 / 1000000000000), orderedInterval (45424946947 / 1000000000000) (45424946948 / 1000000000000))) = true
  norm_num [besselStateAtRationalPoint, besselIntervalStepZero,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, besselZeroTransition,
    besselInitial, besselGridStateAt, besselGridStateBlock00, besselGridStateBlock01,
    besselGridStateBlock02, besselGridStateBlock03, besselGridStateBlock04,
    besselGridStateBlock05, besselGridStateBlock06, besselGridStateBlock07,
    besselGridStateBlock08, besselGridStateBlock09, besselGridStateBlock10,
    besselGridStateBlock11, besselGridStateBlock12, besselGridStateBlock13,
    besselGridStateBlock14, besselGridState008, besselGridState011, besselGridState017, besselGridState020, besselGridState022, besselGridState028, besselGridState030, besselGridState033, besselGridState038, besselGridState041, besselGridState043, besselGridState045, besselGridState047, besselGridState048, besselGridState054, besselGridState055, besselGridState057, besselGridState059, besselGridState065, besselGridState069, besselGridState070, besselGridState074, besselGridState080, besselGridState084, besselGridState086, besselStateSubset, linearInterval, widenInterval,
    rationalErrorInterval, rationalIntervalSubset, orderedInterval, Finset.sum_range_succ,
    IntervalRat.add, IntervalRat.mul, IntervalRat.scale, IntervalRat.singleton]

theorem compactCertificate242_stateChecks4 :
    compactCertificate242.stateChecks 12 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 80 12 (2016302729278161 / 8000000000000)) (orderedInterval (50115137790 / 1000000000000) (50115137823 / 1000000000000), orderedInterval (3689734867 / 1000000000000) (3689734900 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 57 12 (1438928768215713 / 8000000000000)) (orderedInterval (-59490292231 / 1000000000000) (-59490292163 / 1000000000000), orderedInterval (713989364 / 1000000000000) (713989431 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 65 12 (1631591860729527 / 8000000000000)) (orderedInterval (-28255973289 / 1000000000000) (-28255973288 / 1000000000000), orderedInterval (-48128968335 / 1000000000000) (-48128968334 / 1000000000000))) = true
  norm_num [besselStateAtRationalPoint, besselIntervalStepZero,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, besselZeroTransition,
    besselInitial, besselGridStateAt, besselGridStateBlock00, besselGridStateBlock01,
    besselGridStateBlock02, besselGridStateBlock03, besselGridStateBlock04,
    besselGridStateBlock05, besselGridStateBlock06, besselGridStateBlock07,
    besselGridStateBlock08, besselGridStateBlock09, besselGridStateBlock10,
    besselGridStateBlock11, besselGridStateBlock12, besselGridStateBlock13,
    besselGridStateBlock14, besselGridState008, besselGridState011, besselGridState017, besselGridState020, besselGridState022, besselGridState028, besselGridState030, besselGridState033, besselGridState038, besselGridState041, besselGridState043, besselGridState045, besselGridState047, besselGridState048, besselGridState054, besselGridState055, besselGridState057, besselGridState059, besselGridState065, besselGridState069, besselGridState070, besselGridState074, besselGridState080, besselGridState084, besselGridState086, besselStateSubset, linearInterval, widenInterval,
    rationalErrorInterval, rationalIntervalSubset, orderedInterval, Finset.sum_range_succ,
    IntervalRat.add, IntervalRat.mul, IntervalRat.scale, IntervalRat.singleton]

theorem compactCertificate242_stateChecks5 :
    compactCertificate242.stateChecks 15 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 54 12 (1360251191473863 / 8000000000000)) (orderedInterval (56341364652 / 1000000000000) (56341364653 / 1000000000000), orderedInterval (23704178006 / 1000000000000) (23704178007 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 48 12 (1201823179947123 / 8000000000000)) (orderedInterval (13952984279 / 1000000000000) (13952984280 / 1000000000000), orderedInterval (63538378183 / 1000000000000) (63538378184 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 69 12 (348335200857177 / 1600000000000)) (orderedInterval (-53438593604 / 1000000000000) (-53438593001 / 1000000000000), orderedInterval (8398006473 / 1000000000000) (8398007076 / 1000000000000))) = true
  norm_num [besselStateAtRationalPoint, besselIntervalStepZero,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, besselZeroTransition,
    besselInitial, besselGridStateAt, besselGridStateBlock00, besselGridStateBlock01,
    besselGridStateBlock02, besselGridStateBlock03, besselGridStateBlock04,
    besselGridStateBlock05, besselGridStateBlock06, besselGridStateBlock07,
    besselGridStateBlock08, besselGridStateBlock09, besselGridStateBlock10,
    besselGridStateBlock11, besselGridStateBlock12, besselGridStateBlock13,
    besselGridStateBlock14, besselGridState008, besselGridState011, besselGridState017, besselGridState020, besselGridState022, besselGridState028, besselGridState030, besselGridState033, besselGridState038, besselGridState041, besselGridState043, besselGridState045, besselGridState047, besselGridState048, besselGridState054, besselGridState055, besselGridState057, besselGridState059, besselGridState065, besselGridState069, besselGridState070, besselGridState074, besselGridState080, besselGridState084, besselGridState086, besselStateSubset, linearInterval, widenInterval,
    rationalErrorInterval, rationalIntervalSubset, orderedInterval, Finset.sum_range_succ,
    IntervalRat.add, IntervalRat.mul, IntervalRat.scale, IntervalRat.singleton]

theorem compactCertificate242_stateChecks6 :
    compactCertificate242.stateChecks 18 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 38 12 (963513497448219 / 8000000000000)) (orderedInterval (70025923689 / 1000000000000) (70025925078 / 1000000000000), orderedInterval (-19839368376 / 1000000000000) (-19839366987 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 33 12 (816781062406659 / 8000000000000)) (orderedInterval (56134073787 / 1000000000000) (56134149559 / 1000000000000), orderedInterval (-55811969255 / 1000000000000) (-55811893483 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 20 12 (511103664493377 / 8000000000000)) (orderedInterval (96238208621 / 1000000000000) (96238209583 / 1000000000000), orderedInterval (-27259239855 / 1000000000000) (-27259238893 / 1000000000000))) = true
  norm_num [besselStateAtRationalPoint, besselIntervalStepZero,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, besselZeroTransition,
    besselInitial, besselGridStateAt, besselGridStateBlock00, besselGridStateBlock01,
    besselGridStateBlock02, besselGridStateBlock03, besselGridStateBlock04,
    besselGridStateBlock05, besselGridStateBlock06, besselGridStateBlock07,
    besselGridStateBlock08, besselGridStateBlock09, besselGridStateBlock10,
    besselGridStateBlock11, besselGridStateBlock12, besselGridStateBlock13,
    besselGridStateBlock14, besselGridState008, besselGridState011, besselGridState017, besselGridState020, besselGridState022, besselGridState028, besselGridState030, besselGridState033, besselGridState038, besselGridState041, besselGridState043, besselGridState045, besselGridState047, besselGridState048, besselGridState054, besselGridState055, besselGridState057, besselGridState059, besselGridState065, besselGridState069, besselGridState070, besselGridState074, besselGridState080, besselGridState084, besselGridState086, besselStateSubset, linearInterval, widenInterval,
    rationalErrorInterval, rationalIntervalSubset, orderedInterval, Finset.sum_range_succ,
    IntervalRat.add, IntervalRat.mul, IntervalRat.scale, IntervalRat.singleton]

theorem compactCertificate242_stateChecks7 :
    compactCertificate242.stateChecks 21 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 11 12 (274873250618559 / 8000000000000)) (orderedInterval (-74979074979 / 1000000000000) (-74979074978 / 1000000000000), orderedInterval (-112519405524 / 1000000000000) (-112519405523 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 30 12 (746334345892677 / 8000000000000)) (orderedInterval (-14132538535 / 1000000000000) (-14132538442 / 1000000000000), orderedInterval (81465709573 / 1000000000000) (81465709665 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 41 12 (1019055743230629 / 8000000000000)) (orderedInterval (42156700887 / 1000000000000) (42156718050 / 1000000000000), orderedInterval (-56915331966 / 1000000000000) (-56915314802 / 1000000000000))) = true
  norm_num [besselStateAtRationalPoint, besselIntervalStepZero,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, besselZeroTransition,
    besselInitial, besselGridStateAt, besselGridStateBlock00, besselGridStateBlock01,
    besselGridStateBlock02, besselGridStateBlock03, besselGridStateBlock04,
    besselGridStateBlock05, besselGridStateBlock06, besselGridStateBlock07,
    besselGridStateBlock08, besselGridStateBlock09, besselGridStateBlock10,
    besselGridStateBlock11, besselGridStateBlock12, besselGridStateBlock13,
    besselGridStateBlock14, besselGridState008, besselGridState011, besselGridState017, besselGridState020, besselGridState022, besselGridState028, besselGridState030, besselGridState033, besselGridState038, besselGridState041, besselGridState043, besselGridState045, besselGridState047, besselGridState048, besselGridState054, besselGridState055, besselGridState057, besselGridState059, besselGridState065, besselGridState069, besselGridState070, besselGridState074, besselGridState080, besselGridState084, besselGridState086, besselStateSubset, linearInterval, widenInterval,
    rationalErrorInterval, rationalIntervalSubset, orderedInterval, Finset.sum_range_succ,
    IntervalRat.add, IntervalRat.mul, IntervalRat.scale, IntervalRat.singleton]

theorem compactCertificate242_stateChecks8 :
    compactCertificate242.stateChecks 24 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 17 12 (430896335506623 / 8000000000000)) (orderedInterval (-102751628195 / 1000000000000) (-102751628194 / 1000000000000), orderedInterval (-34558966864 / 1000000000000) (-34558966862 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 70 12 (1751569681185183 / 8000000000000)) (orderedInterval (-9677523716 / 1000000000000) (-9677523674 / 1000000000000), orderedInterval (53069309199 / 1000000000000) (53069309241 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 47 12 (1169967372174897 / 8000000000000)) (orderedInterval (38570682413 / 1000000000000) (38570696032 / 1000000000000), orderedInterval (-53661184564 / 1000000000000) (-53661170946 / 1000000000000))) = true
  norm_num [besselStateAtRationalPoint, besselIntervalStepZero,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, besselZeroTransition,
    besselInitial, besselGridStateAt, besselGridStateBlock00, besselGridStateBlock01,
    besselGridStateBlock02, besselGridStateBlock03, besselGridStateBlock04,
    besselGridStateBlock05, besselGridStateBlock06, besselGridStateBlock07,
    besselGridStateBlock08, besselGridStateBlock09, besselGridStateBlock10,
    besselGridStateBlock11, besselGridStateBlock12, besselGridStateBlock13,
    besselGridStateBlock14, besselGridState008, besselGridState011, besselGridState017, besselGridState020, besselGridState022, besselGridState028, besselGridState030, besselGridState033, besselGridState038, besselGridState041, besselGridState043, besselGridState045, besselGridState047, besselGridState048, besselGridState054, besselGridState055, besselGridState057, besselGridState059, besselGridState065, besselGridState069, besselGridState070, besselGridState074, besselGridState080, besselGridState084, besselGridState086, besselStateSubset, linearInterval, widenInterval,
    rationalErrorInterval, rationalIntervalSubset, orderedInterval, Finset.sum_range_succ,
    IntervalRat.add, IntervalRat.mul, IntervalRat.scale, IntervalRat.singleton]

theorem compactCertificate242_states : ∀ j,
    BesselStateValid (compactCertificate242.point j) (compactCertificate242.state j) :=
  compactCertificate242.statesValid_of_checks3 compactCertificate242_stateChecks0
    compactCertificate242_stateChecks1 compactCertificate242_stateChecks2
    compactCertificate242_stateChecks3 compactCertificate242_stateChecks4
    compactCertificate242_stateChecks5 compactCertificate242_stateChecks6
    compactCertificate242_stateChecks7 compactCertificate242_stateChecks8

theorem compactCertificate242_chunkChecks0_0 :
    compactCertificate242.chunkChecks (0 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 0) <| besselDerivativeNearFromState (471 / 4) 0 (IntervalRat.scale (471 / 4) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-55055247493 / 1000000000000) (-55055134397 / 1000000000000), orderedInterval (48972377235 / 1000000000000) (48972490332 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 0) <| besselDerivativeNearFromState (693872936461371 / 8000000000000) 0 (IntervalRat.scale (471 / 4) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-36995917054 / 1000000000000) (-36995914106 / 1000000000000), orderedInterval (77487314554 / 1000000000000) (77487317501 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 0) <| besselDerivativeNearFromState (224384251132443 / 1600000000000) 0 (IntervalRat.scale (471 / 4) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (22913315189 / 1000000000000) (22913315874 / 1000000000000), orderedInterval (-63441767793 / 1000000000000) (-63441767108 / 1000000000000)))) (orderedInterval (-20822123510 / 1000000000000) (-20822078606 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 0) <| besselDerivativeNearFromState (202470392315697 / 8000000000000) 0 (IntervalRat.scale (471 / 4) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (129594261474 / 1000000000000) (129594261475 / 1000000000000), orderedInterval (88861590651 / 1000000000000) (88861590652 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 0) <| besselDerivativeNearFromState (543863953576509 / 8000000000000) 0 (IntervalRat.scale (471 / 4) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-33043910842 / 1000000000000) (-33043909771 / 1000000000000), orderedInterval (91197354480 / 1000000000000) (91197355552 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 0) <| besselDerivativeNearFromState (1476696430566153 / 8000000000000) 0 (IntervalRat.scale (471 / 4) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-1045771554 / 1000000000000) (-1045771551 / 1000000000000), orderedInterval (-58715182985 / 1000000000000) (-58715182982 / 1000000000000)))) (orderedInterval (-2538153218 / 1000000000000) (-2538153163 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 0) <| besselDerivativeNearFromState (1087727907153489 / 8000000000000) 0 (IntervalRat.scale (471 / 4) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-68142075508 / 1000000000000) (-68142075351 / 1000000000000), orderedInterval (6481561522 / 1000000000000) (6481561679 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 0) <| besselDerivativeNearFromState (1863840308635797 / 8000000000000) 0 (IntervalRat.scale (471 / 4) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (50183010574 / 1000000000000) (50183010575 / 1000000000000), orderedInterval (14526780268 / 1000000000000) (14526780270 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 0) <| besselDerivativeNearFromState (1372896335506623 / 8000000000000) 0 (IntervalRat.scale (471 / 4) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (23205833286 / 1000000000000) (23205834248 / 1000000000000), orderedInterval (-56380536569 / 1000000000000) (-56380535607 / 1000000000000)))) (orderedInterval (-987005627 / 1000000000000) (-987005596 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate242_chunkChecks0_1 :
    compactCertificate242.chunkChecks (0 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 0) <| besselDerivativeNearFromState (2106376034804529 / 8000000000000) 0 (IntervalRat.scale (471 / 4) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (9196950030 / 1000000000000) (9196950031 / 1000000000000), orderedInterval (48286749915 / 1000000000000) (48286749916 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 0) <| besselDerivativeNearFromState (1216116770708841 / 8000000000000) 0 (IntervalRat.scale (471 / 4) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (58770397584 / 1000000000000) (58770406800 / 1000000000000), orderedInterval (-27284097554 / 1000000000000) (-27284088338 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 0) <| besselDerivativeNearFromState (2158020550433469 / 8000000000000) 0 (IntervalRat.scale (471 / 4) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (17137796738 / 1000000000000) (17137796739 / 1000000000000), orderedInterval (45424946947 / 1000000000000) (45424946948 / 1000000000000)))) (orderedInterval (5156454621 / 1000000000000) (5156455352 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 0) <| besselDerivativeNearFromState (2016302729278161 / 8000000000000) 0 (IntervalRat.scale (471 / 4) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (50115137790 / 1000000000000) (50115137823 / 1000000000000), orderedInterval (3689734867 / 1000000000000) (3689734900 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 0) <| besselDerivativeNearFromState (1438928768215713 / 8000000000000) 0 (IntervalRat.scale (471 / 4) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-59490292231 / 1000000000000) (-59490292163 / 1000000000000), orderedInterval (713989364 / 1000000000000) (713989431 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 0) <| besselDerivativeNearFromState (1631591860729527 / 8000000000000) 0 (IntervalRat.scale (471 / 4) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-28255973289 / 1000000000000) (-28255973288 / 1000000000000), orderedInterval (-48128968335 / 1000000000000) (-48128968334 / 1000000000000)))) (orderedInterval (-6387313933 / 1000000000000) (-6387313911 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 0) <| besselDerivativeNearFromState (1360251191473863 / 8000000000000) 0 (IntervalRat.scale (471 / 4) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (56341364652 / 1000000000000) (56341364653 / 1000000000000), orderedInterval (23704178006 / 1000000000000) (23704178007 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 0) <| besselDerivativeNearFromState (1201823179947123 / 8000000000000) 0 (IntervalRat.scale (471 / 4) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (13952984279 / 1000000000000) (13952984280 / 1000000000000), orderedInterval (63538378183 / 1000000000000) (63538378184 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 0) <| besselDerivativeNearFromState (348335200857177 / 1600000000000) 0 (IntervalRat.scale (471 / 4) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-53438593604 / 1000000000000) (-53438593001 / 1000000000000), orderedInterval (8398006473 / 1000000000000) (8398007076 / 1000000000000)))) (orderedInterval (-1516110523 / 1000000000000) (-1516110495 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate242_chunkChecks0_2 :
    compactCertificate242.chunkChecks (0 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 0) <| besselDerivativeNearFromState (963513497448219 / 8000000000000) 0 (IntervalRat.scale (471 / 4) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (70025923689 / 1000000000000) (70025925078 / 1000000000000), orderedInterval (-19839368376 / 1000000000000) (-19839366987 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 0) <| besselDerivativeNearFromState (816781062406659 / 8000000000000) 0 (IntervalRat.scale (471 / 4) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (56134073787 / 1000000000000) (56134149559 / 1000000000000), orderedInterval (-55811969255 / 1000000000000) (-55811893483 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 0) <| besselDerivativeNearFromState (511103664493377 / 8000000000000) 0 (IntervalRat.scale (471 / 4) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (96238208621 / 1000000000000) (96238209583 / 1000000000000), orderedInterval (-27259239855 / 1000000000000) (-27259238893 / 1000000000000)))) (orderedInterval (-11240745612 / 1000000000000) (-11240741040 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 0) <| besselDerivativeNearFromState (274873250618559 / 8000000000000) 0 (IntervalRat.scale (471 / 4) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-74979074979 / 1000000000000) (-74979074978 / 1000000000000), orderedInterval (-112519405524 / 1000000000000) (-112519405523 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 0) <| besselDerivativeNearFromState (746334345892677 / 8000000000000) 0 (IntervalRat.scale (471 / 4) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-14132538535 / 1000000000000) (-14132538442 / 1000000000000), orderedInterval (81465709573 / 1000000000000) (81465709665 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 0) <| besselDerivativeNearFromState (1019055743230629 / 8000000000000) 0 (IntervalRat.scale (471 / 4) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (42156700887 / 1000000000000) (42156718050 / 1000000000000), orderedInterval (-56915331966 / 1000000000000) (-56915314802 / 1000000000000)))) (orderedInterval (-1525722900 / 1000000000000) (-1525721568 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 0) <| besselDerivativeNearFromState (430896335506623 / 8000000000000) 0 (IntervalRat.scale (471 / 4) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-102751628195 / 1000000000000) (-102751628194 / 1000000000000), orderedInterval (-34558966864 / 1000000000000) (-34558966862 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 0) <| besselDerivativeNearFromState (1751569681185183 / 8000000000000) 0 (IntervalRat.scale (471 / 4) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-9677523716 / 1000000000000) (-9677523674 / 1000000000000), orderedInterval (53069309199 / 1000000000000) (53069309241 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 0) <| besselDerivativeNearFromState (1169967372174897 / 8000000000000) 0 (IntervalRat.scale (471 / 4) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (38570682413 / 1000000000000) (38570696032 / 1000000000000), orderedInterval (-53661184564 / 1000000000000) (-53661170946 / 1000000000000)))) (orderedInterval (-7068538650 / 1000000000000) (-7068536058 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate242_chunkChecks0 :
    compactCertificate242.chunkChecks (0 : Fin 5) 0 9 = true :=
  compactCertificate242.chunkChecks_nine_of_three (0 : Fin 5) compactCertificate242_chunkChecks0_0
    compactCertificate242_chunkChecks0_1 compactCertificate242_chunkChecks0_2

theorem compactCertificate242_chunkChecks1_0 :
    compactCertificate242.chunkChecks (1 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 1) <| besselDerivativeNearFromState (471 / 4) 1 (IntervalRat.scale (471 / 4) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-55055247493 / 1000000000000) (-55055134397 / 1000000000000), orderedInterval (48972377235 / 1000000000000) (48972490332 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 1) <| besselDerivativeNearFromState (693872936461371 / 8000000000000) 1 (IntervalRat.scale (471 / 4) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-36995917054 / 1000000000000) (-36995914106 / 1000000000000), orderedInterval (77487314554 / 1000000000000) (77487317501 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 1) <| besselDerivativeNearFromState (224384251132443 / 1600000000000) 1 (IntervalRat.scale (471 / 4) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (22913315189 / 1000000000000) (22913315874 / 1000000000000), orderedInterval (-63441767793 / 1000000000000) (-63441767108 / 1000000000000)))) (orderedInterval (15508887200 / 1000000000000) (15508932106 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 1) <| besselDerivativeNearFromState (202470392315697 / 8000000000000) 1 (IntervalRat.scale (471 / 4) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (129594261474 / 1000000000000) (129594261475 / 1000000000000), orderedInterval (88861590651 / 1000000000000) (88861590652 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 1) <| besselDerivativeNearFromState (543863953576509 / 8000000000000) 1 (IntervalRat.scale (471 / 4) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-33043910842 / 1000000000000) (-33043909771 / 1000000000000), orderedInterval (91197354480 / 1000000000000) (91197355552 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 1) <| besselDerivativeNearFromState (1476696430566153 / 8000000000000) 1 (IntervalRat.scale (471 / 4) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-1045771554 / 1000000000000) (-1045771551 / 1000000000000), orderedInterval (-58715182985 / 1000000000000) (-58715182982 / 1000000000000)))) (orderedInterval (8258532412 / 1000000000000) (8258532452 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 1) <| besselDerivativeNearFromState (1087727907153489 / 8000000000000) 1 (IntervalRat.scale (471 / 4) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-68142075508 / 1000000000000) (-68142075351 / 1000000000000), orderedInterval (6481561522 / 1000000000000) (6481561679 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 1) <| besselDerivativeNearFromState (1863840308635797 / 8000000000000) 1 (IntervalRat.scale (471 / 4) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (50183010574 / 1000000000000) (50183010575 / 1000000000000), orderedInterval (14526780268 / 1000000000000) (14526780270 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 1) <| besselDerivativeNearFromState (1372896335506623 / 8000000000000) 1 (IntervalRat.scale (471 / 4) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (23205833286 / 1000000000000) (23205834248 / 1000000000000), orderedInterval (-56380536569 / 1000000000000) (-56380535607 / 1000000000000)))) (orderedInterval (-2872438465 / 1000000000000) (-2872438419 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate242_chunkChecks1_1 :
    compactCertificate242.chunkChecks (1 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 1) <| besselDerivativeNearFromState (2106376034804529 / 8000000000000) 1 (IntervalRat.scale (471 / 4) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (9196950030 / 1000000000000) (9196950031 / 1000000000000), orderedInterval (48286749915 / 1000000000000) (48286749916 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 1) <| besselDerivativeNearFromState (1216116770708841 / 8000000000000) 1 (IntervalRat.scale (471 / 4) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (58770397584 / 1000000000000) (58770406800 / 1000000000000), orderedInterval (-27284097554 / 1000000000000) (-27284088338 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 1) <| besselDerivativeNearFromState (2158020550433469 / 8000000000000) 1 (IntervalRat.scale (471 / 4) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (17137796738 / 1000000000000) (17137796739 / 1000000000000), orderedInterval (45424946947 / 1000000000000) (45424946948 / 1000000000000)))) (orderedInterval (-7001919350 / 1000000000000) (-7001918370 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 1) <| besselDerivativeNearFromState (2016302729278161 / 8000000000000) 1 (IntervalRat.scale (471 / 4) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (50115137790 / 1000000000000) (50115137823 / 1000000000000), orderedInterval (3689734867 / 1000000000000) (3689734900 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 1) <| besselDerivativeNearFromState (1438928768215713 / 8000000000000) 1 (IntervalRat.scale (471 / 4) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-59490292231 / 1000000000000) (-59490292163 / 1000000000000), orderedInterval (713989364 / 1000000000000) (713989431 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 1) <| besselDerivativeNearFromState (1631591860729527 / 8000000000000) 1 (IntervalRat.scale (471 / 4) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-28255973289 / 1000000000000) (-28255973288 / 1000000000000), orderedInterval (-48128968335 / 1000000000000) (-48128968334 / 1000000000000)))) (orderedInterval (382414895 / 1000000000000) (382414930 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 1) <| besselDerivativeNearFromState (1360251191473863 / 8000000000000) 1 (IntervalRat.scale (471 / 4) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (56341364652 / 1000000000000) (56341364653 / 1000000000000), orderedInterval (23704178006 / 1000000000000) (23704178007 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 1) <| besselDerivativeNearFromState (1201823179947123 / 8000000000000) 1 (IntervalRat.scale (471 / 4) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (13952984279 / 1000000000000) (13952984280 / 1000000000000), orderedInterval (63538378183 / 1000000000000) (63538378184 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 1) <| besselDerivativeNearFromState (348335200857177 / 1600000000000) 1 (IntervalRat.scale (471 / 4) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-53438593604 / 1000000000000) (-53438593001 / 1000000000000), orderedInterval (8398006473 / 1000000000000) (8398007076 / 1000000000000)))) (orderedInterval (-3846178109 / 1000000000000) (-3846178064 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate242_chunkChecks1_2 :
    compactCertificate242.chunkChecks (1 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 1) <| besselDerivativeNearFromState (963513497448219 / 8000000000000) 1 (IntervalRat.scale (471 / 4) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (70025923689 / 1000000000000) (70025925078 / 1000000000000), orderedInterval (-19839368376 / 1000000000000) (-19839366987 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 1) <| besselDerivativeNearFromState (816781062406659 / 8000000000000) 1 (IntervalRat.scale (471 / 4) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (56134073787 / 1000000000000) (56134149559 / 1000000000000), orderedInterval (-55811969255 / 1000000000000) (-55811893483 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 1) <| besselDerivativeNearFromState (511103664493377 / 8000000000000) 1 (IntervalRat.scale (471 / 4) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (96238208621 / 1000000000000) (96238209583 / 1000000000000), orderedInterval (-27259239855 / 1000000000000) (-27259238893 / 1000000000000)))) (orderedInterval (5502149709 / 1000000000000) (5502153700 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 1) <| besselDerivativeNearFromState (274873250618559 / 8000000000000) 1 (IntervalRat.scale (471 / 4) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-74979074979 / 1000000000000) (-74979074978 / 1000000000000), orderedInterval (-112519405524 / 1000000000000) (-112519405523 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 1) <| besselDerivativeNearFromState (746334345892677 / 8000000000000) 1 (IntervalRat.scale (471 / 4) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-14132538535 / 1000000000000) (-14132538442 / 1000000000000), orderedInterval (81465709573 / 1000000000000) (81465709665 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 1) <| besselDerivativeNearFromState (1019055743230629 / 8000000000000) 1 (IntervalRat.scale (471 / 4) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (42156700887 / 1000000000000) (42156718050 / 1000000000000), orderedInterval (-56915331966 / 1000000000000) (-56915314802 / 1000000000000)))) (orderedInterval (3860688715 / 1000000000000) (3860690154 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 1) <| besselDerivativeNearFromState (430896335506623 / 8000000000000) 1 (IntervalRat.scale (471 / 4) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-102751628195 / 1000000000000) (-102751628194 / 1000000000000), orderedInterval (-34558966864 / 1000000000000) (-34558966862 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 1) <| besselDerivativeNearFromState (1751569681185183 / 8000000000000) 1 (IntervalRat.scale (471 / 4) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-9677523716 / 1000000000000) (-9677523674 / 1000000000000), orderedInterval (53069309199 / 1000000000000) (53069309241 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 1) <| besselDerivativeNearFromState (1169967372174897 / 8000000000000) 1 (IntervalRat.scale (471 / 4) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (38570682413 / 1000000000000) (38570696032 / 1000000000000), orderedInterval (-53661184564 / 1000000000000) (-53661170946 / 1000000000000)))) (orderedInterval (4376959421 / 1000000000000) (4376962648 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate242_chunkChecks1 :
    compactCertificate242.chunkChecks (1 : Fin 5) 0 9 = true :=
  compactCertificate242.chunkChecks_nine_of_three (1 : Fin 5) compactCertificate242_chunkChecks1_0
    compactCertificate242_chunkChecks1_1 compactCertificate242_chunkChecks1_2

theorem compactCertificate242_chunkChecks2_0 :
    compactCertificate242.chunkChecks (2 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 2) <| besselDerivativeNearFromState (471 / 4) 2 (IntervalRat.scale (471 / 4) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-55055247493 / 1000000000000) (-55055134397 / 1000000000000), orderedInterval (48972377235 / 1000000000000) (48972490332 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 2) <| besselDerivativeNearFromState (693872936461371 / 8000000000000) 2 (IntervalRat.scale (471 / 4) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-36995917054 / 1000000000000) (-36995914106 / 1000000000000), orderedInterval (77487314554 / 1000000000000) (77487317501 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 2) <| besselDerivativeNearFromState (224384251132443 / 1600000000000) 2 (IntervalRat.scale (471 / 4) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (22913315189 / 1000000000000) (22913315874 / 1000000000000), orderedInterval (-63441767793 / 1000000000000) (-63441767108 / 1000000000000)))) (orderedInterval (19970000573 / 1000000000000) (19970045865 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 2) <| besselDerivativeNearFromState (202470392315697 / 8000000000000) 2 (IntervalRat.scale (471 / 4) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (129594261474 / 1000000000000) (129594261475 / 1000000000000), orderedInterval (88861590651 / 1000000000000) (88861590652 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 2) <| besselDerivativeNearFromState (543863953576509 / 8000000000000) 2 (IntervalRat.scale (471 / 4) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-33043910842 / 1000000000000) (-33043909771 / 1000000000000), orderedInterval (91197354480 / 1000000000000) (91197355552 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 2) <| besselDerivativeNearFromState (1476696430566153 / 8000000000000) 2 (IntervalRat.scale (471 / 4) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-1045771554 / 1000000000000) (-1045771551 / 1000000000000), orderedInterval (-58715182985 / 1000000000000) (-58715182982 / 1000000000000)))) (orderedInterval (214288023 / 1000000000000) (214288060 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 2) <| besselDerivativeNearFromState (1087727907153489 / 8000000000000) 2 (IntervalRat.scale (471 / 4) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-68142075508 / 1000000000000) (-68142075351 / 1000000000000), orderedInterval (6481561522 / 1000000000000) (6481561679 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 2) <| besselDerivativeNearFromState (1863840308635797 / 8000000000000) 2 (IntervalRat.scale (471 / 4) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (50183010574 / 1000000000000) (50183010575 / 1000000000000), orderedInterval (14526780268 / 1000000000000) (14526780270 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 2) <| besselDerivativeNearFromState (1372896335506623 / 8000000000000) 2 (IntervalRat.scale (471 / 4) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (23205833286 / 1000000000000) (23205834248 / 1000000000000), orderedInterval (-56380536569 / 1000000000000) (-56380535607 / 1000000000000)))) (orderedInterval (4892706108 / 1000000000000) (4892706179 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate242_chunkChecks2_1 :
    compactCertificate242.chunkChecks (2 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 2) <| besselDerivativeNearFromState (2106376034804529 / 8000000000000) 2 (IntervalRat.scale (471 / 4) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (9196950030 / 1000000000000) (9196950031 / 1000000000000), orderedInterval (48286749915 / 1000000000000) (48286749916 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 2) <| besselDerivativeNearFromState (1216116770708841 / 8000000000000) 2 (IntervalRat.scale (471 / 4) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (58770397584 / 1000000000000) (58770406800 / 1000000000000), orderedInterval (-27284097554 / 1000000000000) (-27284088338 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 2) <| besselDerivativeNearFromState (2158020550433469 / 8000000000000) 2 (IntervalRat.scale (471 / 4) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (17137796738 / 1000000000000) (17137796739 / 1000000000000), orderedInterval (45424946947 / 1000000000000) (45424946948 / 1000000000000)))) (orderedInterval (-11812778194 / 1000000000000) (-11812776839 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 2) <| besselDerivativeNearFromState (2016302729278161 / 8000000000000) 2 (IntervalRat.scale (471 / 4) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (50115137790 / 1000000000000) (50115137823 / 1000000000000), orderedInterval (3689734867 / 1000000000000) (3689734900 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 2) <| besselDerivativeNearFromState (1438928768215713 / 8000000000000) 2 (IntervalRat.scale (471 / 4) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-59490292231 / 1000000000000) (-59490292163 / 1000000000000), orderedInterval (713989364 / 1000000000000) (713989431 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 2) <| besselDerivativeNearFromState (1631591860729527 / 8000000000000) 2 (IntervalRat.scale (471 / 4) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-28255973289 / 1000000000000) (-28255973288 / 1000000000000), orderedInterval (-48128968335 / 1000000000000) (-48128968334 / 1000000000000)))) (orderedInterval (16839166328 / 1000000000000) (16839166385 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 2) <| besselDerivativeNearFromState (1360251191473863 / 8000000000000) 2 (IntervalRat.scale (471 / 4) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (56341364652 / 1000000000000) (56341364653 / 1000000000000), orderedInterval (23704178006 / 1000000000000) (23704178007 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 2) <| besselDerivativeNearFromState (1201823179947123 / 8000000000000) 2 (IntervalRat.scale (471 / 4) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (13952984279 / 1000000000000) (13952984280 / 1000000000000), orderedInterval (63538378183 / 1000000000000) (63538378184 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 2) <| besselDerivativeNearFromState (348335200857177 / 1600000000000) 2 (IntervalRat.scale (471 / 4) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-53438593604 / 1000000000000) (-53438593001 / 1000000000000), orderedInterval (8398006473 / 1000000000000) (8398007076 / 1000000000000)))) (orderedInterval (4653046357 / 1000000000000) (4653046436 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate242_chunkChecks2_2 :
    compactCertificate242.chunkChecks (2 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 2) <| besselDerivativeNearFromState (963513497448219 / 8000000000000) 2 (IntervalRat.scale (471 / 4) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (70025923689 / 1000000000000) (70025925078 / 1000000000000), orderedInterval (-19839368376 / 1000000000000) (-19839366987 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 2) <| besselDerivativeNearFromState (816781062406659 / 8000000000000) 2 (IntervalRat.scale (471 / 4) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (56134073787 / 1000000000000) (56134149559 / 1000000000000), orderedInterval (-55811969255 / 1000000000000) (-55811893483 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 2) <| besselDerivativeNearFromState (511103664493377 / 8000000000000) 2 (IntervalRat.scale (471 / 4) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (96238208621 / 1000000000000) (96238209583 / 1000000000000), orderedInterval (-27259239855 / 1000000000000) (-27259238893 / 1000000000000)))) (orderedInterval (13133468310 / 1000000000000) (13133471836 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 2) <| besselDerivativeNearFromState (274873250618559 / 8000000000000) 2 (IntervalRat.scale (471 / 4) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-74979074979 / 1000000000000) (-74979074978 / 1000000000000), orderedInterval (-112519405524 / 1000000000000) (-112519405523 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 2) <| besselDerivativeNearFromState (746334345892677 / 8000000000000) 2 (IntervalRat.scale (471 / 4) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-14132538535 / 1000000000000) (-14132538442 / 1000000000000), orderedInterval (81465709573 / 1000000000000) (81465709665 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 2) <| besselDerivativeNearFromState (1019055743230629 / 8000000000000) 2 (IntervalRat.scale (471 / 4) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (42156700887 / 1000000000000) (42156718050 / 1000000000000), orderedInterval (-56915331966 / 1000000000000) (-56915314802 / 1000000000000)))) (orderedInterval (3429094743 / 1000000000000) (3429096309 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 2) <| besselDerivativeNearFromState (430896335506623 / 8000000000000) 2 (IntervalRat.scale (471 / 4) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-102751628195 / 1000000000000) (-102751628194 / 1000000000000), orderedInterval (-34558966864 / 1000000000000) (-34558966862 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 2) <| besselDerivativeNearFromState (1751569681185183 / 8000000000000) 2 (IntervalRat.scale (471 / 4) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-9677523716 / 1000000000000) (-9677523674 / 1000000000000), orderedInterval (53069309199 / 1000000000000) (53069309241 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 2) <| besselDerivativeNearFromState (1169967372174897 / 8000000000000) 2 (IntervalRat.scale (471 / 4) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (38570682413 / 1000000000000) (38570696032 / 1000000000000), orderedInterval (-53661184564 / 1000000000000) (-53661170946 / 1000000000000)))) (orderedInterval (8532206261 / 1000000000000) (8532210310 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate242_chunkChecks2 :
    compactCertificate242.chunkChecks (2 : Fin 5) 0 9 = true :=
  compactCertificate242.chunkChecks_nine_of_three (2 : Fin 5) compactCertificate242_chunkChecks2_0
    compactCertificate242_chunkChecks2_1 compactCertificate242_chunkChecks2_2

theorem compactCertificate242_chunkChecks3_0 :
    compactCertificate242.chunkChecks (3 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 3) <| besselDerivativeNearFromState (471 / 4) 3 (IntervalRat.scale (471 / 4) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-55055247493 / 1000000000000) (-55055134397 / 1000000000000), orderedInterval (48972377235 / 1000000000000) (48972490332 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 3) <| besselDerivativeNearFromState (693872936461371 / 8000000000000) 3 (IntervalRat.scale (471 / 4) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-36995917054 / 1000000000000) (-36995914106 / 1000000000000), orderedInterval (77487314554 / 1000000000000) (77487317501 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 3) <| besselDerivativeNearFromState (224384251132443 / 1600000000000) 3 (IntervalRat.scale (471 / 4) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (22913315189 / 1000000000000) (22913315874 / 1000000000000), orderedInterval (-63441767793 / 1000000000000) (-63441767108 / 1000000000000)))) (orderedInterval (-13578638195 / 1000000000000) (-13578592900 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 3) <| besselDerivativeNearFromState (202470392315697 / 8000000000000) 3 (IntervalRat.scale (471 / 4) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (129594261474 / 1000000000000) (129594261475 / 1000000000000), orderedInterval (88861590651 / 1000000000000) (88861590652 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 3) <| besselDerivativeNearFromState (543863953576509 / 8000000000000) 3 (IntervalRat.scale (471 / 4) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-33043910842 / 1000000000000) (-33043909771 / 1000000000000), orderedInterval (91197354480 / 1000000000000) (91197355552 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 3) <| besselDerivativeNearFromState (1476696430566153 / 8000000000000) 3 (IntervalRat.scale (471 / 4) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-1045771554 / 1000000000000) (-1045771551 / 1000000000000), orderedInterval (-58715182985 / 1000000000000) (-58715182982 / 1000000000000)))) (orderedInterval (-16712157985 / 1000000000000) (-16712157943 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 3) <| besselDerivativeNearFromState (1087727907153489 / 8000000000000) 3 (IntervalRat.scale (471 / 4) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-68142075508 / 1000000000000) (-68142075351 / 1000000000000), orderedInterval (6481561522 / 1000000000000) (6481561679 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 3) <| besselDerivativeNearFromState (1863840308635797 / 8000000000000) 3 (IntervalRat.scale (471 / 4) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (50183010574 / 1000000000000) (50183010575 / 1000000000000), orderedInterval (14526780268 / 1000000000000) (14526780270 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 3) <| besselDerivativeNearFromState (1372896335506623 / 8000000000000) 3 (IntervalRat.scale (471 / 4) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (23205833286 / 1000000000000) (23205834248 / 1000000000000), orderedInterval (-56380536569 / 1000000000000) (-56380535607 / 1000000000000)))) (orderedInterval (7647148812 / 1000000000000) (7647148923 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate242_chunkChecks3_1 :
    compactCertificate242.chunkChecks (3 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 3) <| besselDerivativeNearFromState (2106376034804529 / 8000000000000) 3 (IntervalRat.scale (471 / 4) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (9196950030 / 1000000000000) (9196950031 / 1000000000000), orderedInterval (48286749915 / 1000000000000) (48286749916 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 3) <| besselDerivativeNearFromState (1216116770708841 / 8000000000000) 3 (IntervalRat.scale (471 / 4) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (58770397584 / 1000000000000) (58770406800 / 1000000000000), orderedInterval (-27284097554 / 1000000000000) (-27284088338 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 3) <| besselDerivativeNearFromState (2158020550433469 / 8000000000000) 3 (IntervalRat.scale (471 / 4) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (17137796738 / 1000000000000) (17137796739 / 1000000000000), orderedInterval (45424946947 / 1000000000000) (45424946948 / 1000000000000)))) (orderedInterval (22738639456 / 1000000000000) (22738641394 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 3) <| besselDerivativeNearFromState (2016302729278161 / 8000000000000) 3 (IntervalRat.scale (471 / 4) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (50115137790 / 1000000000000) (50115137823 / 1000000000000), orderedInterval (3689734867 / 1000000000000) (3689734900 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 3) <| besselDerivativeNearFromState (1438928768215713 / 8000000000000) 3 (IntervalRat.scale (471 / 4) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-59490292231 / 1000000000000) (-59490292163 / 1000000000000), orderedInterval (713989364 / 1000000000000) (713989431 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 3) <| besselDerivativeNearFromState (1631591860729527 / 8000000000000) 3 (IntervalRat.scale (471 / 4) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-28255973289 / 1000000000000) (-28255973288 / 1000000000000), orderedInterval (-48128968335 / 1000000000000) (-48128968334 / 1000000000000)))) (orderedInterval (-995979628 / 1000000000000) (-995979534 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 3) <| besselDerivativeNearFromState (1360251191473863 / 8000000000000) 3 (IntervalRat.scale (471 / 4) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (56341364652 / 1000000000000) (56341364653 / 1000000000000), orderedInterval (23704178006 / 1000000000000) (23704178007 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 3) <| besselDerivativeNearFromState (1201823179947123 / 8000000000000) 3 (IntervalRat.scale (471 / 4) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (13952984279 / 1000000000000) (13952984280 / 1000000000000), orderedInterval (63538378183 / 1000000000000) (63538378184 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 3) <| besselDerivativeNearFromState (348335200857177 / 1600000000000) 3 (IntervalRat.scale (471 / 4) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-53438593604 / 1000000000000) (-53438593001 / 1000000000000), orderedInterval (8398006473 / 1000000000000) (8398007076 / 1000000000000)))) (orderedInterval (5327967799 / 1000000000000) (5327967936 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate242_chunkChecks3_2 :
    compactCertificate242.chunkChecks (3 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 3) <| besselDerivativeNearFromState (963513497448219 / 8000000000000) 3 (IntervalRat.scale (471 / 4) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (70025923689 / 1000000000000) (70025925078 / 1000000000000), orderedInterval (-19839368376 / 1000000000000) (-19839366987 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 3) <| besselDerivativeNearFromState (816781062406659 / 8000000000000) 3 (IntervalRat.scale (471 / 4) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (56134073787 / 1000000000000) (56134149559 / 1000000000000), orderedInterval (-55811969255 / 1000000000000) (-55811893483 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 3) <| besselDerivativeNearFromState (511103664493377 / 8000000000000) 3 (IntervalRat.scale (471 / 4) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (96238208621 / 1000000000000) (96238209583 / 1000000000000), orderedInterval (-27259239855 / 1000000000000) (-27259238893 / 1000000000000)))) (orderedInterval (-5423143306 / 1000000000000) (-5423140212 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 3) <| besselDerivativeNearFromState (274873250618559 / 8000000000000) 3 (IntervalRat.scale (471 / 4) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-74979074979 / 1000000000000) (-74979074978 / 1000000000000), orderedInterval (-112519405524 / 1000000000000) (-112519405523 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 3) <| besselDerivativeNearFromState (746334345892677 / 8000000000000) 3 (IntervalRat.scale (471 / 4) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-14132538535 / 1000000000000) (-14132538442 / 1000000000000), orderedInterval (81465709573 / 1000000000000) (81465709665 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 3) <| besselDerivativeNearFromState (1019055743230629 / 8000000000000) 3 (IntervalRat.scale (471 / 4) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (42156700887 / 1000000000000) (42156718050 / 1000000000000), orderedInterval (-56915331966 / 1000000000000) (-56915314802 / 1000000000000)))) (orderedInterval (-4683585444 / 1000000000000) (-4683583751 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 3) <| besselDerivativeNearFromState (430896335506623 / 8000000000000) 3 (IntervalRat.scale (471 / 4) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-102751628195 / 1000000000000) (-102751628194 / 1000000000000), orderedInterval (-34558966864 / 1000000000000) (-34558966862 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 3) <| besselDerivativeNearFromState (1751569681185183 / 8000000000000) 3 (IntervalRat.scale (471 / 4) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-9677523716 / 1000000000000) (-9677523674 / 1000000000000), orderedInterval (53069309199 / 1000000000000) (53069309241 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 3) <| besselDerivativeNearFromState (1169967372174897 / 8000000000000) 3 (IntervalRat.scale (471 / 4) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (38570682413 / 1000000000000) (38570696032 / 1000000000000), orderedInterval (-53661184564 / 1000000000000) (-53661170946 / 1000000000000)))) (orderedInterval (8430184955 / 1000000000000) (8430190011 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate242_chunkChecks3 :
    compactCertificate242.chunkChecks (3 : Fin 5) 0 9 = true :=
  compactCertificate242.chunkChecks_nine_of_three (3 : Fin 5) compactCertificate242_chunkChecks3_0
    compactCertificate242_chunkChecks3_1 compactCertificate242_chunkChecks3_2

theorem compactCertificate242_chunkChecks4_0 :
    compactCertificate242.chunkChecks (4 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 4) <| besselDerivativeNearFromState (471 / 4) 4 (IntervalRat.scale (471 / 4) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-55055247493 / 1000000000000) (-55055134397 / 1000000000000), orderedInterval (48972377235 / 1000000000000) (48972490332 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 4) <| besselDerivativeNearFromState (693872936461371 / 8000000000000) 4 (IntervalRat.scale (471 / 4) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-36995917054 / 1000000000000) (-36995914106 / 1000000000000), orderedInterval (77487314554 / 1000000000000) (77487317501 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 4) <| besselDerivativeNearFromState (224384251132443 / 1600000000000) 4 (IntervalRat.scale (471 / 4) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (22913315189 / 1000000000000) (22913315874 / 1000000000000), orderedInterval (-63441767793 / 1000000000000) (-63441767108 / 1000000000000)))) (orderedInterval (-18985985733 / 1000000000000) (-18985940049 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 4) <| besselDerivativeNearFromState (202470392315697 / 8000000000000) 4 (IntervalRat.scale (471 / 4) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (129594261474 / 1000000000000) (129594261475 / 1000000000000), orderedInterval (88861590651 / 1000000000000) (88861590652 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 4) <| besselDerivativeNearFromState (543863953576509 / 8000000000000) 4 (IntervalRat.scale (471 / 4) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-33043910842 / 1000000000000) (-33043909771 / 1000000000000), orderedInterval (91197354480 / 1000000000000) (91197355552 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 4) <| besselDerivativeNearFromState (1476696430566153 / 8000000000000) 4 (IntervalRat.scale (471 / 4) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-1045771554 / 1000000000000) (-1045771551 / 1000000000000), orderedInterval (-58715182985 / 1000000000000) (-58715182982 / 1000000000000)))) (orderedInterval (595770065 / 1000000000000) (595770123 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 4) <| besselDerivativeNearFromState (1087727907153489 / 8000000000000) 4 (IntervalRat.scale (471 / 4) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-68142075508 / 1000000000000) (-68142075351 / 1000000000000), orderedInterval (6481561522 / 1000000000000) (6481561679 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 4) <| besselDerivativeNearFromState (1863840308635797 / 8000000000000) 4 (IntervalRat.scale (471 / 4) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (50183010574 / 1000000000000) (50183010575 / 1000000000000), orderedInterval (14526780268 / 1000000000000) (14526780270 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 4) <| besselDerivativeNearFromState (1372896335506623 / 8000000000000) 4 (IntervalRat.scale (471 / 4) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (23205833286 / 1000000000000) (23205834248 / 1000000000000), orderedInterval (-56380536569 / 1000000000000) (-56380535607 / 1000000000000)))) (orderedInterval (-21321552455 / 1000000000000) (-21321552279 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate242_chunkChecks4_1 :
    compactCertificate242.chunkChecks (4 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 4) <| besselDerivativeNearFromState (2106376034804529 / 8000000000000) 4 (IntervalRat.scale (471 / 4) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (9196950030 / 1000000000000) (9196950031 / 1000000000000), orderedInterval (48286749915 / 1000000000000) (48286749916 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 4) <| besselDerivativeNearFromState (1216116770708841 / 8000000000000) 4 (IntervalRat.scale (471 / 4) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (58770397584 / 1000000000000) (58770406800 / 1000000000000), orderedInterval (-27284097554 / 1000000000000) (-27284088338 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 4) <| besselDerivativeNearFromState (2158020550433469 / 8000000000000) 4 (IntervalRat.scale (471 / 4) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (17137796738 / 1000000000000) (17137796739 / 1000000000000), orderedInterval (45424946947 / 1000000000000) (45424946948 / 1000000000000)))) (orderedInterval (37956297891 / 1000000000000) (37956300831 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 4) <| besselDerivativeNearFromState (2016302729278161 / 8000000000000) 4 (IntervalRat.scale (471 / 4) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (50115137790 / 1000000000000) (50115137823 / 1000000000000), orderedInterval (3689734867 / 1000000000000) (3689734900 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 4) <| besselDerivativeNearFromState (1438928768215713 / 8000000000000) 4 (IntervalRat.scale (471 / 4) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-59490292231 / 1000000000000) (-59490292163 / 1000000000000), orderedInterval (713989364 / 1000000000000) (713989431 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 4) <| besselDerivativeNearFromState (1631591860729527 / 8000000000000) 4 (IntervalRat.scale (471 / 4) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-28255973289 / 1000000000000) (-28255973288 / 1000000000000), orderedInterval (-48128968335 / 1000000000000) (-48128968334 / 1000000000000)))) (orderedInterval (-48313707793 / 1000000000000) (-48313707633 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 4) <| besselDerivativeNearFromState (1360251191473863 / 8000000000000) 4 (IntervalRat.scale (471 / 4) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (56341364652 / 1000000000000) (56341364653 / 1000000000000), orderedInterval (23704178006 / 1000000000000) (23704178007 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 4) <| besselDerivativeNearFromState (1201823179947123 / 8000000000000) 4 (IntervalRat.scale (471 / 4) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (13952984279 / 1000000000000) (13952984280 / 1000000000000), orderedInterval (63538378183 / 1000000000000) (63538378184 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 4) <| besselDerivativeNearFromState (348335200857177 / 1600000000000) 4 (IntervalRat.scale (471 / 4) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-53438593604 / 1000000000000) (-53438593001 / 1000000000000), orderedInterval (8398006473 / 1000000000000) (8398007076 / 1000000000000)))) (orderedInterval (-15366204487 / 1000000000000) (-15366204244 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate242_chunkChecks4_2 :
    compactCertificate242.chunkChecks (4 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 4) <| besselDerivativeNearFromState (963513497448219 / 8000000000000) 4 (IntervalRat.scale (471 / 4) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (70025923689 / 1000000000000) (70025925078 / 1000000000000), orderedInterval (-19839368376 / 1000000000000) (-19839366987 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 4) <| besselDerivativeNearFromState (816781062406659 / 8000000000000) 4 (IntervalRat.scale (471 / 4) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (56134073787 / 1000000000000) (56134149559 / 1000000000000), orderedInterval (-55811969255 / 1000000000000) (-55811893483 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 4) <| besselDerivativeNearFromState (511103664493377 / 8000000000000) 4 (IntervalRat.scale (471 / 4) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (96238208621 / 1000000000000) (96238209583 / 1000000000000), orderedInterval (-27259239855 / 1000000000000) (-27259238893 / 1000000000000)))) (orderedInterval (-13686271867 / 1000000000000) (-13686269121 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 4) <| besselDerivativeNearFromState (274873250618559 / 8000000000000) 4 (IntervalRat.scale (471 / 4) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-74979074979 / 1000000000000) (-74979074978 / 1000000000000), orderedInterval (-112519405524 / 1000000000000) (-112519405523 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 4) <| besselDerivativeNearFromState (746334345892677 / 8000000000000) 4 (IntervalRat.scale (471 / 4) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-14132538535 / 1000000000000) (-14132538442 / 1000000000000), orderedInterval (81465709573 / 1000000000000) (81465709665 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 4) <| besselDerivativeNearFromState (1019055743230629 / 8000000000000) 4 (IntervalRat.scale (471 / 4) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (42156700887 / 1000000000000) (42156718050 / 1000000000000), orderedInterval (-56915331966 / 1000000000000) (-56915314802 / 1000000000000)))) (orderedInterval (-4208736993 / 1000000000000) (-4208735149 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 4) <| besselDerivativeNearFromState (430896335506623 / 8000000000000) 4 (IntervalRat.scale (471 / 4) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-102751628195 / 1000000000000) (-102751628194 / 1000000000000), orderedInterval (-34558966864 / 1000000000000) (-34558966862 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 4) <| besselDerivativeNearFromState (1751569681185183 / 8000000000000) 4 (IntervalRat.scale (471 / 4) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-9677523716 / 1000000000000) (-9677523674 / 1000000000000), orderedInterval (53069309199 / 1000000000000) (53069309241 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 4) <| besselDerivativeNearFromState (1169967372174897 / 8000000000000) 4 (IntervalRat.scale (471 / 4) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (38570682413 / 1000000000000) (38570696032 / 1000000000000), orderedInterval (-53661184564 / 1000000000000) (-53661170946 / 1000000000000)))) (orderedInterval (-7973270826 / 1000000000000) (-7973264454 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate242_chunkChecks4 :
    compactCertificate242.chunkChecks (4 : Fin 5) 0 9 = true :=
  compactCertificate242.chunkChecks_nine_of_three (4 : Fin 5) compactCertificate242_chunkChecks4_0
    compactCertificate242_chunkChecks4_1 compactCertificate242_chunkChecks4_2

theorem compactCertificate242_chunks :
    ∀ r : Fin 5, ∀ b, compactCertificate242.chunkCheck r b = true :=
  compactCertificate242.chunkChecks_all (by
    intro r
    fin_cases r
    · exact compactCertificate242_chunkChecks0
    · exact compactCertificate242_chunkChecks1
    · exact compactCertificate242_chunkChecks2
    · exact compactCertificate242_chunkChecks3
    · exact compactCertificate242_chunkChecks4)

theorem compactCertificate242_coefficient0 :
    compactCertificate242.coefficientCheck (0 : Fin 5) = true := by
  norm_num [CompactCertificate.coefficientCheck, intervalFinSumHull,
    compactCertificate242, rationalIntervalSubset, orderedInterval, Fin.sum_univ_succ]

theorem compactCertificate242_coefficient1 :
    compactCertificate242.coefficientCheck (1 : Fin 5) = true := by
  norm_num [CompactCertificate.coefficientCheck, intervalFinSumHull,
    compactCertificate242, rationalIntervalSubset, orderedInterval, Fin.sum_univ_succ]

theorem compactCertificate242_coefficient2 :
    compactCertificate242.coefficientCheck (2 : Fin 5) = true := by
  norm_num [CompactCertificate.coefficientCheck, intervalFinSumHull,
    compactCertificate242, rationalIntervalSubset, orderedInterval, Fin.sum_univ_succ]

theorem compactCertificate242_coefficient3 :
    compactCertificate242.coefficientCheck (3 : Fin 5) = true := by
  norm_num [CompactCertificate.coefficientCheck, intervalFinSumHull,
    compactCertificate242, rationalIntervalSubset, orderedInterval, Fin.sum_univ_succ]

theorem compactCertificate242_coefficient4 :
    compactCertificate242.coefficientCheck (4 : Fin 5) = true := by
  norm_num [CompactCertificate.coefficientCheck, intervalFinSumHull,
    compactCertificate242, rationalIntervalSubset, orderedInterval, Fin.sum_univ_succ]

theorem compactCertificate242_coefficients : ∀ r : Fin 5,
    compactCertificate242.coefficientCheck r = true := by
  intro r
  fin_cases r
  · exact compactCertificate242_coefficient0
  · exact compactCertificate242_coefficient1
  · exact compactCertificate242_coefficient2
  · exact compactCertificate242_coefficient3
  · exact compactCertificate242_coefficient4

theorem compactCertificate242_lower : (1 : ℚ) ≤ compactCertificate242.output.lo := by
  norm_num [CompactCertificate.output, CompactCertificate.interval,
    CompactCertificate.coefficientTargetNat, compactCertificate242, dualConstant,
    intervalTaylorSum, intervalPow, intervalSub, intervalMaxAbs, widenInterval,
    rationalErrorInterval, orderedInterval, IntervalRat.add, IntervalRat.mul, IntervalRat.scale,
    IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4]

theorem compactCertificate242_proves {t : ℝ} (ht : t ∈ compactCertificate242.interval) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t :=
  compactCertificate242.proves compactCertificate242_states compactCertificate242_chunks
    compactCertificate242_coefficients compactCertificate242_lower ht

end Erdos232
