/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, OpenAI Codex
-/
import ErdosProblems.Erdos232.CompactBase

open LeanCert.Core
namespace Erdos232

def compactCertificate217 : CompactCertificate where
  left := 195 / 2
  right := 98
  center := 391 / 4
  grid := fun i =>
    match i.val with
    | 0 => 31
    | 1 => 23
    | 2 => 37
    | 3 => 7
    | 4 => 18
    | 5 => 49
    | 6 => 36
    | 7 => 62
    | 8 => 45
    | 9 => 70
    | 10 => 40
    | 11 => 71
    | 12 => 67
    | 13 => 48
    | 14 => 54
    | 15 => 45
    | 16 => 40
    | 17 => 58
    | 18 => 32
    | 19 => 27
    | 20 => 17
    | 21 => 9
    | 22 => 25
    | 23 => 34
    | 24 => 14
    | 25 => 58
    | _ => 39
  point := fun i =>
    match i.val with
    | 0 => 391 / 4
    | 1 => 576017660629291 / 8000000000000
    | 2 => 186272276417803 / 1600000000000
    | 3 => 168080516763137 / 8000000000000
    | 4 => 451487910506189 / 8000000000000
    | 5 => 1225877503930713 / 8000000000000
    | 6 => 902975821012769 / 8000000000000
    | 7 => 1547264460035237 / 8000000000000
    | 8 => 1139707998265583 / 8000000000000
    | 9 => 1748605158404609 / 8000000000000
    | 10 => 1009557658911161 / 8000000000000
    | 11 => 1791477781782349 / 8000000000000
    | 12 => 1673830928126881 / 8000000000000
    | 13 => 1194524731151473 / 8000000000000
    | 14 => 1354463731518567 / 8000000000000
    | 15 => 1129210649397623 / 8000000000000
    | 16 => 997691854266083 / 8000000000000
    | 17 => 289169986274217 / 1600000000000
    | 18 => 799859400217099 / 8000000000000
    | 19 => 678049671764339 / 8000000000000
    | 20 => 424292001734417 / 8000000000000
    | 21 => 228185649664239 / 8000000000000
    | 22 => 619568427269717 / 8000000000000
    | 23 => 845967718902709 / 8000000000000
    | 24 => 357707998265583 / 8000000000000
    | 25 => 1454063153595343 / 8000000000000
    | _ => 971246799406337 / 8000000000000
  state := fun i =>
    match i.val with
    | 0 => (orderedInterval (-73486773723 / 1000000000000) (-73486773722 / 1000000000000), orderedInterval (-32976363398 / 1000000000000) (-32976363397 / 1000000000000))
    | 1 => (orderedInterval (-47473038941 / 1000000000000) (-47473038940 / 1000000000000), orderedInterval (-80837372731 / 1000000000000) (-80837372730 / 1000000000000))
    | 2 => (orderedInterval (-60812476948 / 1000000000000) (-60812476947 / 1000000000000), orderedInterval (-41811612807 / 1000000000000) (-41811612806 / 1000000000000))
    | 3 => (orderedInterval (34855403874 / 1000000000000) (34855404091 / 1000000000000), orderedInterval (-171397695031 / 1000000000000) (-171397694814 / 1000000000000))
    | 4 => (orderedInterval (65995113741 / 1000000000000) (65995113742 / 1000000000000), orderedInterval (82632736048 / 1000000000000) (82632736049 / 1000000000000))
    | 5 => (orderedInterval (-5229994919 / 1000000000000) (-5229994917 / 1000000000000), orderedInterval (-64226299018 / 1000000000000) (-64226299016 / 1000000000000))
    | 6 => (orderedInterval (39824611451 / 1000000000000) (39824611452 / 1000000000000), orderedInterval (63496328661 / 1000000000000) (63496328662 / 1000000000000))
    | 7 => (orderedInterval (-31725653150 / 1000000000000) (-31725645824 / 1000000000000), orderedInterval (47884482708 / 1000000000000) (47884490034 / 1000000000000))
    | 8 => (orderedInterval (-63751395065 / 1000000000000) (-63751392764 / 1000000000000), orderedInterval (20333168395 / 1000000000000) (20333170696 / 1000000000000))
    | 9 => (orderedInterval (-28255204451 / 1000000000000) (-28255199988 / 1000000000000), orderedInterval (46045392116 / 1000000000000) (46045396579 / 1000000000000))
    | 10 => (orderedInterval (68722374653 / 1000000000000) (68722374655 / 1000000000000), orderedInterval (17670485531 / 1000000000000) (17670485533 / 1000000000000))
    | 11 => (orderedInterval (-53074696531 / 1000000000000) (-53074696230 / 1000000000000), orderedInterval (5212683529 / 1000000000000) (5212683830 / 1000000000000))
    | 12 => (orderedInterval (25130899187 / 1000000000000) (25130901190 / 1000000000000), orderedInterval (-49163403173 / 1000000000000) (-49163401171 / 1000000000000))
    | 13 => (orderedInterval (-41879497773 / 1000000000000) (-41879471216 / 1000000000000), orderedInterval (50237112281 / 1000000000000) (50237138838 / 1000000000000))
    | 14 => (orderedInterval (26485368244 / 1000000000000) (26485368245 / 1000000000000), orderedInterval (55226977531 / 1000000000000) (55226977532 / 1000000000000))
    | 15 => (orderedInterval (-35910485291 / 1000000000000) (-35910485290 / 1000000000000), orderedInterval (-56623499485 / 1000000000000) (-56623499484 / 1000000000000))
    | 16 => (orderedInterval (-11934660838 / 1000000000000) (-11934660768 / 1000000000000), orderedInterval (70491749858 / 1000000000000) (70491749928 / 1000000000000))
    | 17 => (orderedInterval (-38072014267 / 1000000000000) (-38071991310 / 1000000000000), orderedInterval (45635432589 / 1000000000000) (45635455546 / 1000000000000))
    | 18 => (orderedInterval (18626886769 / 1000000000000) (18626886770 / 1000000000000), orderedInterval (77498260831 / 1000000000000) (77498260832 / 1000000000000))
    | 19 => (orderedInterval (-56959281958 / 1000000000000) (-56959281957 / 1000000000000), orderedInterval (-64985088152 / 1000000000000) (-64985088151 / 1000000000000))
    | 20 => (orderedInterval (-43918458384 / 1000000000000) (-43918458383 / 1000000000000), orderedInterval (-99960087366 / 1000000000000) (-99960087365 / 1000000000000))
    | 21 => (orderedInterval (-128059394861 / 1000000000000) (-128059394860 / 1000000000000), orderedInterval (-74687947805 / 1000000000000) (-74687947804 / 1000000000000))
    | 22 => (orderedInterval (27656057514 / 1000000000000) (27656058151 / 1000000000000), orderedInterval (-86523505394 / 1000000000000) (-86523504757 / 1000000000000))
    | 23 => (orderedInterval (-21738242168 / 1000000000000) (-21738241782 / 1000000000000), orderedInterval (74586206410 / 1000000000000) (74586206796 / 1000000000000))
    | 24 => (orderedInterval (119124614614 / 1000000000000) (119124614623 / 1000000000000), orderedInterval (5464819622 / 1000000000000) (5464819631 / 1000000000000))
    | 25 => (orderedInterval (19190563519 / 1000000000000) (19190563520 / 1000000000000), orderedInterval (55932053884 / 1000000000000) (55932053885 / 1000000000000))
    | _ => (orderedInterval (23594803321 / 1000000000000) (23594803960 / 1000000000000), orderedInterval (-68559223657 / 1000000000000) (-68559223019 / 1000000000000))
  chunkTarget := fun r b =>
    match r.val with
    | 0 =>
      match b.val with
      | 0 => orderedInterval (-33138486655 / 1000000000000) (-33138486647 / 1000000000000)
      | 1 => orderedInterval (2403238863 / 1000000000000) (2403238878 / 1000000000000)
      | 2 => orderedInterval (-562199589 / 1000000000000) (-562199301 / 1000000000000)
      | 3 => orderedInterval (2567489482 / 1000000000000) (2567490358 / 1000000000000)
      | 4 => orderedInterval (-4547966882 / 1000000000000) (-4547964322 / 1000000000000)
      | 5 => orderedInterval (-706495412 / 1000000000000) (-706494810 / 1000000000000)
      | 6 => orderedInterval (-1184182887 / 1000000000000) (-1184182862 / 1000000000000)
      | 7 => orderedInterval (3403196814 / 1000000000000) (3403196871 / 1000000000000)
      | _ => orderedInterval (-5271034859 / 1000000000000) (-5271034711 / 1000000000000)
    | 1 =>
      match b.val with
      | 0 => orderedInterval (-16547694552 / 1000000000000) (-16547694543 / 1000000000000)
      | 1 => orderedInterval (9299057796 / 1000000000000) (9299057811 / 1000000000000)
      | 2 => orderedInterval (-2206092420 / 1000000000000) (-2206091882 / 1000000000000)
      | 3 => orderedInterval (-14907061092 / 1000000000000) (-14907059140 / 1000000000000)
      | 4 => orderedInterval (8672291936 / 1000000000000) (8672295870 / 1000000000000)
      | 5 => orderedInterval (-3930504373 / 1000000000000) (-3930503266 / 1000000000000)
      | 6 => orderedInterval (-11250817135 / 1000000000000) (-11250817111 / 1000000000000)
      | 7 => orderedInterval (-4226147359 / 1000000000000) (-4226147305 / 1000000000000)
      | _ => orderedInterval (7525756589 / 1000000000000) (7525756777 / 1000000000000)
    | 2 =>
      match b.val with
      | 0 => orderedInterval (34598788373 / 1000000000000) (34598788384 / 1000000000000)
      | 1 => orderedInterval (-1794527604 / 1000000000000) (-1794527584 / 1000000000000)
      | 2 => orderedInterval (-535608857 / 1000000000000) (-535607831 / 1000000000000)
      | 3 => orderedInterval (6160137062 / 1000000000000) (6160141444 / 1000000000000)
      | 4 => orderedInterval (11632532604 / 1000000000000) (11632538701 / 1000000000000)
      | 5 => orderedInterval (3125492924 / 1000000000000) (3125494972 / 1000000000000)
      | 6 => orderedInterval (1228129791 / 1000000000000) (1228129813 / 1000000000000)
      | 7 => orderedInterval (-1713954283 / 1000000000000) (-1713954228 / 1000000000000)
      | _ => orderedInterval (12002743546 / 1000000000000) (12002743790 / 1000000000000)
    | 3 =>
      match b.val with
      | 0 => orderedInterval (17161083888 / 1000000000000) (17161083900 / 1000000000000)
      | 1 => orderedInterval (-18168728476 / 1000000000000) (-18168728447 / 1000000000000)
      | 2 => orderedInterval (9924315764 / 1000000000000) (9924317728 / 1000000000000)
      | 3 => orderedInterval (79683458811 / 1000000000000) (79683468613 / 1000000000000)
      | 4 => orderedInterval (-24301748012 / 1000000000000) (-24301738592 / 1000000000000)
      | 5 => orderedInterval (2928581291 / 1000000000000) (2928585067 / 1000000000000)
      | 6 => orderedInterval (11368256417 / 1000000000000) (11368256440 / 1000000000000)
      | 7 => orderedInterval (6243424040 / 1000000000000) (6243424097 / 1000000000000)
      | _ => orderedInterval (4499952422 / 1000000000000) (4499952742 / 1000000000000)
    | _ =>
      match b.val with
      | 0 => orderedInterval (-36785500789 / 1000000000000) (-36785500776 / 1000000000000)
      | 1 => orderedInterval (2883738378 / 1000000000000) (2883738422 / 1000000000000)
      | 2 => orderedInterval (7842670879 / 1000000000000) (7842674690 / 1000000000000)
      | 3 => orderedInterval (-69782928332 / 1000000000000) (-69782906298 / 1000000000000)
      | 4 => orderedInterval (-31792297498 / 1000000000000) (-31792282785 / 1000000000000)
      | 5 => orderedInterval (-11444463841 / 1000000000000) (-11444456836 / 1000000000000)
      | 6 => orderedInterval (-1793987835 / 1000000000000) (-1793987813 / 1000000000000)
      | 7 => orderedInterval (1923715567 / 1000000000000) (1923715627 / 1000000000000)
      | _ => orderedInterval (-29267177092 / 1000000000000) (-29267176661 / 1000000000000)
  coefficientTarget := fun i =>
    match i.val with
    | 0 => orderedInterval (-37036441125 / 1000000000000) (-37036436546 / 1000000000000)
    | 1 => orderedInterval (-27571210610 / 1000000000000) (-27571202789 / 1000000000000)
    | 2 => orderedInterval (64703733556 / 1000000000000) (64703747461 / 1000000000000)
    | 3 => orderedInterval (89338596145 / 1000000000000) (89338621548 / 1000000000000)
    | _ => orderedInterval (-168216230563 / 1000000000000) (-168216182430 / 1000000000000)

theorem compactCertificate217_stateChecks0 :
    compactCertificate217.stateChecks 0 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 31 12 (391 / 4)) (orderedInterval (-73486773723 / 1000000000000) (-73486773722 / 1000000000000), orderedInterval (-32976363398 / 1000000000000) (-32976363397 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 23 12 (576017660629291 / 8000000000000)) (orderedInterval (-47473038941 / 1000000000000) (-47473038940 / 1000000000000), orderedInterval (-80837372731 / 1000000000000) (-80837372730 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 37 12 (186272276417803 / 1600000000000)) (orderedInterval (-60812476948 / 1000000000000) (-60812476947 / 1000000000000), orderedInterval (-41811612807 / 1000000000000) (-41811612806 / 1000000000000))) = true
  norm_num [besselStateAtRationalPoint, besselIntervalStepZero,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, besselZeroTransition,
    besselInitial, besselGridStateAt, besselGridStateBlock00, besselGridStateBlock01,
    besselGridStateBlock02, besselGridStateBlock03, besselGridStateBlock04,
    besselGridStateBlock05, besselGridStateBlock06, besselGridStateBlock07,
    besselGridStateBlock08, besselGridStateBlock09, besselGridStateBlock10,
    besselGridStateBlock11, besselGridStateBlock12, besselGridStateBlock13,
    besselGridStateBlock14, besselGridState007, besselGridState009, besselGridState014, besselGridState017, besselGridState018, besselGridState023, besselGridState025, besselGridState027, besselGridState031, besselGridState032, besselGridState034, besselGridState036, besselGridState037, besselGridState039, besselGridState040, besselGridState045, besselGridState048, besselGridState049, besselGridState054, besselGridState058, besselGridState062, besselGridState067, besselGridState070, besselGridState071, besselStateSubset, linearInterval, widenInterval,
    rationalErrorInterval, rationalIntervalSubset, orderedInterval, Finset.sum_range_succ,
    IntervalRat.add, IntervalRat.mul, IntervalRat.scale, IntervalRat.singleton]

theorem compactCertificate217_stateChecks1 :
    compactCertificate217.stateChecks 3 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 7 12 (168080516763137 / 8000000000000)) (orderedInterval (34855403874 / 1000000000000) (34855404091 / 1000000000000), orderedInterval (-171397695031 / 1000000000000) (-171397694814 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 18 12 (451487910506189 / 8000000000000)) (orderedInterval (65995113741 / 1000000000000) (65995113742 / 1000000000000), orderedInterval (82632736048 / 1000000000000) (82632736049 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 49 12 (1225877503930713 / 8000000000000)) (orderedInterval (-5229994919 / 1000000000000) (-5229994917 / 1000000000000), orderedInterval (-64226299018 / 1000000000000) (-64226299016 / 1000000000000))) = true
  norm_num [besselStateAtRationalPoint, besselIntervalStepZero,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, besselZeroTransition,
    besselInitial, besselGridStateAt, besselGridStateBlock00, besselGridStateBlock01,
    besselGridStateBlock02, besselGridStateBlock03, besselGridStateBlock04,
    besselGridStateBlock05, besselGridStateBlock06, besselGridStateBlock07,
    besselGridStateBlock08, besselGridStateBlock09, besselGridStateBlock10,
    besselGridStateBlock11, besselGridStateBlock12, besselGridStateBlock13,
    besselGridStateBlock14, besselGridState007, besselGridState009, besselGridState014, besselGridState017, besselGridState018, besselGridState023, besselGridState025, besselGridState027, besselGridState031, besselGridState032, besselGridState034, besselGridState036, besselGridState037, besselGridState039, besselGridState040, besselGridState045, besselGridState048, besselGridState049, besselGridState054, besselGridState058, besselGridState062, besselGridState067, besselGridState070, besselGridState071, besselStateSubset, linearInterval, widenInterval,
    rationalErrorInterval, rationalIntervalSubset, orderedInterval, Finset.sum_range_succ,
    IntervalRat.add, IntervalRat.mul, IntervalRat.scale, IntervalRat.singleton]

theorem compactCertificate217_stateChecks2 :
    compactCertificate217.stateChecks 6 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 36 12 (902975821012769 / 8000000000000)) (orderedInterval (39824611451 / 1000000000000) (39824611452 / 1000000000000), orderedInterval (63496328661 / 1000000000000) (63496328662 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 62 12 (1547264460035237 / 8000000000000)) (orderedInterval (-31725653150 / 1000000000000) (-31725645824 / 1000000000000), orderedInterval (47884482708 / 1000000000000) (47884490034 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 45 12 (1139707998265583 / 8000000000000)) (orderedInterval (-63751395065 / 1000000000000) (-63751392764 / 1000000000000), orderedInterval (20333168395 / 1000000000000) (20333170696 / 1000000000000))) = true
  norm_num [besselStateAtRationalPoint, besselIntervalStepZero,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, besselZeroTransition,
    besselInitial, besselGridStateAt, besselGridStateBlock00, besselGridStateBlock01,
    besselGridStateBlock02, besselGridStateBlock03, besselGridStateBlock04,
    besselGridStateBlock05, besselGridStateBlock06, besselGridStateBlock07,
    besselGridStateBlock08, besselGridStateBlock09, besselGridStateBlock10,
    besselGridStateBlock11, besselGridStateBlock12, besselGridStateBlock13,
    besselGridStateBlock14, besselGridState007, besselGridState009, besselGridState014, besselGridState017, besselGridState018, besselGridState023, besselGridState025, besselGridState027, besselGridState031, besselGridState032, besselGridState034, besselGridState036, besselGridState037, besselGridState039, besselGridState040, besselGridState045, besselGridState048, besselGridState049, besselGridState054, besselGridState058, besselGridState062, besselGridState067, besselGridState070, besselGridState071, besselStateSubset, linearInterval, widenInterval,
    rationalErrorInterval, rationalIntervalSubset, orderedInterval, Finset.sum_range_succ,
    IntervalRat.add, IntervalRat.mul, IntervalRat.scale, IntervalRat.singleton]

theorem compactCertificate217_stateChecks3 :
    compactCertificate217.stateChecks 9 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 70 12 (1748605158404609 / 8000000000000)) (orderedInterval (-28255204451 / 1000000000000) (-28255199988 / 1000000000000), orderedInterval (46045392116 / 1000000000000) (46045396579 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 40 12 (1009557658911161 / 8000000000000)) (orderedInterval (68722374653 / 1000000000000) (68722374655 / 1000000000000), orderedInterval (17670485531 / 1000000000000) (17670485533 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 71 12 (1791477781782349 / 8000000000000)) (orderedInterval (-53074696531 / 1000000000000) (-53074696230 / 1000000000000), orderedInterval (5212683529 / 1000000000000) (5212683830 / 1000000000000))) = true
  norm_num [besselStateAtRationalPoint, besselIntervalStepZero,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, besselZeroTransition,
    besselInitial, besselGridStateAt, besselGridStateBlock00, besselGridStateBlock01,
    besselGridStateBlock02, besselGridStateBlock03, besselGridStateBlock04,
    besselGridStateBlock05, besselGridStateBlock06, besselGridStateBlock07,
    besselGridStateBlock08, besselGridStateBlock09, besselGridStateBlock10,
    besselGridStateBlock11, besselGridStateBlock12, besselGridStateBlock13,
    besselGridStateBlock14, besselGridState007, besselGridState009, besselGridState014, besselGridState017, besselGridState018, besselGridState023, besselGridState025, besselGridState027, besselGridState031, besselGridState032, besselGridState034, besselGridState036, besselGridState037, besselGridState039, besselGridState040, besselGridState045, besselGridState048, besselGridState049, besselGridState054, besselGridState058, besselGridState062, besselGridState067, besselGridState070, besselGridState071, besselStateSubset, linearInterval, widenInterval,
    rationalErrorInterval, rationalIntervalSubset, orderedInterval, Finset.sum_range_succ,
    IntervalRat.add, IntervalRat.mul, IntervalRat.scale, IntervalRat.singleton]

theorem compactCertificate217_stateChecks4 :
    compactCertificate217.stateChecks 12 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 67 12 (1673830928126881 / 8000000000000)) (orderedInterval (25130899187 / 1000000000000) (25130901190 / 1000000000000), orderedInterval (-49163403173 / 1000000000000) (-49163401171 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 48 12 (1194524731151473 / 8000000000000)) (orderedInterval (-41879497773 / 1000000000000) (-41879471216 / 1000000000000), orderedInterval (50237112281 / 1000000000000) (50237138838 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 54 12 (1354463731518567 / 8000000000000)) (orderedInterval (26485368244 / 1000000000000) (26485368245 / 1000000000000), orderedInterval (55226977531 / 1000000000000) (55226977532 / 1000000000000))) = true
  norm_num [besselStateAtRationalPoint, besselIntervalStepZero,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, besselZeroTransition,
    besselInitial, besselGridStateAt, besselGridStateBlock00, besselGridStateBlock01,
    besselGridStateBlock02, besselGridStateBlock03, besselGridStateBlock04,
    besselGridStateBlock05, besselGridStateBlock06, besselGridStateBlock07,
    besselGridStateBlock08, besselGridStateBlock09, besselGridStateBlock10,
    besselGridStateBlock11, besselGridStateBlock12, besselGridStateBlock13,
    besselGridStateBlock14, besselGridState007, besselGridState009, besselGridState014, besselGridState017, besselGridState018, besselGridState023, besselGridState025, besselGridState027, besselGridState031, besselGridState032, besselGridState034, besselGridState036, besselGridState037, besselGridState039, besselGridState040, besselGridState045, besselGridState048, besselGridState049, besselGridState054, besselGridState058, besselGridState062, besselGridState067, besselGridState070, besselGridState071, besselStateSubset, linearInterval, widenInterval,
    rationalErrorInterval, rationalIntervalSubset, orderedInterval, Finset.sum_range_succ,
    IntervalRat.add, IntervalRat.mul, IntervalRat.scale, IntervalRat.singleton]

theorem compactCertificate217_stateChecks5 :
    compactCertificate217.stateChecks 15 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 45 12 (1129210649397623 / 8000000000000)) (orderedInterval (-35910485291 / 1000000000000) (-35910485290 / 1000000000000), orderedInterval (-56623499485 / 1000000000000) (-56623499484 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 40 12 (997691854266083 / 8000000000000)) (orderedInterval (-11934660838 / 1000000000000) (-11934660768 / 1000000000000), orderedInterval (70491749858 / 1000000000000) (70491749928 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 58 12 (289169986274217 / 1600000000000)) (orderedInterval (-38072014267 / 1000000000000) (-38071991310 / 1000000000000), orderedInterval (45635432589 / 1000000000000) (45635455546 / 1000000000000))) = true
  norm_num [besselStateAtRationalPoint, besselIntervalStepZero,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, besselZeroTransition,
    besselInitial, besselGridStateAt, besselGridStateBlock00, besselGridStateBlock01,
    besselGridStateBlock02, besselGridStateBlock03, besselGridStateBlock04,
    besselGridStateBlock05, besselGridStateBlock06, besselGridStateBlock07,
    besselGridStateBlock08, besselGridStateBlock09, besselGridStateBlock10,
    besselGridStateBlock11, besselGridStateBlock12, besselGridStateBlock13,
    besselGridStateBlock14, besselGridState007, besselGridState009, besselGridState014, besselGridState017, besselGridState018, besselGridState023, besselGridState025, besselGridState027, besselGridState031, besselGridState032, besselGridState034, besselGridState036, besselGridState037, besselGridState039, besselGridState040, besselGridState045, besselGridState048, besselGridState049, besselGridState054, besselGridState058, besselGridState062, besselGridState067, besselGridState070, besselGridState071, besselStateSubset, linearInterval, widenInterval,
    rationalErrorInterval, rationalIntervalSubset, orderedInterval, Finset.sum_range_succ,
    IntervalRat.add, IntervalRat.mul, IntervalRat.scale, IntervalRat.singleton]

theorem compactCertificate217_stateChecks6 :
    compactCertificate217.stateChecks 18 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 32 12 (799859400217099 / 8000000000000)) (orderedInterval (18626886769 / 1000000000000) (18626886770 / 1000000000000), orderedInterval (77498260831 / 1000000000000) (77498260832 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 27 12 (678049671764339 / 8000000000000)) (orderedInterval (-56959281958 / 1000000000000) (-56959281957 / 1000000000000), orderedInterval (-64985088152 / 1000000000000) (-64985088151 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 17 12 (424292001734417 / 8000000000000)) (orderedInterval (-43918458384 / 1000000000000) (-43918458383 / 1000000000000), orderedInterval (-99960087366 / 1000000000000) (-99960087365 / 1000000000000))) = true
  norm_num [besselStateAtRationalPoint, besselIntervalStepZero,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, besselZeroTransition,
    besselInitial, besselGridStateAt, besselGridStateBlock00, besselGridStateBlock01,
    besselGridStateBlock02, besselGridStateBlock03, besselGridStateBlock04,
    besselGridStateBlock05, besselGridStateBlock06, besselGridStateBlock07,
    besselGridStateBlock08, besselGridStateBlock09, besselGridStateBlock10,
    besselGridStateBlock11, besselGridStateBlock12, besselGridStateBlock13,
    besselGridStateBlock14, besselGridState007, besselGridState009, besselGridState014, besselGridState017, besselGridState018, besselGridState023, besselGridState025, besselGridState027, besselGridState031, besselGridState032, besselGridState034, besselGridState036, besselGridState037, besselGridState039, besselGridState040, besselGridState045, besselGridState048, besselGridState049, besselGridState054, besselGridState058, besselGridState062, besselGridState067, besselGridState070, besselGridState071, besselStateSubset, linearInterval, widenInterval,
    rationalErrorInterval, rationalIntervalSubset, orderedInterval, Finset.sum_range_succ,
    IntervalRat.add, IntervalRat.mul, IntervalRat.scale, IntervalRat.singleton]

theorem compactCertificate217_stateChecks7 :
    compactCertificate217.stateChecks 21 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 9 12 (228185649664239 / 8000000000000)) (orderedInterval (-128059394861 / 1000000000000) (-128059394860 / 1000000000000), orderedInterval (-74687947805 / 1000000000000) (-74687947804 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 25 12 (619568427269717 / 8000000000000)) (orderedInterval (27656057514 / 1000000000000) (27656058151 / 1000000000000), orderedInterval (-86523505394 / 1000000000000) (-86523504757 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 34 12 (845967718902709 / 8000000000000)) (orderedInterval (-21738242168 / 1000000000000) (-21738241782 / 1000000000000), orderedInterval (74586206410 / 1000000000000) (74586206796 / 1000000000000))) = true
  norm_num [besselStateAtRationalPoint, besselIntervalStepZero,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, besselZeroTransition,
    besselInitial, besselGridStateAt, besselGridStateBlock00, besselGridStateBlock01,
    besselGridStateBlock02, besselGridStateBlock03, besselGridStateBlock04,
    besselGridStateBlock05, besselGridStateBlock06, besselGridStateBlock07,
    besselGridStateBlock08, besselGridStateBlock09, besselGridStateBlock10,
    besselGridStateBlock11, besselGridStateBlock12, besselGridStateBlock13,
    besselGridStateBlock14, besselGridState007, besselGridState009, besselGridState014, besselGridState017, besselGridState018, besselGridState023, besselGridState025, besselGridState027, besselGridState031, besselGridState032, besselGridState034, besselGridState036, besselGridState037, besselGridState039, besselGridState040, besselGridState045, besselGridState048, besselGridState049, besselGridState054, besselGridState058, besselGridState062, besselGridState067, besselGridState070, besselGridState071, besselStateSubset, linearInterval, widenInterval,
    rationalErrorInterval, rationalIntervalSubset, orderedInterval, Finset.sum_range_succ,
    IntervalRat.add, IntervalRat.mul, IntervalRat.scale, IntervalRat.singleton]

theorem compactCertificate217_stateChecks8 :
    compactCertificate217.stateChecks 24 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 14 12 (357707998265583 / 8000000000000)) (orderedInterval (119124614614 / 1000000000000) (119124614623 / 1000000000000), orderedInterval (5464819622 / 1000000000000) (5464819631 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 58 12 (1454063153595343 / 8000000000000)) (orderedInterval (19190563519 / 1000000000000) (19190563520 / 1000000000000), orderedInterval (55932053884 / 1000000000000) (55932053885 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 39 12 (971246799406337 / 8000000000000)) (orderedInterval (23594803321 / 1000000000000) (23594803960 / 1000000000000), orderedInterval (-68559223657 / 1000000000000) (-68559223019 / 1000000000000))) = true
  norm_num [besselStateAtRationalPoint, besselIntervalStepZero,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, besselZeroTransition,
    besselInitial, besselGridStateAt, besselGridStateBlock00, besselGridStateBlock01,
    besselGridStateBlock02, besselGridStateBlock03, besselGridStateBlock04,
    besselGridStateBlock05, besselGridStateBlock06, besselGridStateBlock07,
    besselGridStateBlock08, besselGridStateBlock09, besselGridStateBlock10,
    besselGridStateBlock11, besselGridStateBlock12, besselGridStateBlock13,
    besselGridStateBlock14, besselGridState007, besselGridState009, besselGridState014, besselGridState017, besselGridState018, besselGridState023, besselGridState025, besselGridState027, besselGridState031, besselGridState032, besselGridState034, besselGridState036, besselGridState037, besselGridState039, besselGridState040, besselGridState045, besselGridState048, besselGridState049, besselGridState054, besselGridState058, besselGridState062, besselGridState067, besselGridState070, besselGridState071, besselStateSubset, linearInterval, widenInterval,
    rationalErrorInterval, rationalIntervalSubset, orderedInterval, Finset.sum_range_succ,
    IntervalRat.add, IntervalRat.mul, IntervalRat.scale, IntervalRat.singleton]

theorem compactCertificate217_states : ∀ j,
    BesselStateValid (compactCertificate217.point j) (compactCertificate217.state j) :=
  compactCertificate217.statesValid_of_checks3 compactCertificate217_stateChecks0
    compactCertificate217_stateChecks1 compactCertificate217_stateChecks2
    compactCertificate217_stateChecks3 compactCertificate217_stateChecks4
    compactCertificate217_stateChecks5 compactCertificate217_stateChecks6
    compactCertificate217_stateChecks7 compactCertificate217_stateChecks8

theorem compactCertificate217_chunkChecks0_0 :
    compactCertificate217.chunkChecks (0 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 0) <| besselDerivativeNearFromState (391 / 4) 0 (IntervalRat.scale (391 / 4) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-73486773723 / 1000000000000) (-73486773722 / 1000000000000), orderedInterval (-32976363398 / 1000000000000) (-32976363397 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 0) <| besselDerivativeNearFromState (576017660629291 / 8000000000000) 0 (IntervalRat.scale (391 / 4) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-47473038941 / 1000000000000) (-47473038940 / 1000000000000), orderedInterval (-80837372731 / 1000000000000) (-80837372730 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 0) <| besselDerivativeNearFromState (186272276417803 / 1600000000000) 0 (IntervalRat.scale (391 / 4) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-60812476948 / 1000000000000) (-60812476947 / 1000000000000), orderedInterval (-41811612807 / 1000000000000) (-41811612806 / 1000000000000)))) (orderedInterval (-33138486655 / 1000000000000) (-33138486647 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 0) <| besselDerivativeNearFromState (168080516763137 / 8000000000000) 0 (IntervalRat.scale (391 / 4) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (34855403874 / 1000000000000) (34855404091 / 1000000000000), orderedInterval (-171397695031 / 1000000000000) (-171397694814 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 0) <| besselDerivativeNearFromState (451487910506189 / 8000000000000) 0 (IntervalRat.scale (391 / 4) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (65995113741 / 1000000000000) (65995113742 / 1000000000000), orderedInterval (82632736048 / 1000000000000) (82632736049 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 0) <| besselDerivativeNearFromState (1225877503930713 / 8000000000000) 0 (IntervalRat.scale (391 / 4) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-5229994919 / 1000000000000) (-5229994917 / 1000000000000), orderedInterval (-64226299018 / 1000000000000) (-64226299016 / 1000000000000)))) (orderedInterval (2403238863 / 1000000000000) (2403238878 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 0) <| besselDerivativeNearFromState (902975821012769 / 8000000000000) 0 (IntervalRat.scale (391 / 4) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (39824611451 / 1000000000000) (39824611452 / 1000000000000), orderedInterval (63496328661 / 1000000000000) (63496328662 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 0) <| besselDerivativeNearFromState (1547264460035237 / 8000000000000) 0 (IntervalRat.scale (391 / 4) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-31725653150 / 1000000000000) (-31725645824 / 1000000000000), orderedInterval (47884482708 / 1000000000000) (47884490034 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 0) <| besselDerivativeNearFromState (1139707998265583 / 8000000000000) 0 (IntervalRat.scale (391 / 4) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-63751395065 / 1000000000000) (-63751392764 / 1000000000000), orderedInterval (20333168395 / 1000000000000) (20333170696 / 1000000000000)))) (orderedInterval (-562199589 / 1000000000000) (-562199301 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate217_chunkChecks0_1 :
    compactCertificate217.chunkChecks (0 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 0) <| besselDerivativeNearFromState (1748605158404609 / 8000000000000) 0 (IntervalRat.scale (391 / 4) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-28255204451 / 1000000000000) (-28255199988 / 1000000000000), orderedInterval (46045392116 / 1000000000000) (46045396579 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 0) <| besselDerivativeNearFromState (1009557658911161 / 8000000000000) 0 (IntervalRat.scale (391 / 4) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (68722374653 / 1000000000000) (68722374655 / 1000000000000), orderedInterval (17670485531 / 1000000000000) (17670485533 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 0) <| besselDerivativeNearFromState (1791477781782349 / 8000000000000) 0 (IntervalRat.scale (391 / 4) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-53074696531 / 1000000000000) (-53074696230 / 1000000000000), orderedInterval (5212683529 / 1000000000000) (5212683830 / 1000000000000)))) (orderedInterval (2567489482 / 1000000000000) (2567490358 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 0) <| besselDerivativeNearFromState (1673830928126881 / 8000000000000) 0 (IntervalRat.scale (391 / 4) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (25130899187 / 1000000000000) (25130901190 / 1000000000000), orderedInterval (-49163403173 / 1000000000000) (-49163401171 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 0) <| besselDerivativeNearFromState (1194524731151473 / 8000000000000) 0 (IntervalRat.scale (391 / 4) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-41879497773 / 1000000000000) (-41879471216 / 1000000000000), orderedInterval (50237112281 / 1000000000000) (50237138838 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 0) <| besselDerivativeNearFromState (1354463731518567 / 8000000000000) 0 (IntervalRat.scale (391 / 4) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (26485368244 / 1000000000000) (26485368245 / 1000000000000), orderedInterval (55226977531 / 1000000000000) (55226977532 / 1000000000000)))) (orderedInterval (-4547966882 / 1000000000000) (-4547964322 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 0) <| besselDerivativeNearFromState (1129210649397623 / 8000000000000) 0 (IntervalRat.scale (391 / 4) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-35910485291 / 1000000000000) (-35910485290 / 1000000000000), orderedInterval (-56623499485 / 1000000000000) (-56623499484 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 0) <| besselDerivativeNearFromState (997691854266083 / 8000000000000) 0 (IntervalRat.scale (391 / 4) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-11934660838 / 1000000000000) (-11934660768 / 1000000000000), orderedInterval (70491749858 / 1000000000000) (70491749928 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 0) <| besselDerivativeNearFromState (289169986274217 / 1600000000000) 0 (IntervalRat.scale (391 / 4) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-38072014267 / 1000000000000) (-38071991310 / 1000000000000), orderedInterval (45635432589 / 1000000000000) (45635455546 / 1000000000000)))) (orderedInterval (-706495412 / 1000000000000) (-706494810 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate217_chunkChecks0_2 :
    compactCertificate217.chunkChecks (0 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 0) <| besselDerivativeNearFromState (799859400217099 / 8000000000000) 0 (IntervalRat.scale (391 / 4) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (18626886769 / 1000000000000) (18626886770 / 1000000000000), orderedInterval (77498260831 / 1000000000000) (77498260832 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 0) <| besselDerivativeNearFromState (678049671764339 / 8000000000000) 0 (IntervalRat.scale (391 / 4) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-56959281958 / 1000000000000) (-56959281957 / 1000000000000), orderedInterval (-64985088152 / 1000000000000) (-64985088151 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 0) <| besselDerivativeNearFromState (424292001734417 / 8000000000000) 0 (IntervalRat.scale (391 / 4) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-43918458384 / 1000000000000) (-43918458383 / 1000000000000), orderedInterval (-99960087366 / 1000000000000) (-99960087365 / 1000000000000)))) (orderedInterval (-1184182887 / 1000000000000) (-1184182862 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 0) <| besselDerivativeNearFromState (228185649664239 / 8000000000000) 0 (IntervalRat.scale (391 / 4) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-128059394861 / 1000000000000) (-128059394860 / 1000000000000), orderedInterval (-74687947805 / 1000000000000) (-74687947804 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 0) <| besselDerivativeNearFromState (619568427269717 / 8000000000000) 0 (IntervalRat.scale (391 / 4) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (27656057514 / 1000000000000) (27656058151 / 1000000000000), orderedInterval (-86523505394 / 1000000000000) (-86523504757 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 0) <| besselDerivativeNearFromState (845967718902709 / 8000000000000) 0 (IntervalRat.scale (391 / 4) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-21738242168 / 1000000000000) (-21738241782 / 1000000000000), orderedInterval (74586206410 / 1000000000000) (74586206796 / 1000000000000)))) (orderedInterval (3403196814 / 1000000000000) (3403196871 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 0) <| besselDerivativeNearFromState (357707998265583 / 8000000000000) 0 (IntervalRat.scale (391 / 4) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (119124614614 / 1000000000000) (119124614623 / 1000000000000), orderedInterval (5464819622 / 1000000000000) (5464819631 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 0) <| besselDerivativeNearFromState (1454063153595343 / 8000000000000) 0 (IntervalRat.scale (391 / 4) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (19190563519 / 1000000000000) (19190563520 / 1000000000000), orderedInterval (55932053884 / 1000000000000) (55932053885 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 0) <| besselDerivativeNearFromState (971246799406337 / 8000000000000) 0 (IntervalRat.scale (391 / 4) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (23594803321 / 1000000000000) (23594803960 / 1000000000000), orderedInterval (-68559223657 / 1000000000000) (-68559223019 / 1000000000000)))) (orderedInterval (-5271034859 / 1000000000000) (-5271034711 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate217_chunkChecks0 :
    compactCertificate217.chunkChecks (0 : Fin 5) 0 9 = true :=
  compactCertificate217.chunkChecks_nine_of_three (0 : Fin 5) compactCertificate217_chunkChecks0_0
    compactCertificate217_chunkChecks0_1 compactCertificate217_chunkChecks0_2

theorem compactCertificate217_chunkChecks1_0 :
    compactCertificate217.chunkChecks (1 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 1) <| besselDerivativeNearFromState (391 / 4) 1 (IntervalRat.scale (391 / 4) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-73486773723 / 1000000000000) (-73486773722 / 1000000000000), orderedInterval (-32976363398 / 1000000000000) (-32976363397 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 1) <| besselDerivativeNearFromState (576017660629291 / 8000000000000) 1 (IntervalRat.scale (391 / 4) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-47473038941 / 1000000000000) (-47473038940 / 1000000000000), orderedInterval (-80837372731 / 1000000000000) (-80837372730 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 1) <| besselDerivativeNearFromState (186272276417803 / 1600000000000) 1 (IntervalRat.scale (391 / 4) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-60812476948 / 1000000000000) (-60812476947 / 1000000000000), orderedInterval (-41811612807 / 1000000000000) (-41811612806 / 1000000000000)))) (orderedInterval (-16547694552 / 1000000000000) (-16547694543 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 1) <| besselDerivativeNearFromState (168080516763137 / 8000000000000) 1 (IntervalRat.scale (391 / 4) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (34855403874 / 1000000000000) (34855404091 / 1000000000000), orderedInterval (-171397695031 / 1000000000000) (-171397694814 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 1) <| besselDerivativeNearFromState (451487910506189 / 8000000000000) 1 (IntervalRat.scale (391 / 4) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (65995113741 / 1000000000000) (65995113742 / 1000000000000), orderedInterval (82632736048 / 1000000000000) (82632736049 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 1) <| besselDerivativeNearFromState (1225877503930713 / 8000000000000) 1 (IntervalRat.scale (391 / 4) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-5229994919 / 1000000000000) (-5229994917 / 1000000000000), orderedInterval (-64226299018 / 1000000000000) (-64226299016 / 1000000000000)))) (orderedInterval (9299057796 / 1000000000000) (9299057811 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 1) <| besselDerivativeNearFromState (902975821012769 / 8000000000000) 1 (IntervalRat.scale (391 / 4) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (39824611451 / 1000000000000) (39824611452 / 1000000000000), orderedInterval (63496328661 / 1000000000000) (63496328662 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 1) <| besselDerivativeNearFromState (1547264460035237 / 8000000000000) 1 (IntervalRat.scale (391 / 4) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-31725653150 / 1000000000000) (-31725645824 / 1000000000000), orderedInterval (47884482708 / 1000000000000) (47884490034 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 1) <| besselDerivativeNearFromState (1139707998265583 / 8000000000000) 1 (IntervalRat.scale (391 / 4) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-63751395065 / 1000000000000) (-63751392764 / 1000000000000), orderedInterval (20333168395 / 1000000000000) (20333170696 / 1000000000000)))) (orderedInterval (-2206092420 / 1000000000000) (-2206091882 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate217_chunkChecks1_1 :
    compactCertificate217.chunkChecks (1 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 1) <| besselDerivativeNearFromState (1748605158404609 / 8000000000000) 1 (IntervalRat.scale (391 / 4) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-28255204451 / 1000000000000) (-28255199988 / 1000000000000), orderedInterval (46045392116 / 1000000000000) (46045396579 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 1) <| besselDerivativeNearFromState (1009557658911161 / 8000000000000) 1 (IntervalRat.scale (391 / 4) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (68722374653 / 1000000000000) (68722374655 / 1000000000000), orderedInterval (17670485531 / 1000000000000) (17670485533 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 1) <| besselDerivativeNearFromState (1791477781782349 / 8000000000000) 1 (IntervalRat.scale (391 / 4) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-53074696531 / 1000000000000) (-53074696230 / 1000000000000), orderedInterval (5212683529 / 1000000000000) (5212683830 / 1000000000000)))) (orderedInterval (-14907061092 / 1000000000000) (-14907059140 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 1) <| besselDerivativeNearFromState (1673830928126881 / 8000000000000) 1 (IntervalRat.scale (391 / 4) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (25130899187 / 1000000000000) (25130901190 / 1000000000000), orderedInterval (-49163403173 / 1000000000000) (-49163401171 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 1) <| besselDerivativeNearFromState (1194524731151473 / 8000000000000) 1 (IntervalRat.scale (391 / 4) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-41879497773 / 1000000000000) (-41879471216 / 1000000000000), orderedInterval (50237112281 / 1000000000000) (50237138838 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 1) <| besselDerivativeNearFromState (1354463731518567 / 8000000000000) 1 (IntervalRat.scale (391 / 4) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (26485368244 / 1000000000000) (26485368245 / 1000000000000), orderedInterval (55226977531 / 1000000000000) (55226977532 / 1000000000000)))) (orderedInterval (8672291936 / 1000000000000) (8672295870 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 1) <| besselDerivativeNearFromState (1129210649397623 / 8000000000000) 1 (IntervalRat.scale (391 / 4) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-35910485291 / 1000000000000) (-35910485290 / 1000000000000), orderedInterval (-56623499485 / 1000000000000) (-56623499484 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 1) <| besselDerivativeNearFromState (997691854266083 / 8000000000000) 1 (IntervalRat.scale (391 / 4) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-11934660838 / 1000000000000) (-11934660768 / 1000000000000), orderedInterval (70491749858 / 1000000000000) (70491749928 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 1) <| besselDerivativeNearFromState (289169986274217 / 1600000000000) 1 (IntervalRat.scale (391 / 4) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-38072014267 / 1000000000000) (-38071991310 / 1000000000000), orderedInterval (45635432589 / 1000000000000) (45635455546 / 1000000000000)))) (orderedInterval (-3930504373 / 1000000000000) (-3930503266 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate217_chunkChecks1_2 :
    compactCertificate217.chunkChecks (1 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 1) <| besselDerivativeNearFromState (799859400217099 / 8000000000000) 1 (IntervalRat.scale (391 / 4) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (18626886769 / 1000000000000) (18626886770 / 1000000000000), orderedInterval (77498260831 / 1000000000000) (77498260832 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 1) <| besselDerivativeNearFromState (678049671764339 / 8000000000000) 1 (IntervalRat.scale (391 / 4) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-56959281958 / 1000000000000) (-56959281957 / 1000000000000), orderedInterval (-64985088152 / 1000000000000) (-64985088151 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 1) <| besselDerivativeNearFromState (424292001734417 / 8000000000000) 1 (IntervalRat.scale (391 / 4) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-43918458384 / 1000000000000) (-43918458383 / 1000000000000), orderedInterval (-99960087366 / 1000000000000) (-99960087365 / 1000000000000)))) (orderedInterval (-11250817135 / 1000000000000) (-11250817111 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 1) <| besselDerivativeNearFromState (228185649664239 / 8000000000000) 1 (IntervalRat.scale (391 / 4) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-128059394861 / 1000000000000) (-128059394860 / 1000000000000), orderedInterval (-74687947805 / 1000000000000) (-74687947804 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 1) <| besselDerivativeNearFromState (619568427269717 / 8000000000000) 1 (IntervalRat.scale (391 / 4) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (27656057514 / 1000000000000) (27656058151 / 1000000000000), orderedInterval (-86523505394 / 1000000000000) (-86523504757 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 1) <| besselDerivativeNearFromState (845967718902709 / 8000000000000) 1 (IntervalRat.scale (391 / 4) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-21738242168 / 1000000000000) (-21738241782 / 1000000000000), orderedInterval (74586206410 / 1000000000000) (74586206796 / 1000000000000)))) (orderedInterval (-4226147359 / 1000000000000) (-4226147305 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 1) <| besselDerivativeNearFromState (357707998265583 / 8000000000000) 1 (IntervalRat.scale (391 / 4) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (119124614614 / 1000000000000) (119124614623 / 1000000000000), orderedInterval (5464819622 / 1000000000000) (5464819631 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 1) <| besselDerivativeNearFromState (1454063153595343 / 8000000000000) 1 (IntervalRat.scale (391 / 4) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (19190563519 / 1000000000000) (19190563520 / 1000000000000), orderedInterval (55932053884 / 1000000000000) (55932053885 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 1) <| besselDerivativeNearFromState (971246799406337 / 8000000000000) 1 (IntervalRat.scale (391 / 4) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (23594803321 / 1000000000000) (23594803960 / 1000000000000), orderedInterval (-68559223657 / 1000000000000) (-68559223019 / 1000000000000)))) (orderedInterval (7525756589 / 1000000000000) (7525756777 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate217_chunkChecks1 :
    compactCertificate217.chunkChecks (1 : Fin 5) 0 9 = true :=
  compactCertificate217.chunkChecks_nine_of_three (1 : Fin 5) compactCertificate217_chunkChecks1_0
    compactCertificate217_chunkChecks1_1 compactCertificate217_chunkChecks1_2

theorem compactCertificate217_chunkChecks2_0 :
    compactCertificate217.chunkChecks (2 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 2) <| besselDerivativeNearFromState (391 / 4) 2 (IntervalRat.scale (391 / 4) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-73486773723 / 1000000000000) (-73486773722 / 1000000000000), orderedInterval (-32976363398 / 1000000000000) (-32976363397 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 2) <| besselDerivativeNearFromState (576017660629291 / 8000000000000) 2 (IntervalRat.scale (391 / 4) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-47473038941 / 1000000000000) (-47473038940 / 1000000000000), orderedInterval (-80837372731 / 1000000000000) (-80837372730 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 2) <| besselDerivativeNearFromState (186272276417803 / 1600000000000) 2 (IntervalRat.scale (391 / 4) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-60812476948 / 1000000000000) (-60812476947 / 1000000000000), orderedInterval (-41811612807 / 1000000000000) (-41811612806 / 1000000000000)))) (orderedInterval (34598788373 / 1000000000000) (34598788384 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 2) <| besselDerivativeNearFromState (168080516763137 / 8000000000000) 2 (IntervalRat.scale (391 / 4) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (34855403874 / 1000000000000) (34855404091 / 1000000000000), orderedInterval (-171397695031 / 1000000000000) (-171397694814 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 2) <| besselDerivativeNearFromState (451487910506189 / 8000000000000) 2 (IntervalRat.scale (391 / 4) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (65995113741 / 1000000000000) (65995113742 / 1000000000000), orderedInterval (82632736048 / 1000000000000) (82632736049 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 2) <| besselDerivativeNearFromState (1225877503930713 / 8000000000000) 2 (IntervalRat.scale (391 / 4) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-5229994919 / 1000000000000) (-5229994917 / 1000000000000), orderedInterval (-64226299018 / 1000000000000) (-64226299016 / 1000000000000)))) (orderedInterval (-1794527604 / 1000000000000) (-1794527584 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 2) <| besselDerivativeNearFromState (902975821012769 / 8000000000000) 2 (IntervalRat.scale (391 / 4) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (39824611451 / 1000000000000) (39824611452 / 1000000000000), orderedInterval (63496328661 / 1000000000000) (63496328662 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 2) <| besselDerivativeNearFromState (1547264460035237 / 8000000000000) 2 (IntervalRat.scale (391 / 4) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-31725653150 / 1000000000000) (-31725645824 / 1000000000000), orderedInterval (47884482708 / 1000000000000) (47884490034 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 2) <| besselDerivativeNearFromState (1139707998265583 / 8000000000000) 2 (IntervalRat.scale (391 / 4) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-63751395065 / 1000000000000) (-63751392764 / 1000000000000), orderedInterval (20333168395 / 1000000000000) (20333170696 / 1000000000000)))) (orderedInterval (-535608857 / 1000000000000) (-535607831 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate217_chunkChecks2_1 :
    compactCertificate217.chunkChecks (2 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 2) <| besselDerivativeNearFromState (1748605158404609 / 8000000000000) 2 (IntervalRat.scale (391 / 4) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-28255204451 / 1000000000000) (-28255199988 / 1000000000000), orderedInterval (46045392116 / 1000000000000) (46045396579 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 2) <| besselDerivativeNearFromState (1009557658911161 / 8000000000000) 2 (IntervalRat.scale (391 / 4) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (68722374653 / 1000000000000) (68722374655 / 1000000000000), orderedInterval (17670485531 / 1000000000000) (17670485533 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 2) <| besselDerivativeNearFromState (1791477781782349 / 8000000000000) 2 (IntervalRat.scale (391 / 4) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-53074696531 / 1000000000000) (-53074696230 / 1000000000000), orderedInterval (5212683529 / 1000000000000) (5212683830 / 1000000000000)))) (orderedInterval (6160137062 / 1000000000000) (6160141444 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 2) <| besselDerivativeNearFromState (1673830928126881 / 8000000000000) 2 (IntervalRat.scale (391 / 4) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (25130899187 / 1000000000000) (25130901190 / 1000000000000), orderedInterval (-49163403173 / 1000000000000) (-49163401171 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 2) <| besselDerivativeNearFromState (1194524731151473 / 8000000000000) 2 (IntervalRat.scale (391 / 4) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-41879497773 / 1000000000000) (-41879471216 / 1000000000000), orderedInterval (50237112281 / 1000000000000) (50237138838 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 2) <| besselDerivativeNearFromState (1354463731518567 / 8000000000000) 2 (IntervalRat.scale (391 / 4) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (26485368244 / 1000000000000) (26485368245 / 1000000000000), orderedInterval (55226977531 / 1000000000000) (55226977532 / 1000000000000)))) (orderedInterval (11632532604 / 1000000000000) (11632538701 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 2) <| besselDerivativeNearFromState (1129210649397623 / 8000000000000) 2 (IntervalRat.scale (391 / 4) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-35910485291 / 1000000000000) (-35910485290 / 1000000000000), orderedInterval (-56623499485 / 1000000000000) (-56623499484 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 2) <| besselDerivativeNearFromState (997691854266083 / 8000000000000) 2 (IntervalRat.scale (391 / 4) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-11934660838 / 1000000000000) (-11934660768 / 1000000000000), orderedInterval (70491749858 / 1000000000000) (70491749928 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 2) <| besselDerivativeNearFromState (289169986274217 / 1600000000000) 2 (IntervalRat.scale (391 / 4) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-38072014267 / 1000000000000) (-38071991310 / 1000000000000), orderedInterval (45635432589 / 1000000000000) (45635455546 / 1000000000000)))) (orderedInterval (3125492924 / 1000000000000) (3125494972 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate217_chunkChecks2_2 :
    compactCertificate217.chunkChecks (2 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 2) <| besselDerivativeNearFromState (799859400217099 / 8000000000000) 2 (IntervalRat.scale (391 / 4) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (18626886769 / 1000000000000) (18626886770 / 1000000000000), orderedInterval (77498260831 / 1000000000000) (77498260832 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 2) <| besselDerivativeNearFromState (678049671764339 / 8000000000000) 2 (IntervalRat.scale (391 / 4) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-56959281958 / 1000000000000) (-56959281957 / 1000000000000), orderedInterval (-64985088152 / 1000000000000) (-64985088151 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 2) <| besselDerivativeNearFromState (424292001734417 / 8000000000000) 2 (IntervalRat.scale (391 / 4) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-43918458384 / 1000000000000) (-43918458383 / 1000000000000), orderedInterval (-99960087366 / 1000000000000) (-99960087365 / 1000000000000)))) (orderedInterval (1228129791 / 1000000000000) (1228129813 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 2) <| besselDerivativeNearFromState (228185649664239 / 8000000000000) 2 (IntervalRat.scale (391 / 4) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-128059394861 / 1000000000000) (-128059394860 / 1000000000000), orderedInterval (-74687947805 / 1000000000000) (-74687947804 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 2) <| besselDerivativeNearFromState (619568427269717 / 8000000000000) 2 (IntervalRat.scale (391 / 4) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (27656057514 / 1000000000000) (27656058151 / 1000000000000), orderedInterval (-86523505394 / 1000000000000) (-86523504757 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 2) <| besselDerivativeNearFromState (845967718902709 / 8000000000000) 2 (IntervalRat.scale (391 / 4) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-21738242168 / 1000000000000) (-21738241782 / 1000000000000), orderedInterval (74586206410 / 1000000000000) (74586206796 / 1000000000000)))) (orderedInterval (-1713954283 / 1000000000000) (-1713954228 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 2) <| besselDerivativeNearFromState (357707998265583 / 8000000000000) 2 (IntervalRat.scale (391 / 4) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (119124614614 / 1000000000000) (119124614623 / 1000000000000), orderedInterval (5464819622 / 1000000000000) (5464819631 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 2) <| besselDerivativeNearFromState (1454063153595343 / 8000000000000) 2 (IntervalRat.scale (391 / 4) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (19190563519 / 1000000000000) (19190563520 / 1000000000000), orderedInterval (55932053884 / 1000000000000) (55932053885 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 2) <| besselDerivativeNearFromState (971246799406337 / 8000000000000) 2 (IntervalRat.scale (391 / 4) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (23594803321 / 1000000000000) (23594803960 / 1000000000000), orderedInterval (-68559223657 / 1000000000000) (-68559223019 / 1000000000000)))) (orderedInterval (12002743546 / 1000000000000) (12002743790 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate217_chunkChecks2 :
    compactCertificate217.chunkChecks (2 : Fin 5) 0 9 = true :=
  compactCertificate217.chunkChecks_nine_of_three (2 : Fin 5) compactCertificate217_chunkChecks2_0
    compactCertificate217_chunkChecks2_1 compactCertificate217_chunkChecks2_2

theorem compactCertificate217_chunkChecks3_0 :
    compactCertificate217.chunkChecks (3 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 3) <| besselDerivativeNearFromState (391 / 4) 3 (IntervalRat.scale (391 / 4) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-73486773723 / 1000000000000) (-73486773722 / 1000000000000), orderedInterval (-32976363398 / 1000000000000) (-32976363397 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 3) <| besselDerivativeNearFromState (576017660629291 / 8000000000000) 3 (IntervalRat.scale (391 / 4) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-47473038941 / 1000000000000) (-47473038940 / 1000000000000), orderedInterval (-80837372731 / 1000000000000) (-80837372730 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 3) <| besselDerivativeNearFromState (186272276417803 / 1600000000000) 3 (IntervalRat.scale (391 / 4) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-60812476948 / 1000000000000) (-60812476947 / 1000000000000), orderedInterval (-41811612807 / 1000000000000) (-41811612806 / 1000000000000)))) (orderedInterval (17161083888 / 1000000000000) (17161083900 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 3) <| besselDerivativeNearFromState (168080516763137 / 8000000000000) 3 (IntervalRat.scale (391 / 4) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (34855403874 / 1000000000000) (34855404091 / 1000000000000), orderedInterval (-171397695031 / 1000000000000) (-171397694814 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 3) <| besselDerivativeNearFromState (451487910506189 / 8000000000000) 3 (IntervalRat.scale (391 / 4) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (65995113741 / 1000000000000) (65995113742 / 1000000000000), orderedInterval (82632736048 / 1000000000000) (82632736049 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 3) <| besselDerivativeNearFromState (1225877503930713 / 8000000000000) 3 (IntervalRat.scale (391 / 4) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-5229994919 / 1000000000000) (-5229994917 / 1000000000000), orderedInterval (-64226299018 / 1000000000000) (-64226299016 / 1000000000000)))) (orderedInterval (-18168728476 / 1000000000000) (-18168728447 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 3) <| besselDerivativeNearFromState (902975821012769 / 8000000000000) 3 (IntervalRat.scale (391 / 4) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (39824611451 / 1000000000000) (39824611452 / 1000000000000), orderedInterval (63496328661 / 1000000000000) (63496328662 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 3) <| besselDerivativeNearFromState (1547264460035237 / 8000000000000) 3 (IntervalRat.scale (391 / 4) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-31725653150 / 1000000000000) (-31725645824 / 1000000000000), orderedInterval (47884482708 / 1000000000000) (47884490034 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 3) <| besselDerivativeNearFromState (1139707998265583 / 8000000000000) 3 (IntervalRat.scale (391 / 4) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-63751395065 / 1000000000000) (-63751392764 / 1000000000000), orderedInterval (20333168395 / 1000000000000) (20333170696 / 1000000000000)))) (orderedInterval (9924315764 / 1000000000000) (9924317728 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate217_chunkChecks3_1 :
    compactCertificate217.chunkChecks (3 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 3) <| besselDerivativeNearFromState (1748605158404609 / 8000000000000) 3 (IntervalRat.scale (391 / 4) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-28255204451 / 1000000000000) (-28255199988 / 1000000000000), orderedInterval (46045392116 / 1000000000000) (46045396579 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 3) <| besselDerivativeNearFromState (1009557658911161 / 8000000000000) 3 (IntervalRat.scale (391 / 4) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (68722374653 / 1000000000000) (68722374655 / 1000000000000), orderedInterval (17670485531 / 1000000000000) (17670485533 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 3) <| besselDerivativeNearFromState (1791477781782349 / 8000000000000) 3 (IntervalRat.scale (391 / 4) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-53074696531 / 1000000000000) (-53074696230 / 1000000000000), orderedInterval (5212683529 / 1000000000000) (5212683830 / 1000000000000)))) (orderedInterval (79683458811 / 1000000000000) (79683468613 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 3) <| besselDerivativeNearFromState (1673830928126881 / 8000000000000) 3 (IntervalRat.scale (391 / 4) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (25130899187 / 1000000000000) (25130901190 / 1000000000000), orderedInterval (-49163403173 / 1000000000000) (-49163401171 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 3) <| besselDerivativeNearFromState (1194524731151473 / 8000000000000) 3 (IntervalRat.scale (391 / 4) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-41879497773 / 1000000000000) (-41879471216 / 1000000000000), orderedInterval (50237112281 / 1000000000000) (50237138838 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 3) <| besselDerivativeNearFromState (1354463731518567 / 8000000000000) 3 (IntervalRat.scale (391 / 4) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (26485368244 / 1000000000000) (26485368245 / 1000000000000), orderedInterval (55226977531 / 1000000000000) (55226977532 / 1000000000000)))) (orderedInterval (-24301748012 / 1000000000000) (-24301738592 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 3) <| besselDerivativeNearFromState (1129210649397623 / 8000000000000) 3 (IntervalRat.scale (391 / 4) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-35910485291 / 1000000000000) (-35910485290 / 1000000000000), orderedInterval (-56623499485 / 1000000000000) (-56623499484 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 3) <| besselDerivativeNearFromState (997691854266083 / 8000000000000) 3 (IntervalRat.scale (391 / 4) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-11934660838 / 1000000000000) (-11934660768 / 1000000000000), orderedInterval (70491749858 / 1000000000000) (70491749928 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 3) <| besselDerivativeNearFromState (289169986274217 / 1600000000000) 3 (IntervalRat.scale (391 / 4) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-38072014267 / 1000000000000) (-38071991310 / 1000000000000), orderedInterval (45635432589 / 1000000000000) (45635455546 / 1000000000000)))) (orderedInterval (2928581291 / 1000000000000) (2928585067 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate217_chunkChecks3_2 :
    compactCertificate217.chunkChecks (3 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 3) <| besselDerivativeNearFromState (799859400217099 / 8000000000000) 3 (IntervalRat.scale (391 / 4) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (18626886769 / 1000000000000) (18626886770 / 1000000000000), orderedInterval (77498260831 / 1000000000000) (77498260832 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 3) <| besselDerivativeNearFromState (678049671764339 / 8000000000000) 3 (IntervalRat.scale (391 / 4) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-56959281958 / 1000000000000) (-56959281957 / 1000000000000), orderedInterval (-64985088152 / 1000000000000) (-64985088151 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 3) <| besselDerivativeNearFromState (424292001734417 / 8000000000000) 3 (IntervalRat.scale (391 / 4) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-43918458384 / 1000000000000) (-43918458383 / 1000000000000), orderedInterval (-99960087366 / 1000000000000) (-99960087365 / 1000000000000)))) (orderedInterval (11368256417 / 1000000000000) (11368256440 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 3) <| besselDerivativeNearFromState (228185649664239 / 8000000000000) 3 (IntervalRat.scale (391 / 4) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-128059394861 / 1000000000000) (-128059394860 / 1000000000000), orderedInterval (-74687947805 / 1000000000000) (-74687947804 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 3) <| besselDerivativeNearFromState (619568427269717 / 8000000000000) 3 (IntervalRat.scale (391 / 4) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (27656057514 / 1000000000000) (27656058151 / 1000000000000), orderedInterval (-86523505394 / 1000000000000) (-86523504757 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 3) <| besselDerivativeNearFromState (845967718902709 / 8000000000000) 3 (IntervalRat.scale (391 / 4) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-21738242168 / 1000000000000) (-21738241782 / 1000000000000), orderedInterval (74586206410 / 1000000000000) (74586206796 / 1000000000000)))) (orderedInterval (6243424040 / 1000000000000) (6243424097 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 3) <| besselDerivativeNearFromState (357707998265583 / 8000000000000) 3 (IntervalRat.scale (391 / 4) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (119124614614 / 1000000000000) (119124614623 / 1000000000000), orderedInterval (5464819622 / 1000000000000) (5464819631 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 3) <| besselDerivativeNearFromState (1454063153595343 / 8000000000000) 3 (IntervalRat.scale (391 / 4) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (19190563519 / 1000000000000) (19190563520 / 1000000000000), orderedInterval (55932053884 / 1000000000000) (55932053885 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 3) <| besselDerivativeNearFromState (971246799406337 / 8000000000000) 3 (IntervalRat.scale (391 / 4) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (23594803321 / 1000000000000) (23594803960 / 1000000000000), orderedInterval (-68559223657 / 1000000000000) (-68559223019 / 1000000000000)))) (orderedInterval (4499952422 / 1000000000000) (4499952742 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate217_chunkChecks3 :
    compactCertificate217.chunkChecks (3 : Fin 5) 0 9 = true :=
  compactCertificate217.chunkChecks_nine_of_three (3 : Fin 5) compactCertificate217_chunkChecks3_0
    compactCertificate217_chunkChecks3_1 compactCertificate217_chunkChecks3_2

theorem compactCertificate217_chunkChecks4_0 :
    compactCertificate217.chunkChecks (4 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 4) <| besselDerivativeNearFromState (391 / 4) 4 (IntervalRat.scale (391 / 4) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-73486773723 / 1000000000000) (-73486773722 / 1000000000000), orderedInterval (-32976363398 / 1000000000000) (-32976363397 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 4) <| besselDerivativeNearFromState (576017660629291 / 8000000000000) 4 (IntervalRat.scale (391 / 4) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-47473038941 / 1000000000000) (-47473038940 / 1000000000000), orderedInterval (-80837372731 / 1000000000000) (-80837372730 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 4) <| besselDerivativeNearFromState (186272276417803 / 1600000000000) 4 (IntervalRat.scale (391 / 4) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-60812476948 / 1000000000000) (-60812476947 / 1000000000000), orderedInterval (-41811612807 / 1000000000000) (-41811612806 / 1000000000000)))) (orderedInterval (-36785500789 / 1000000000000) (-36785500776 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 4) <| besselDerivativeNearFromState (168080516763137 / 8000000000000) 4 (IntervalRat.scale (391 / 4) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (34855403874 / 1000000000000) (34855404091 / 1000000000000), orderedInterval (-171397695031 / 1000000000000) (-171397694814 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 4) <| besselDerivativeNearFromState (451487910506189 / 8000000000000) 4 (IntervalRat.scale (391 / 4) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (65995113741 / 1000000000000) (65995113742 / 1000000000000), orderedInterval (82632736048 / 1000000000000) (82632736049 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 4) <| besselDerivativeNearFromState (1225877503930713 / 8000000000000) 4 (IntervalRat.scale (391 / 4) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-5229994919 / 1000000000000) (-5229994917 / 1000000000000), orderedInterval (-64226299018 / 1000000000000) (-64226299016 / 1000000000000)))) (orderedInterval (2883738378 / 1000000000000) (2883738422 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 4) <| besselDerivativeNearFromState (902975821012769 / 8000000000000) 4 (IntervalRat.scale (391 / 4) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (39824611451 / 1000000000000) (39824611452 / 1000000000000), orderedInterval (63496328661 / 1000000000000) (63496328662 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 4) <| besselDerivativeNearFromState (1547264460035237 / 8000000000000) 4 (IntervalRat.scale (391 / 4) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-31725653150 / 1000000000000) (-31725645824 / 1000000000000), orderedInterval (47884482708 / 1000000000000) (47884490034 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 4) <| besselDerivativeNearFromState (1139707998265583 / 8000000000000) 4 (IntervalRat.scale (391 / 4) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-63751395065 / 1000000000000) (-63751392764 / 1000000000000), orderedInterval (20333168395 / 1000000000000) (20333170696 / 1000000000000)))) (orderedInterval (7842670879 / 1000000000000) (7842674690 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate217_chunkChecks4_1 :
    compactCertificate217.chunkChecks (4 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 4) <| besselDerivativeNearFromState (1748605158404609 / 8000000000000) 4 (IntervalRat.scale (391 / 4) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-28255204451 / 1000000000000) (-28255199988 / 1000000000000), orderedInterval (46045392116 / 1000000000000) (46045396579 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 4) <| besselDerivativeNearFromState (1009557658911161 / 8000000000000) 4 (IntervalRat.scale (391 / 4) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (68722374653 / 1000000000000) (68722374655 / 1000000000000), orderedInterval (17670485531 / 1000000000000) (17670485533 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 4) <| besselDerivativeNearFromState (1791477781782349 / 8000000000000) 4 (IntervalRat.scale (391 / 4) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-53074696531 / 1000000000000) (-53074696230 / 1000000000000), orderedInterval (5212683529 / 1000000000000) (5212683830 / 1000000000000)))) (orderedInterval (-69782928332 / 1000000000000) (-69782906298 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 4) <| besselDerivativeNearFromState (1673830928126881 / 8000000000000) 4 (IntervalRat.scale (391 / 4) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (25130899187 / 1000000000000) (25130901190 / 1000000000000), orderedInterval (-49163403173 / 1000000000000) (-49163401171 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 4) <| besselDerivativeNearFromState (1194524731151473 / 8000000000000) 4 (IntervalRat.scale (391 / 4) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-41879497773 / 1000000000000) (-41879471216 / 1000000000000), orderedInterval (50237112281 / 1000000000000) (50237138838 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 4) <| besselDerivativeNearFromState (1354463731518567 / 8000000000000) 4 (IntervalRat.scale (391 / 4) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (26485368244 / 1000000000000) (26485368245 / 1000000000000), orderedInterval (55226977531 / 1000000000000) (55226977532 / 1000000000000)))) (orderedInterval (-31792297498 / 1000000000000) (-31792282785 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 4) <| besselDerivativeNearFromState (1129210649397623 / 8000000000000) 4 (IntervalRat.scale (391 / 4) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-35910485291 / 1000000000000) (-35910485290 / 1000000000000), orderedInterval (-56623499485 / 1000000000000) (-56623499484 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 4) <| besselDerivativeNearFromState (997691854266083 / 8000000000000) 4 (IntervalRat.scale (391 / 4) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-11934660838 / 1000000000000) (-11934660768 / 1000000000000), orderedInterval (70491749858 / 1000000000000) (70491749928 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 4) <| besselDerivativeNearFromState (289169986274217 / 1600000000000) 4 (IntervalRat.scale (391 / 4) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-38072014267 / 1000000000000) (-38071991310 / 1000000000000), orderedInterval (45635432589 / 1000000000000) (45635455546 / 1000000000000)))) (orderedInterval (-11444463841 / 1000000000000) (-11444456836 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate217_chunkChecks4_2 :
    compactCertificate217.chunkChecks (4 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 4) <| besselDerivativeNearFromState (799859400217099 / 8000000000000) 4 (IntervalRat.scale (391 / 4) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (18626886769 / 1000000000000) (18626886770 / 1000000000000), orderedInterval (77498260831 / 1000000000000) (77498260832 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 4) <| besselDerivativeNearFromState (678049671764339 / 8000000000000) 4 (IntervalRat.scale (391 / 4) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-56959281958 / 1000000000000) (-56959281957 / 1000000000000), orderedInterval (-64985088152 / 1000000000000) (-64985088151 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 4) <| besselDerivativeNearFromState (424292001734417 / 8000000000000) 4 (IntervalRat.scale (391 / 4) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-43918458384 / 1000000000000) (-43918458383 / 1000000000000), orderedInterval (-99960087366 / 1000000000000) (-99960087365 / 1000000000000)))) (orderedInterval (-1793987835 / 1000000000000) (-1793987813 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 4) <| besselDerivativeNearFromState (228185649664239 / 8000000000000) 4 (IntervalRat.scale (391 / 4) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-128059394861 / 1000000000000) (-128059394860 / 1000000000000), orderedInterval (-74687947805 / 1000000000000) (-74687947804 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 4) <| besselDerivativeNearFromState (619568427269717 / 8000000000000) 4 (IntervalRat.scale (391 / 4) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (27656057514 / 1000000000000) (27656058151 / 1000000000000), orderedInterval (-86523505394 / 1000000000000) (-86523504757 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 4) <| besselDerivativeNearFromState (845967718902709 / 8000000000000) 4 (IntervalRat.scale (391 / 4) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-21738242168 / 1000000000000) (-21738241782 / 1000000000000), orderedInterval (74586206410 / 1000000000000) (74586206796 / 1000000000000)))) (orderedInterval (1923715567 / 1000000000000) (1923715627 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 4) <| besselDerivativeNearFromState (357707998265583 / 8000000000000) 4 (IntervalRat.scale (391 / 4) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (119124614614 / 1000000000000) (119124614623 / 1000000000000), orderedInterval (5464819622 / 1000000000000) (5464819631 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 4) <| besselDerivativeNearFromState (1454063153595343 / 8000000000000) 4 (IntervalRat.scale (391 / 4) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (19190563519 / 1000000000000) (19190563520 / 1000000000000), orderedInterval (55932053884 / 1000000000000) (55932053885 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 4) <| besselDerivativeNearFromState (971246799406337 / 8000000000000) 4 (IntervalRat.scale (391 / 4) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (23594803321 / 1000000000000) (23594803960 / 1000000000000), orderedInterval (-68559223657 / 1000000000000) (-68559223019 / 1000000000000)))) (orderedInterval (-29267177092 / 1000000000000) (-29267176661 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate217_chunkChecks4 :
    compactCertificate217.chunkChecks (4 : Fin 5) 0 9 = true :=
  compactCertificate217.chunkChecks_nine_of_three (4 : Fin 5) compactCertificate217_chunkChecks4_0
    compactCertificate217_chunkChecks4_1 compactCertificate217_chunkChecks4_2

theorem compactCertificate217_chunks :
    ∀ r : Fin 5, ∀ b, compactCertificate217.chunkCheck r b = true :=
  compactCertificate217.chunkChecks_all (by
    intro r
    fin_cases r
    · exact compactCertificate217_chunkChecks0
    · exact compactCertificate217_chunkChecks1
    · exact compactCertificate217_chunkChecks2
    · exact compactCertificate217_chunkChecks3
    · exact compactCertificate217_chunkChecks4)

theorem compactCertificate217_coefficient0 :
    compactCertificate217.coefficientCheck (0 : Fin 5) = true := by
  norm_num [CompactCertificate.coefficientCheck, intervalFinSumHull,
    compactCertificate217, rationalIntervalSubset, orderedInterval, Fin.sum_univ_succ]

theorem compactCertificate217_coefficient1 :
    compactCertificate217.coefficientCheck (1 : Fin 5) = true := by
  norm_num [CompactCertificate.coefficientCheck, intervalFinSumHull,
    compactCertificate217, rationalIntervalSubset, orderedInterval, Fin.sum_univ_succ]

theorem compactCertificate217_coefficient2 :
    compactCertificate217.coefficientCheck (2 : Fin 5) = true := by
  norm_num [CompactCertificate.coefficientCheck, intervalFinSumHull,
    compactCertificate217, rationalIntervalSubset, orderedInterval, Fin.sum_univ_succ]

theorem compactCertificate217_coefficient3 :
    compactCertificate217.coefficientCheck (3 : Fin 5) = true := by
  norm_num [CompactCertificate.coefficientCheck, intervalFinSumHull,
    compactCertificate217, rationalIntervalSubset, orderedInterval, Fin.sum_univ_succ]

theorem compactCertificate217_coefficient4 :
    compactCertificate217.coefficientCheck (4 : Fin 5) = true := by
  norm_num [CompactCertificate.coefficientCheck, intervalFinSumHull,
    compactCertificate217, rationalIntervalSubset, orderedInterval, Fin.sum_univ_succ]

theorem compactCertificate217_coefficients : ∀ r : Fin 5,
    compactCertificate217.coefficientCheck r = true := by
  intro r
  fin_cases r
  · exact compactCertificate217_coefficient0
  · exact compactCertificate217_coefficient1
  · exact compactCertificate217_coefficient2
  · exact compactCertificate217_coefficient3
  · exact compactCertificate217_coefficient4

theorem compactCertificate217_lower : (1 : ℚ) ≤ compactCertificate217.output.lo := by
  norm_num [CompactCertificate.output, CompactCertificate.interval,
    CompactCertificate.coefficientTargetNat, compactCertificate217, dualConstant,
    intervalTaylorSum, intervalPow, intervalSub, intervalMaxAbs, widenInterval,
    rationalErrorInterval, orderedInterval, IntervalRat.add, IntervalRat.mul, IntervalRat.scale,
    IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4]

theorem compactCertificate217_proves {t : ℝ} (ht : t ∈ compactCertificate217.interval) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t :=
  compactCertificate217.proves compactCertificate217_states compactCertificate217_chunks
    compactCertificate217_coefficients compactCertificate217_lower ht

end Erdos232
