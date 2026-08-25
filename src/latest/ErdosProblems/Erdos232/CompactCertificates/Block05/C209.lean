/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, OpenAI Codex
-/
import ErdosProblems.Erdos232.CompactBase

open LeanCert.Core
namespace Erdos232

def compactCertificate209 : CompactCertificate where
  left := 1481 / 16
  right := 741 / 8
  center := 2963 / 32
  grid := fun i =>
    match i.val with
    | 0 => 29
    | 1 => 22
    | 2 => 35
    | 3 => 6
    | 4 => 17
    | 5 => 46
    | 6 => 34
    | 7 => 58
    | 8 => 43
    | 9 => 66
    | 10 => 38
    | 11 => 68
    | 12 => 63
    | 13 => 45
    | 14 => 51
    | 15 => 43
    | 16 => 38
    | 17 => 55
    | 18 => 30
    | 19 => 26
    | 20 => 16
    | 21 => 9
    | 22 => 23
    | 23 => 32
    | 24 => 13
    | 25 => 55
    | _ => 37
  point := fun i =>
    match i.val with
    | 0 => 2963 / 32
    | 1 => 4365064778630663 / 64000000000000
    | 2 => 1411572263493479 / 12800000000000
    | 3 => 1273715015777941 / 64000000000000
    | 4 => 3421377695216977 / 64000000000000
    | 5 => 9289705995260109 / 64000000000000
    | 6 => 6842755390436917 / 64000000000000
    | 7 => 11725177992543241 / 64000000000000
    | 8 => 8636713040565019 / 64000000000000
    | 9 => 13250938834662037 / 64000000000000
    | 10 => 7650433103206573 / 64000000000000
    | 11 => 13575827793915857 / 64000000000000
    | 12 => 12684299335140533 / 64000000000000
    | 13 => 9052114522766789 / 64000000000000
    | 14 => 10264133085650931 / 64000000000000
    | 15 => 8557164077148739 / 64000000000000
    | 16 => 7560513974911519 / 64000000000000
    | 17 => 2191331635116381 / 12800000000000
    | 18 => 6061338626197607 / 64000000000000
    | 19 => 5138263880914927 / 64000000000000
    | 20 => 3215286959434981 / 64000000000000
    | 21 => 1729192020345627 / 64000000000000
    | 22 => 4695092710997881 / 64000000000000
    | 23 => 6410747701045337 / 64000000000000
    | 24 => 2710713040565019 / 64000000000000
    | 25 => 11018898015608699 / 64000000000000
    | _ => 7360113213915541 / 64000000000000
  state := fun i =>
    match i.val with
    | 0 => (orderedInterval (-63375266443 / 1000000000000) (-63375182967 / 1000000000000), orderedInterval (53811517147 / 1000000000000) (53811600624 / 1000000000000))
    | 1 => (orderedInterval (-12268864344 / 1000000000000) (-12268864285 / 1000000000000), orderedInterval (95921832680 / 1000000000000) (95921832738 / 1000000000000))
    | 2 => (orderedInterval (-67972815577 / 1000000000000) (-67972815576 / 1000000000000), orderedInterval (-33639823537 / 1000000000000) (-33639823536 / 1000000000000))
    | 3 => (orderedInterval (172787413872 / 1000000000000) (172787414573 / 1000000000000), orderedInterval (-50423486746 / 1000000000000) (-50423486045 / 1000000000000))
    | 4 => (orderedInterval (-80894056429 / 1000000000000) (-80894056428 / 1000000000000), orderedInterval (-72487275100 / 1000000000000) (-72487275099 / 1000000000000))
    | 5 => (orderedInterval (65503218626 / 1000000000000) (65503218631 / 1000000000000), orderedInterval (9531282111 / 1000000000000) (9531282116 / 1000000000000))
    | 6 => (orderedInterval (59870773850 / 1000000000000) (59870773851 / 1000000000000), orderedInterval (48400149074 / 1000000000000) (48400149075 / 1000000000000))
    | 7 => (orderedInterval (57684150757 / 1000000000000) (57684151696 / 1000000000000), orderedInterval (-12298828708 / 1000000000000) (-12298827769 / 1000000000000))
    | 8 => (orderedInterval (-41272231504 / 1000000000000) (-41272231503 / 1000000000000), orderedInterval (-54747981991 / 1000000000000) (-54747981990 / 1000000000000))
    | 9 => (orderedInterval (25880883652 / 1000000000000) (25880883653 / 1000000000000), orderedInterval (48977898400 / 1000000000000) (48977898401 / 1000000000000))
    | 10 => (orderedInterval (59012527660 / 1000000000000) (59012527661 / 1000000000000), orderedInterval (42685383285 / 1000000000000) (42685383286 / 1000000000000))
    | 11 => (orderedInterval (-36171790063 / 1000000000000) (-36171765111 / 1000000000000), orderedInterval (41228844478 / 1000000000000) (41228869430 / 1000000000000))
    | 12 => (orderedInterval (-49346985872 / 1000000000000) (-49346985871 / 1000000000000), orderedInterval (-27750289009 / 1000000000000) (-27750289008 / 1000000000000))
    | 13 => (orderedInterval (-50497316941 / 1000000000000) (-50497316940 / 1000000000000), orderedInterval (-43991933197 / 1000000000000) (-43991933196 / 1000000000000))
    | 14 => (orderedInterval (-50896925950 / 1000000000000) (-50896925949 / 1000000000000), orderedInterval (-36976420159 / 1000000000000) (-36976420158 / 1000000000000))
    | 15 => (orderedInterval (38866585152 / 1000000000000) (38866596368 / 1000000000000), orderedInterval (-57160710853 / 1000000000000) (-57160699636 / 1000000000000))
    | 16 => (orderedInterval (-32797058184 / 1000000000000) (-32797055201 / 1000000000000), orderedInterval (65815209304 / 1000000000000) (65815212287 / 1000000000000))
    | 17 => (orderedInterval (43962569801 / 1000000000000) (43962633521 / 1000000000000), orderedInterval (-42388460616 / 1000000000000) (-42388396896 / 1000000000000))
    | 18 => (orderedInterval (77666280212 / 1000000000000) (77666280213 / 1000000000000), orderedInterval (25853394465 / 1000000000000) (25853394466 / 1000000000000))
    | 19 => (orderedInterval (-51171989577 / 1000000000000) (-51171972964 / 1000000000000), orderedInterval (73194876613 / 1000000000000) (73194893225 / 1000000000000))
    | 20 => (orderedInterval (77246025116 / 1000000000000) (77246025117 / 1000000000000), orderedInterval (81115034516 / 1000000000000) (81115034517 / 1000000000000))
    | 21 => (orderedInterval (70186391335 / 1000000000000) (70186396675 / 1000000000000), orderedInterval (-137821188910 / 1000000000000) (-137821183569 / 1000000000000))
    | 22 => (orderedInterval (-88510242876 / 1000000000000) (-88510241094 / 1000000000000), orderedInterval (29649744840 / 1000000000000) (29649746622 / 1000000000000))
    | 23 => (orderedInterval (32588469662 / 1000000000000) (32588469663 / 1000000000000), orderedInterval (72594252519 / 1000000000000) (72594252520 / 1000000000000))
    | 24 => (orderedInterval (-91694235258 / 1000000000000) (-91694150970 / 1000000000000), orderedInterval (82461970526 / 1000000000000) (82462054814 / 1000000000000))
    | 25 => (orderedInterval (-10129231955 / 1000000000000) (-10129231954 / 1000000000000), orderedInterval (-59929156792 / 1000000000000) (-59929156791 / 1000000000000))
    | _ => (orderedInterval (32553056643 / 1000000000000) (32553059353 / 1000000000000), orderedInterval (-67044966741 / 1000000000000) (-67044964032 / 1000000000000))
  chunkTarget := fun r b =>
    match r.val with
    | 0 =>
      match b.val with
      | 0 => orderedInterval (-29222781365 / 1000000000000) (-29222748270 / 1000000000000)
      | 1 => orderedInterval (-9484804486 / 1000000000000) (-9484804466 / 1000000000000)
      | 2 => orderedInterval (-2776678441 / 1000000000000) (-2776678406 / 1000000000000)
      | 3 => orderedInterval (-5368410954 / 1000000000000) (-5368407369 / 1000000000000)
      | 4 => orderedInterval (-3626737879 / 1000000000000) (-3626737867 / 1000000000000)
      | 5 => orderedInterval (3451300418 / 1000000000000) (3451302360 / 1000000000000)
      | 6 => orderedInterval (-7007154517 / 1000000000000) (-7007153552 / 1000000000000)
      | 7 => orderedInterval (-1785523897 / 1000000000000) (-1785523746 / 1000000000000)
      | _ => orderedInterval (-5836042928 / 1000000000000) (-5836041885 / 1000000000000)
    | 1 =>
      match b.val with
      | 0 => orderedInterval (19636314555 / 1000000000000) (19636347651 / 1000000000000)
      | 1 => orderedInterval (-2472633122 / 1000000000000) (-2472633106 / 1000000000000)
      | 2 => orderedInterval (-1177823944 / 1000000000000) (-1177823877 / 1000000000000)
      | 3 => orderedInterval (-1950321538 / 1000000000000) (-1950313334 / 1000000000000)
      | 4 => orderedInterval (-4958086710 / 1000000000000) (-4958086691 / 1000000000000)
      | 5 => orderedInterval (-7765028570 / 1000000000000) (-7765025135 / 1000000000000)
      | 6 => orderedInterval (-6387512142 / 1000000000000) (-6387511304 / 1000000000000)
      | 7 => orderedInterval (-5808988678 / 1000000000000) (-5808988606 / 1000000000000)
      | _ => orderedInterval (24921929677 / 1000000000000) (24921930578 / 1000000000000)
    | 2 =>
      match b.val with
      | 0 => orderedInterval (30627581370 / 1000000000000) (30627614823 / 1000000000000)
      | 1 => orderedInterval (12541090993 / 1000000000000) (12541091013 / 1000000000000)
      | 2 => orderedInterval (9096784543 / 1000000000000) (9096784674 / 1000000000000)
      | 3 => orderedInterval (42713763305 / 1000000000000) (42713782173 / 1000000000000)
      | 4 => orderedInterval (6341390727 / 1000000000000) (6341390758 / 1000000000000)
      | 5 => orderedInterval (-7754900418 / 1000000000000) (-7754894235 / 1000000000000)
      | 6 => orderedInterval (10143122500 / 1000000000000) (10143123238 / 1000000000000)
      | 7 => orderedInterval (1835467860 / 1000000000000) (1835467905 / 1000000000000)
      | _ => orderedInterval (6417480890 / 1000000000000) (6417481844 / 1000000000000)
    | 3 =>
      match b.val with
      | 0 => orderedInterval (-18679804225 / 1000000000000) (-18679770777 / 1000000000000)
      | 1 => orderedInterval (2978411951 / 1000000000000) (2978411979 / 1000000000000)
      | 2 => orderedInterval (1059332601 / 1000000000000) (1059332857 / 1000000000000)
      | 3 => orderedInterval (19567500348 / 1000000000000) (19567543554 / 1000000000000)
      | 4 => orderedInterval (8872961536 / 1000000000000) (8872961588 / 1000000000000)
      | 5 => orderedInterval (16751537559 / 1000000000000) (16751548711 / 1000000000000)
      | 6 => orderedInterval (6592026634 / 1000000000000) (6592027276 / 1000000000000)
      | 7 => orderedInterval (7294370914 / 1000000000000) (7294370948 / 1000000000000)
      | _ => orderedInterval (-55576486616 / 1000000000000) (-55576485501 / 1000000000000)
    | _ =>
      match b.val with
      | 0 => orderedInterval (-32772006554 / 1000000000000) (-32771972752 / 1000000000000)
      | 1 => orderedInterval (-28516010846 / 1000000000000) (-28516010803 / 1000000000000)
      | 2 => orderedInterval (-31790492778 / 1000000000000) (-31790492274 / 1000000000000)
      | 3 => orderedInterval (-244869733738 / 1000000000000) (-244869634326 / 1000000000000)
      | 4 => orderedInterval (-5171389671 / 1000000000000) (-5171389581 / 1000000000000)
      | 5 => orderedInterval (19715303474 / 1000000000000) (19715323839 / 1000000000000)
      | 6 => orderedInterval (-11878334679 / 1000000000000) (-11878334114 / 1000000000000)
      | 7 => orderedInterval (-2796100840 / 1000000000000) (-2796100811 / 1000000000000)
      | _ => orderedInterval (-3500430318 / 1000000000000) (-3500428931 / 1000000000000)
  coefficientTarget := fun i =>
    match i.val with
    | 0 => orderedInterval (-61656834049 / 1000000000000) (-61656793201 / 1000000000000)
    | 1 => orderedInterval (14037849528 / 1000000000000) (14037896176 / 1000000000000)
    | 2 => orderedInterval (111961781770 / 1000000000000) (111961842193 / 1000000000000)
    | 3 => orderedInterval (-11140149298 / 1000000000000) (-11140059365 / 1000000000000)
    | _ => orderedInterval (-341579195950 / 1000000000000) (-341579039753 / 1000000000000)

theorem compactCertificate209_stateChecks0 :
    compactCertificate209.stateChecks 0 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 29 12 (2963 / 32)) (orderedInterval (-63375266443 / 1000000000000) (-63375182967 / 1000000000000), orderedInterval (53811517147 / 1000000000000) (53811600624 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 22 12 (4365064778630663 / 64000000000000)) (orderedInterval (-12268864344 / 1000000000000) (-12268864285 / 1000000000000), orderedInterval (95921832680 / 1000000000000) (95921832738 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 35 12 (1411572263493479 / 12800000000000)) (orderedInterval (-67972815577 / 1000000000000) (-67972815576 / 1000000000000), orderedInterval (-33639823537 / 1000000000000) (-33639823536 / 1000000000000))) = true
  norm_num [besselStateAtRationalPoint, besselIntervalStepZero,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, besselZeroTransition,
    besselInitial, besselGridStateAt, besselGridStateBlock00, besselGridStateBlock01,
    besselGridStateBlock02, besselGridStateBlock03, besselGridStateBlock04,
    besselGridStateBlock05, besselGridStateBlock06, besselGridStateBlock07,
    besselGridStateBlock08, besselGridStateBlock09, besselGridStateBlock10,
    besselGridStateBlock11, besselGridStateBlock12, besselGridStateBlock13,
    besselGridStateBlock14, besselGridState006, besselGridState009, besselGridState013, besselGridState016, besselGridState017, besselGridState022, besselGridState023, besselGridState026, besselGridState029, besselGridState030, besselGridState032, besselGridState034, besselGridState035, besselGridState037, besselGridState038, besselGridState043, besselGridState045, besselGridState046, besselGridState051, besselGridState055, besselGridState058, besselGridState063, besselGridState066, besselGridState068, besselStateSubset, linearInterval, widenInterval,
    rationalErrorInterval, rationalIntervalSubset, orderedInterval, Finset.sum_range_succ,
    IntervalRat.add, IntervalRat.mul, IntervalRat.scale, IntervalRat.singleton]

theorem compactCertificate209_stateChecks1 :
    compactCertificate209.stateChecks 3 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 6 12 (1273715015777941 / 64000000000000)) (orderedInterval (172787413872 / 1000000000000) (172787414573 / 1000000000000), orderedInterval (-50423486746 / 1000000000000) (-50423486045 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 17 12 (3421377695216977 / 64000000000000)) (orderedInterval (-80894056429 / 1000000000000) (-80894056428 / 1000000000000), orderedInterval (-72487275100 / 1000000000000) (-72487275099 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 46 12 (9289705995260109 / 64000000000000)) (orderedInterval (65503218626 / 1000000000000) (65503218631 / 1000000000000), orderedInterval (9531282111 / 1000000000000) (9531282116 / 1000000000000))) = true
  norm_num [besselStateAtRationalPoint, besselIntervalStepZero,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, besselZeroTransition,
    besselInitial, besselGridStateAt, besselGridStateBlock00, besselGridStateBlock01,
    besselGridStateBlock02, besselGridStateBlock03, besselGridStateBlock04,
    besselGridStateBlock05, besselGridStateBlock06, besselGridStateBlock07,
    besselGridStateBlock08, besselGridStateBlock09, besselGridStateBlock10,
    besselGridStateBlock11, besselGridStateBlock12, besselGridStateBlock13,
    besselGridStateBlock14, besselGridState006, besselGridState009, besselGridState013, besselGridState016, besselGridState017, besselGridState022, besselGridState023, besselGridState026, besselGridState029, besselGridState030, besselGridState032, besselGridState034, besselGridState035, besselGridState037, besselGridState038, besselGridState043, besselGridState045, besselGridState046, besselGridState051, besselGridState055, besselGridState058, besselGridState063, besselGridState066, besselGridState068, besselStateSubset, linearInterval, widenInterval,
    rationalErrorInterval, rationalIntervalSubset, orderedInterval, Finset.sum_range_succ,
    IntervalRat.add, IntervalRat.mul, IntervalRat.scale, IntervalRat.singleton]

theorem compactCertificate209_stateChecks2 :
    compactCertificate209.stateChecks 6 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 34 12 (6842755390436917 / 64000000000000)) (orderedInterval (59870773850 / 1000000000000) (59870773851 / 1000000000000), orderedInterval (48400149074 / 1000000000000) (48400149075 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 58 12 (11725177992543241 / 64000000000000)) (orderedInterval (57684150757 / 1000000000000) (57684151696 / 1000000000000), orderedInterval (-12298828708 / 1000000000000) (-12298827769 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 43 12 (8636713040565019 / 64000000000000)) (orderedInterval (-41272231504 / 1000000000000) (-41272231503 / 1000000000000), orderedInterval (-54747981991 / 1000000000000) (-54747981990 / 1000000000000))) = true
  norm_num [besselStateAtRationalPoint, besselIntervalStepZero,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, besselZeroTransition,
    besselInitial, besselGridStateAt, besselGridStateBlock00, besselGridStateBlock01,
    besselGridStateBlock02, besselGridStateBlock03, besselGridStateBlock04,
    besselGridStateBlock05, besselGridStateBlock06, besselGridStateBlock07,
    besselGridStateBlock08, besselGridStateBlock09, besselGridStateBlock10,
    besselGridStateBlock11, besselGridStateBlock12, besselGridStateBlock13,
    besselGridStateBlock14, besselGridState006, besselGridState009, besselGridState013, besselGridState016, besselGridState017, besselGridState022, besselGridState023, besselGridState026, besselGridState029, besselGridState030, besselGridState032, besselGridState034, besselGridState035, besselGridState037, besselGridState038, besselGridState043, besselGridState045, besselGridState046, besselGridState051, besselGridState055, besselGridState058, besselGridState063, besselGridState066, besselGridState068, besselStateSubset, linearInterval, widenInterval,
    rationalErrorInterval, rationalIntervalSubset, orderedInterval, Finset.sum_range_succ,
    IntervalRat.add, IntervalRat.mul, IntervalRat.scale, IntervalRat.singleton]

theorem compactCertificate209_stateChecks3 :
    compactCertificate209.stateChecks 9 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 66 12 (13250938834662037 / 64000000000000)) (orderedInterval (25880883652 / 1000000000000) (25880883653 / 1000000000000), orderedInterval (48977898400 / 1000000000000) (48977898401 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 38 12 (7650433103206573 / 64000000000000)) (orderedInterval (59012527660 / 1000000000000) (59012527661 / 1000000000000), orderedInterval (42685383285 / 1000000000000) (42685383286 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 68 12 (13575827793915857 / 64000000000000)) (orderedInterval (-36171790063 / 1000000000000) (-36171765111 / 1000000000000), orderedInterval (41228844478 / 1000000000000) (41228869430 / 1000000000000))) = true
  norm_num [besselStateAtRationalPoint, besselIntervalStepZero,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, besselZeroTransition,
    besselInitial, besselGridStateAt, besselGridStateBlock00, besselGridStateBlock01,
    besselGridStateBlock02, besselGridStateBlock03, besselGridStateBlock04,
    besselGridStateBlock05, besselGridStateBlock06, besselGridStateBlock07,
    besselGridStateBlock08, besselGridStateBlock09, besselGridStateBlock10,
    besselGridStateBlock11, besselGridStateBlock12, besselGridStateBlock13,
    besselGridStateBlock14, besselGridState006, besselGridState009, besselGridState013, besselGridState016, besselGridState017, besselGridState022, besselGridState023, besselGridState026, besselGridState029, besselGridState030, besselGridState032, besselGridState034, besselGridState035, besselGridState037, besselGridState038, besselGridState043, besselGridState045, besselGridState046, besselGridState051, besselGridState055, besselGridState058, besselGridState063, besselGridState066, besselGridState068, besselStateSubset, linearInterval, widenInterval,
    rationalErrorInterval, rationalIntervalSubset, orderedInterval, Finset.sum_range_succ,
    IntervalRat.add, IntervalRat.mul, IntervalRat.scale, IntervalRat.singleton]

theorem compactCertificate209_stateChecks4 :
    compactCertificate209.stateChecks 12 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 63 12 (12684299335140533 / 64000000000000)) (orderedInterval (-49346985872 / 1000000000000) (-49346985871 / 1000000000000), orderedInterval (-27750289009 / 1000000000000) (-27750289008 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 45 12 (9052114522766789 / 64000000000000)) (orderedInterval (-50497316941 / 1000000000000) (-50497316940 / 1000000000000), orderedInterval (-43991933197 / 1000000000000) (-43991933196 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 51 12 (10264133085650931 / 64000000000000)) (orderedInterval (-50896925950 / 1000000000000) (-50896925949 / 1000000000000), orderedInterval (-36976420159 / 1000000000000) (-36976420158 / 1000000000000))) = true
  norm_num [besselStateAtRationalPoint, besselIntervalStepZero,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, besselZeroTransition,
    besselInitial, besselGridStateAt, besselGridStateBlock00, besselGridStateBlock01,
    besselGridStateBlock02, besselGridStateBlock03, besselGridStateBlock04,
    besselGridStateBlock05, besselGridStateBlock06, besselGridStateBlock07,
    besselGridStateBlock08, besselGridStateBlock09, besselGridStateBlock10,
    besselGridStateBlock11, besselGridStateBlock12, besselGridStateBlock13,
    besselGridStateBlock14, besselGridState006, besselGridState009, besselGridState013, besselGridState016, besselGridState017, besselGridState022, besselGridState023, besselGridState026, besselGridState029, besselGridState030, besselGridState032, besselGridState034, besselGridState035, besselGridState037, besselGridState038, besselGridState043, besselGridState045, besselGridState046, besselGridState051, besselGridState055, besselGridState058, besselGridState063, besselGridState066, besselGridState068, besselStateSubset, linearInterval, widenInterval,
    rationalErrorInterval, rationalIntervalSubset, orderedInterval, Finset.sum_range_succ,
    IntervalRat.add, IntervalRat.mul, IntervalRat.scale, IntervalRat.singleton]

theorem compactCertificate209_stateChecks5 :
    compactCertificate209.stateChecks 15 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 43 12 (8557164077148739 / 64000000000000)) (orderedInterval (38866585152 / 1000000000000) (38866596368 / 1000000000000), orderedInterval (-57160710853 / 1000000000000) (-57160699636 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 38 12 (7560513974911519 / 64000000000000)) (orderedInterval (-32797058184 / 1000000000000) (-32797055201 / 1000000000000), orderedInterval (65815209304 / 1000000000000) (65815212287 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 55 12 (2191331635116381 / 12800000000000)) (orderedInterval (43962569801 / 1000000000000) (43962633521 / 1000000000000), orderedInterval (-42388460616 / 1000000000000) (-42388396896 / 1000000000000))) = true
  norm_num [besselStateAtRationalPoint, besselIntervalStepZero,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, besselZeroTransition,
    besselInitial, besselGridStateAt, besselGridStateBlock00, besselGridStateBlock01,
    besselGridStateBlock02, besselGridStateBlock03, besselGridStateBlock04,
    besselGridStateBlock05, besselGridStateBlock06, besselGridStateBlock07,
    besselGridStateBlock08, besselGridStateBlock09, besselGridStateBlock10,
    besselGridStateBlock11, besselGridStateBlock12, besselGridStateBlock13,
    besselGridStateBlock14, besselGridState006, besselGridState009, besselGridState013, besselGridState016, besselGridState017, besselGridState022, besselGridState023, besselGridState026, besselGridState029, besselGridState030, besselGridState032, besselGridState034, besselGridState035, besselGridState037, besselGridState038, besselGridState043, besselGridState045, besselGridState046, besselGridState051, besselGridState055, besselGridState058, besselGridState063, besselGridState066, besselGridState068, besselStateSubset, linearInterval, widenInterval,
    rationalErrorInterval, rationalIntervalSubset, orderedInterval, Finset.sum_range_succ,
    IntervalRat.add, IntervalRat.mul, IntervalRat.scale, IntervalRat.singleton]

theorem compactCertificate209_stateChecks6 :
    compactCertificate209.stateChecks 18 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 30 12 (6061338626197607 / 64000000000000)) (orderedInterval (77666280212 / 1000000000000) (77666280213 / 1000000000000), orderedInterval (25853394465 / 1000000000000) (25853394466 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 26 12 (5138263880914927 / 64000000000000)) (orderedInterval (-51171989577 / 1000000000000) (-51171972964 / 1000000000000), orderedInterval (73194876613 / 1000000000000) (73194893225 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 16 12 (3215286959434981 / 64000000000000)) (orderedInterval (77246025116 / 1000000000000) (77246025117 / 1000000000000), orderedInterval (81115034516 / 1000000000000) (81115034517 / 1000000000000))) = true
  norm_num [besselStateAtRationalPoint, besselIntervalStepZero,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, besselZeroTransition,
    besselInitial, besselGridStateAt, besselGridStateBlock00, besselGridStateBlock01,
    besselGridStateBlock02, besselGridStateBlock03, besselGridStateBlock04,
    besselGridStateBlock05, besselGridStateBlock06, besselGridStateBlock07,
    besselGridStateBlock08, besselGridStateBlock09, besselGridStateBlock10,
    besselGridStateBlock11, besselGridStateBlock12, besselGridStateBlock13,
    besselGridStateBlock14, besselGridState006, besselGridState009, besselGridState013, besselGridState016, besselGridState017, besselGridState022, besselGridState023, besselGridState026, besselGridState029, besselGridState030, besselGridState032, besselGridState034, besselGridState035, besselGridState037, besselGridState038, besselGridState043, besselGridState045, besselGridState046, besselGridState051, besselGridState055, besselGridState058, besselGridState063, besselGridState066, besselGridState068, besselStateSubset, linearInterval, widenInterval,
    rationalErrorInterval, rationalIntervalSubset, orderedInterval, Finset.sum_range_succ,
    IntervalRat.add, IntervalRat.mul, IntervalRat.scale, IntervalRat.singleton]

theorem compactCertificate209_stateChecks7 :
    compactCertificate209.stateChecks 21 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 9 12 (1729192020345627 / 64000000000000)) (orderedInterval (70186391335 / 1000000000000) (70186396675 / 1000000000000), orderedInterval (-137821188910 / 1000000000000) (-137821183569 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 23 12 (4695092710997881 / 64000000000000)) (orderedInterval (-88510242876 / 1000000000000) (-88510241094 / 1000000000000), orderedInterval (29649744840 / 1000000000000) (29649746622 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 32 12 (6410747701045337 / 64000000000000)) (orderedInterval (32588469662 / 1000000000000) (32588469663 / 1000000000000), orderedInterval (72594252519 / 1000000000000) (72594252520 / 1000000000000))) = true
  norm_num [besselStateAtRationalPoint, besselIntervalStepZero,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, besselZeroTransition,
    besselInitial, besselGridStateAt, besselGridStateBlock00, besselGridStateBlock01,
    besselGridStateBlock02, besselGridStateBlock03, besselGridStateBlock04,
    besselGridStateBlock05, besselGridStateBlock06, besselGridStateBlock07,
    besselGridStateBlock08, besselGridStateBlock09, besselGridStateBlock10,
    besselGridStateBlock11, besselGridStateBlock12, besselGridStateBlock13,
    besselGridStateBlock14, besselGridState006, besselGridState009, besselGridState013, besselGridState016, besselGridState017, besselGridState022, besselGridState023, besselGridState026, besselGridState029, besselGridState030, besselGridState032, besselGridState034, besselGridState035, besselGridState037, besselGridState038, besselGridState043, besselGridState045, besselGridState046, besselGridState051, besselGridState055, besselGridState058, besselGridState063, besselGridState066, besselGridState068, besselStateSubset, linearInterval, widenInterval,
    rationalErrorInterval, rationalIntervalSubset, orderedInterval, Finset.sum_range_succ,
    IntervalRat.add, IntervalRat.mul, IntervalRat.scale, IntervalRat.singleton]

theorem compactCertificate209_stateChecks8 :
    compactCertificate209.stateChecks 24 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 13 12 (2710713040565019 / 64000000000000)) (orderedInterval (-91694235258 / 1000000000000) (-91694150970 / 1000000000000), orderedInterval (82461970526 / 1000000000000) (82462054814 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 55 12 (11018898015608699 / 64000000000000)) (orderedInterval (-10129231955 / 1000000000000) (-10129231954 / 1000000000000), orderedInterval (-59929156792 / 1000000000000) (-59929156791 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 37 12 (7360113213915541 / 64000000000000)) (orderedInterval (32553056643 / 1000000000000) (32553059353 / 1000000000000), orderedInterval (-67044966741 / 1000000000000) (-67044964032 / 1000000000000))) = true
  norm_num [besselStateAtRationalPoint, besselIntervalStepZero,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, besselZeroTransition,
    besselInitial, besselGridStateAt, besselGridStateBlock00, besselGridStateBlock01,
    besselGridStateBlock02, besselGridStateBlock03, besselGridStateBlock04,
    besselGridStateBlock05, besselGridStateBlock06, besselGridStateBlock07,
    besselGridStateBlock08, besselGridStateBlock09, besselGridStateBlock10,
    besselGridStateBlock11, besselGridStateBlock12, besselGridStateBlock13,
    besselGridStateBlock14, besselGridState006, besselGridState009, besselGridState013, besselGridState016, besselGridState017, besselGridState022, besselGridState023, besselGridState026, besselGridState029, besselGridState030, besselGridState032, besselGridState034, besselGridState035, besselGridState037, besselGridState038, besselGridState043, besselGridState045, besselGridState046, besselGridState051, besselGridState055, besselGridState058, besselGridState063, besselGridState066, besselGridState068, besselStateSubset, linearInterval, widenInterval,
    rationalErrorInterval, rationalIntervalSubset, orderedInterval, Finset.sum_range_succ,
    IntervalRat.add, IntervalRat.mul, IntervalRat.scale, IntervalRat.singleton]

theorem compactCertificate209_states : ∀ j,
    BesselStateValid (compactCertificate209.point j) (compactCertificate209.state j) :=
  compactCertificate209.statesValid_of_checks3 compactCertificate209_stateChecks0
    compactCertificate209_stateChecks1 compactCertificate209_stateChecks2
    compactCertificate209_stateChecks3 compactCertificate209_stateChecks4
    compactCertificate209_stateChecks5 compactCertificate209_stateChecks6
    compactCertificate209_stateChecks7 compactCertificate209_stateChecks8

theorem compactCertificate209_chunkChecks0_0 :
    compactCertificate209.chunkChecks (0 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 0) <| besselDerivativeNearFromState (2963 / 32) 0 (IntervalRat.scale (2963 / 32) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-63375266443 / 1000000000000) (-63375182967 / 1000000000000), orderedInterval (53811517147 / 1000000000000) (53811600624 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 0) <| besselDerivativeNearFromState (4365064778630663 / 64000000000000) 0 (IntervalRat.scale (2963 / 32) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-12268864344 / 1000000000000) (-12268864285 / 1000000000000), orderedInterval (95921832680 / 1000000000000) (95921832738 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 0) <| besselDerivativeNearFromState (1411572263493479 / 12800000000000) 0 (IntervalRat.scale (2963 / 32) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-67972815577 / 1000000000000) (-67972815576 / 1000000000000), orderedInterval (-33639823537 / 1000000000000) (-33639823536 / 1000000000000)))) (orderedInterval (-29222781365 / 1000000000000) (-29222748270 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 0) <| besselDerivativeNearFromState (1273715015777941 / 64000000000000) 0 (IntervalRat.scale (2963 / 32) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (172787413872 / 1000000000000) (172787414573 / 1000000000000), orderedInterval (-50423486746 / 1000000000000) (-50423486045 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 0) <| besselDerivativeNearFromState (3421377695216977 / 64000000000000) 0 (IntervalRat.scale (2963 / 32) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-80894056429 / 1000000000000) (-80894056428 / 1000000000000), orderedInterval (-72487275100 / 1000000000000) (-72487275099 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 0) <| besselDerivativeNearFromState (9289705995260109 / 64000000000000) 0 (IntervalRat.scale (2963 / 32) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (65503218626 / 1000000000000) (65503218631 / 1000000000000), orderedInterval (9531282111 / 1000000000000) (9531282116 / 1000000000000)))) (orderedInterval (-9484804486 / 1000000000000) (-9484804466 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 0) <| besselDerivativeNearFromState (6842755390436917 / 64000000000000) 0 (IntervalRat.scale (2963 / 32) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (59870773850 / 1000000000000) (59870773851 / 1000000000000), orderedInterval (48400149074 / 1000000000000) (48400149075 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 0) <| besselDerivativeNearFromState (11725177992543241 / 64000000000000) 0 (IntervalRat.scale (2963 / 32) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (57684150757 / 1000000000000) (57684151696 / 1000000000000), orderedInterval (-12298828708 / 1000000000000) (-12298827769 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 0) <| besselDerivativeNearFromState (8636713040565019 / 64000000000000) 0 (IntervalRat.scale (2963 / 32) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-41272231504 / 1000000000000) (-41272231503 / 1000000000000), orderedInterval (-54747981991 / 1000000000000) (-54747981990 / 1000000000000)))) (orderedInterval (-2776678441 / 1000000000000) (-2776678406 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate209_chunkChecks0_1 :
    compactCertificate209.chunkChecks (0 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 0) <| besselDerivativeNearFromState (13250938834662037 / 64000000000000) 0 (IntervalRat.scale (2963 / 32) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (25880883652 / 1000000000000) (25880883653 / 1000000000000), orderedInterval (48977898400 / 1000000000000) (48977898401 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 0) <| besselDerivativeNearFromState (7650433103206573 / 64000000000000) 0 (IntervalRat.scale (2963 / 32) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (59012527660 / 1000000000000) (59012527661 / 1000000000000), orderedInterval (42685383285 / 1000000000000) (42685383286 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 0) <| besselDerivativeNearFromState (13575827793915857 / 64000000000000) 0 (IntervalRat.scale (2963 / 32) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-36171790063 / 1000000000000) (-36171765111 / 1000000000000), orderedInterval (41228844478 / 1000000000000) (41228869430 / 1000000000000)))) (orderedInterval (-5368410954 / 1000000000000) (-5368407369 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 0) <| besselDerivativeNearFromState (12684299335140533 / 64000000000000) 0 (IntervalRat.scale (2963 / 32) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-49346985872 / 1000000000000) (-49346985871 / 1000000000000), orderedInterval (-27750289009 / 1000000000000) (-27750289008 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 0) <| besselDerivativeNearFromState (9052114522766789 / 64000000000000) 0 (IntervalRat.scale (2963 / 32) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-50497316941 / 1000000000000) (-50497316940 / 1000000000000), orderedInterval (-43991933197 / 1000000000000) (-43991933196 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 0) <| besselDerivativeNearFromState (10264133085650931 / 64000000000000) 0 (IntervalRat.scale (2963 / 32) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-50896925950 / 1000000000000) (-50896925949 / 1000000000000), orderedInterval (-36976420159 / 1000000000000) (-36976420158 / 1000000000000)))) (orderedInterval (-3626737879 / 1000000000000) (-3626737867 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 0) <| besselDerivativeNearFromState (8557164077148739 / 64000000000000) 0 (IntervalRat.scale (2963 / 32) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (38866585152 / 1000000000000) (38866596368 / 1000000000000), orderedInterval (-57160710853 / 1000000000000) (-57160699636 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 0) <| besselDerivativeNearFromState (7560513974911519 / 64000000000000) 0 (IntervalRat.scale (2963 / 32) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-32797058184 / 1000000000000) (-32797055201 / 1000000000000), orderedInterval (65815209304 / 1000000000000) (65815212287 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 0) <| besselDerivativeNearFromState (2191331635116381 / 12800000000000) 0 (IntervalRat.scale (2963 / 32) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (43962569801 / 1000000000000) (43962633521 / 1000000000000), orderedInterval (-42388460616 / 1000000000000) (-42388396896 / 1000000000000)))) (orderedInterval (3451300418 / 1000000000000) (3451302360 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate209_chunkChecks0_2 :
    compactCertificate209.chunkChecks (0 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 0) <| besselDerivativeNearFromState (6061338626197607 / 64000000000000) 0 (IntervalRat.scale (2963 / 32) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (77666280212 / 1000000000000) (77666280213 / 1000000000000), orderedInterval (25853394465 / 1000000000000) (25853394466 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 0) <| besselDerivativeNearFromState (5138263880914927 / 64000000000000) 0 (IntervalRat.scale (2963 / 32) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-51171989577 / 1000000000000) (-51171972964 / 1000000000000), orderedInterval (73194876613 / 1000000000000) (73194893225 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 0) <| besselDerivativeNearFromState (3215286959434981 / 64000000000000) 0 (IntervalRat.scale (2963 / 32) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (77246025116 / 1000000000000) (77246025117 / 1000000000000), orderedInterval (81115034516 / 1000000000000) (81115034517 / 1000000000000)))) (orderedInterval (-7007154517 / 1000000000000) (-7007153552 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 0) <| besselDerivativeNearFromState (1729192020345627 / 64000000000000) 0 (IntervalRat.scale (2963 / 32) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (70186391335 / 1000000000000) (70186396675 / 1000000000000), orderedInterval (-137821188910 / 1000000000000) (-137821183569 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 0) <| besselDerivativeNearFromState (4695092710997881 / 64000000000000) 0 (IntervalRat.scale (2963 / 32) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-88510242876 / 1000000000000) (-88510241094 / 1000000000000), orderedInterval (29649744840 / 1000000000000) (29649746622 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 0) <| besselDerivativeNearFromState (6410747701045337 / 64000000000000) 0 (IntervalRat.scale (2963 / 32) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (32588469662 / 1000000000000) (32588469663 / 1000000000000), orderedInterval (72594252519 / 1000000000000) (72594252520 / 1000000000000)))) (orderedInterval (-1785523897 / 1000000000000) (-1785523746 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 0) <| besselDerivativeNearFromState (2710713040565019 / 64000000000000) 0 (IntervalRat.scale (2963 / 32) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-91694235258 / 1000000000000) (-91694150970 / 1000000000000), orderedInterval (82461970526 / 1000000000000) (82462054814 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 0) <| besselDerivativeNearFromState (11018898015608699 / 64000000000000) 0 (IntervalRat.scale (2963 / 32) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-10129231955 / 1000000000000) (-10129231954 / 1000000000000), orderedInterval (-59929156792 / 1000000000000) (-59929156791 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 0) <| besselDerivativeNearFromState (7360113213915541 / 64000000000000) 0 (IntervalRat.scale (2963 / 32) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (32553056643 / 1000000000000) (32553059353 / 1000000000000), orderedInterval (-67044966741 / 1000000000000) (-67044964032 / 1000000000000)))) (orderedInterval (-5836042928 / 1000000000000) (-5836041885 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate209_chunkChecks0 :
    compactCertificate209.chunkChecks (0 : Fin 5) 0 9 = true :=
  compactCertificate209.chunkChecks_nine_of_three (0 : Fin 5) compactCertificate209_chunkChecks0_0
    compactCertificate209_chunkChecks0_1 compactCertificate209_chunkChecks0_2

theorem compactCertificate209_chunkChecks1_0 :
    compactCertificate209.chunkChecks (1 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 1) <| besselDerivativeNearFromState (2963 / 32) 1 (IntervalRat.scale (2963 / 32) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-63375266443 / 1000000000000) (-63375182967 / 1000000000000), orderedInterval (53811517147 / 1000000000000) (53811600624 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 1) <| besselDerivativeNearFromState (4365064778630663 / 64000000000000) 1 (IntervalRat.scale (2963 / 32) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-12268864344 / 1000000000000) (-12268864285 / 1000000000000), orderedInterval (95921832680 / 1000000000000) (95921832738 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 1) <| besselDerivativeNearFromState (1411572263493479 / 12800000000000) 1 (IntervalRat.scale (2963 / 32) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-67972815577 / 1000000000000) (-67972815576 / 1000000000000), orderedInterval (-33639823537 / 1000000000000) (-33639823536 / 1000000000000)))) (orderedInterval (19636314555 / 1000000000000) (19636347651 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 1) <| besselDerivativeNearFromState (1273715015777941 / 64000000000000) 1 (IntervalRat.scale (2963 / 32) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (172787413872 / 1000000000000) (172787414573 / 1000000000000), orderedInterval (-50423486746 / 1000000000000) (-50423486045 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 1) <| besselDerivativeNearFromState (3421377695216977 / 64000000000000) 1 (IntervalRat.scale (2963 / 32) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-80894056429 / 1000000000000) (-80894056428 / 1000000000000), orderedInterval (-72487275100 / 1000000000000) (-72487275099 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 1) <| besselDerivativeNearFromState (9289705995260109 / 64000000000000) 1 (IntervalRat.scale (2963 / 32) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (65503218626 / 1000000000000) (65503218631 / 1000000000000), orderedInterval (9531282111 / 1000000000000) (9531282116 / 1000000000000)))) (orderedInterval (-2472633122 / 1000000000000) (-2472633106 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 1) <| besselDerivativeNearFromState (6842755390436917 / 64000000000000) 1 (IntervalRat.scale (2963 / 32) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (59870773850 / 1000000000000) (59870773851 / 1000000000000), orderedInterval (48400149074 / 1000000000000) (48400149075 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 1) <| besselDerivativeNearFromState (11725177992543241 / 64000000000000) 1 (IntervalRat.scale (2963 / 32) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (57684150757 / 1000000000000) (57684151696 / 1000000000000), orderedInterval (-12298828708 / 1000000000000) (-12298827769 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 1) <| besselDerivativeNearFromState (8636713040565019 / 64000000000000) 1 (IntervalRat.scale (2963 / 32) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-41272231504 / 1000000000000) (-41272231503 / 1000000000000), orderedInterval (-54747981991 / 1000000000000) (-54747981990 / 1000000000000)))) (orderedInterval (-1177823944 / 1000000000000) (-1177823877 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate209_chunkChecks1_1 :
    compactCertificate209.chunkChecks (1 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 1) <| besselDerivativeNearFromState (13250938834662037 / 64000000000000) 1 (IntervalRat.scale (2963 / 32) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (25880883652 / 1000000000000) (25880883653 / 1000000000000), orderedInterval (48977898400 / 1000000000000) (48977898401 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 1) <| besselDerivativeNearFromState (7650433103206573 / 64000000000000) 1 (IntervalRat.scale (2963 / 32) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (59012527660 / 1000000000000) (59012527661 / 1000000000000), orderedInterval (42685383285 / 1000000000000) (42685383286 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 1) <| besselDerivativeNearFromState (13575827793915857 / 64000000000000) 1 (IntervalRat.scale (2963 / 32) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-36171790063 / 1000000000000) (-36171765111 / 1000000000000), orderedInterval (41228844478 / 1000000000000) (41228869430 / 1000000000000)))) (orderedInterval (-1950321538 / 1000000000000) (-1950313334 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 1) <| besselDerivativeNearFromState (12684299335140533 / 64000000000000) 1 (IntervalRat.scale (2963 / 32) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-49346985872 / 1000000000000) (-49346985871 / 1000000000000), orderedInterval (-27750289009 / 1000000000000) (-27750289008 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 1) <| besselDerivativeNearFromState (9052114522766789 / 64000000000000) 1 (IntervalRat.scale (2963 / 32) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-50497316941 / 1000000000000) (-50497316940 / 1000000000000), orderedInterval (-43991933197 / 1000000000000) (-43991933196 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 1) <| besselDerivativeNearFromState (10264133085650931 / 64000000000000) 1 (IntervalRat.scale (2963 / 32) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-50896925950 / 1000000000000) (-50896925949 / 1000000000000), orderedInterval (-36976420159 / 1000000000000) (-36976420158 / 1000000000000)))) (orderedInterval (-4958086710 / 1000000000000) (-4958086691 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 1) <| besselDerivativeNearFromState (8557164077148739 / 64000000000000) 1 (IntervalRat.scale (2963 / 32) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (38866585152 / 1000000000000) (38866596368 / 1000000000000), orderedInterval (-57160710853 / 1000000000000) (-57160699636 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 1) <| besselDerivativeNearFromState (7560513974911519 / 64000000000000) 1 (IntervalRat.scale (2963 / 32) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-32797058184 / 1000000000000) (-32797055201 / 1000000000000), orderedInterval (65815209304 / 1000000000000) (65815212287 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 1) <| besselDerivativeNearFromState (2191331635116381 / 12800000000000) 1 (IntervalRat.scale (2963 / 32) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (43962569801 / 1000000000000) (43962633521 / 1000000000000), orderedInterval (-42388460616 / 1000000000000) (-42388396896 / 1000000000000)))) (orderedInterval (-7765028570 / 1000000000000) (-7765025135 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate209_chunkChecks1_2 :
    compactCertificate209.chunkChecks (1 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 1) <| besselDerivativeNearFromState (6061338626197607 / 64000000000000) 1 (IntervalRat.scale (2963 / 32) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (77666280212 / 1000000000000) (77666280213 / 1000000000000), orderedInterval (25853394465 / 1000000000000) (25853394466 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 1) <| besselDerivativeNearFromState (5138263880914927 / 64000000000000) 1 (IntervalRat.scale (2963 / 32) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-51171989577 / 1000000000000) (-51171972964 / 1000000000000), orderedInterval (73194876613 / 1000000000000) (73194893225 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 1) <| besselDerivativeNearFromState (3215286959434981 / 64000000000000) 1 (IntervalRat.scale (2963 / 32) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (77246025116 / 1000000000000) (77246025117 / 1000000000000), orderedInterval (81115034516 / 1000000000000) (81115034517 / 1000000000000)))) (orderedInterval (-6387512142 / 1000000000000) (-6387511304 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 1) <| besselDerivativeNearFromState (1729192020345627 / 64000000000000) 1 (IntervalRat.scale (2963 / 32) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (70186391335 / 1000000000000) (70186396675 / 1000000000000), orderedInterval (-137821188910 / 1000000000000) (-137821183569 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 1) <| besselDerivativeNearFromState (4695092710997881 / 64000000000000) 1 (IntervalRat.scale (2963 / 32) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-88510242876 / 1000000000000) (-88510241094 / 1000000000000), orderedInterval (29649744840 / 1000000000000) (29649746622 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 1) <| besselDerivativeNearFromState (6410747701045337 / 64000000000000) 1 (IntervalRat.scale (2963 / 32) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (32588469662 / 1000000000000) (32588469663 / 1000000000000), orderedInterval (72594252519 / 1000000000000) (72594252520 / 1000000000000)))) (orderedInterval (-5808988678 / 1000000000000) (-5808988606 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 1) <| besselDerivativeNearFromState (2710713040565019 / 64000000000000) 1 (IntervalRat.scale (2963 / 32) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-91694235258 / 1000000000000) (-91694150970 / 1000000000000), orderedInterval (82461970526 / 1000000000000) (82462054814 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 1) <| besselDerivativeNearFromState (11018898015608699 / 64000000000000) 1 (IntervalRat.scale (2963 / 32) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-10129231955 / 1000000000000) (-10129231954 / 1000000000000), orderedInterval (-59929156792 / 1000000000000) (-59929156791 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 1) <| besselDerivativeNearFromState (7360113213915541 / 64000000000000) 1 (IntervalRat.scale (2963 / 32) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (32553056643 / 1000000000000) (32553059353 / 1000000000000), orderedInterval (-67044966741 / 1000000000000) (-67044964032 / 1000000000000)))) (orderedInterval (24921929677 / 1000000000000) (24921930578 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate209_chunkChecks1 :
    compactCertificate209.chunkChecks (1 : Fin 5) 0 9 = true :=
  compactCertificate209.chunkChecks_nine_of_three (1 : Fin 5) compactCertificate209_chunkChecks1_0
    compactCertificate209_chunkChecks1_1 compactCertificate209_chunkChecks1_2

theorem compactCertificate209_chunkChecks2_0 :
    compactCertificate209.chunkChecks (2 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 2) <| besselDerivativeNearFromState (2963 / 32) 2 (IntervalRat.scale (2963 / 32) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-63375266443 / 1000000000000) (-63375182967 / 1000000000000), orderedInterval (53811517147 / 1000000000000) (53811600624 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 2) <| besselDerivativeNearFromState (4365064778630663 / 64000000000000) 2 (IntervalRat.scale (2963 / 32) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-12268864344 / 1000000000000) (-12268864285 / 1000000000000), orderedInterval (95921832680 / 1000000000000) (95921832738 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 2) <| besselDerivativeNearFromState (1411572263493479 / 12800000000000) 2 (IntervalRat.scale (2963 / 32) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-67972815577 / 1000000000000) (-67972815576 / 1000000000000), orderedInterval (-33639823537 / 1000000000000) (-33639823536 / 1000000000000)))) (orderedInterval (30627581370 / 1000000000000) (30627614823 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 2) <| besselDerivativeNearFromState (1273715015777941 / 64000000000000) 2 (IntervalRat.scale (2963 / 32) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (172787413872 / 1000000000000) (172787414573 / 1000000000000), orderedInterval (-50423486746 / 1000000000000) (-50423486045 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 2) <| besselDerivativeNearFromState (3421377695216977 / 64000000000000) 2 (IntervalRat.scale (2963 / 32) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-80894056429 / 1000000000000) (-80894056428 / 1000000000000), orderedInterval (-72487275100 / 1000000000000) (-72487275099 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 2) <| besselDerivativeNearFromState (9289705995260109 / 64000000000000) 2 (IntervalRat.scale (2963 / 32) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (65503218626 / 1000000000000) (65503218631 / 1000000000000), orderedInterval (9531282111 / 1000000000000) (9531282116 / 1000000000000)))) (orderedInterval (12541090993 / 1000000000000) (12541091013 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 2) <| besselDerivativeNearFromState (6842755390436917 / 64000000000000) 2 (IntervalRat.scale (2963 / 32) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (59870773850 / 1000000000000) (59870773851 / 1000000000000), orderedInterval (48400149074 / 1000000000000) (48400149075 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 2) <| besselDerivativeNearFromState (11725177992543241 / 64000000000000) 2 (IntervalRat.scale (2963 / 32) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (57684150757 / 1000000000000) (57684151696 / 1000000000000), orderedInterval (-12298828708 / 1000000000000) (-12298827769 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 2) <| besselDerivativeNearFromState (8636713040565019 / 64000000000000) 2 (IntervalRat.scale (2963 / 32) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-41272231504 / 1000000000000) (-41272231503 / 1000000000000), orderedInterval (-54747981991 / 1000000000000) (-54747981990 / 1000000000000)))) (orderedInterval (9096784543 / 1000000000000) (9096784674 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate209_chunkChecks2_1 :
    compactCertificate209.chunkChecks (2 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 2) <| besselDerivativeNearFromState (13250938834662037 / 64000000000000) 2 (IntervalRat.scale (2963 / 32) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (25880883652 / 1000000000000) (25880883653 / 1000000000000), orderedInterval (48977898400 / 1000000000000) (48977898401 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 2) <| besselDerivativeNearFromState (7650433103206573 / 64000000000000) 2 (IntervalRat.scale (2963 / 32) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (59012527660 / 1000000000000) (59012527661 / 1000000000000), orderedInterval (42685383285 / 1000000000000) (42685383286 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 2) <| besselDerivativeNearFromState (13575827793915857 / 64000000000000) 2 (IntervalRat.scale (2963 / 32) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-36171790063 / 1000000000000) (-36171765111 / 1000000000000), orderedInterval (41228844478 / 1000000000000) (41228869430 / 1000000000000)))) (orderedInterval (42713763305 / 1000000000000) (42713782173 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 2) <| besselDerivativeNearFromState (12684299335140533 / 64000000000000) 2 (IntervalRat.scale (2963 / 32) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-49346985872 / 1000000000000) (-49346985871 / 1000000000000), orderedInterval (-27750289009 / 1000000000000) (-27750289008 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 2) <| besselDerivativeNearFromState (9052114522766789 / 64000000000000) 2 (IntervalRat.scale (2963 / 32) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-50497316941 / 1000000000000) (-50497316940 / 1000000000000), orderedInterval (-43991933197 / 1000000000000) (-43991933196 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 2) <| besselDerivativeNearFromState (10264133085650931 / 64000000000000) 2 (IntervalRat.scale (2963 / 32) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-50896925950 / 1000000000000) (-50896925949 / 1000000000000), orderedInterval (-36976420159 / 1000000000000) (-36976420158 / 1000000000000)))) (orderedInterval (6341390727 / 1000000000000) (6341390758 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 2) <| besselDerivativeNearFromState (8557164077148739 / 64000000000000) 2 (IntervalRat.scale (2963 / 32) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (38866585152 / 1000000000000) (38866596368 / 1000000000000), orderedInterval (-57160710853 / 1000000000000) (-57160699636 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 2) <| besselDerivativeNearFromState (7560513974911519 / 64000000000000) 2 (IntervalRat.scale (2963 / 32) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-32797058184 / 1000000000000) (-32797055201 / 1000000000000), orderedInterval (65815209304 / 1000000000000) (65815212287 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 2) <| besselDerivativeNearFromState (2191331635116381 / 12800000000000) 2 (IntervalRat.scale (2963 / 32) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (43962569801 / 1000000000000) (43962633521 / 1000000000000), orderedInterval (-42388460616 / 1000000000000) (-42388396896 / 1000000000000)))) (orderedInterval (-7754900418 / 1000000000000) (-7754894235 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate209_chunkChecks2_2 :
    compactCertificate209.chunkChecks (2 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 2) <| besselDerivativeNearFromState (6061338626197607 / 64000000000000) 2 (IntervalRat.scale (2963 / 32) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (77666280212 / 1000000000000) (77666280213 / 1000000000000), orderedInterval (25853394465 / 1000000000000) (25853394466 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 2) <| besselDerivativeNearFromState (5138263880914927 / 64000000000000) 2 (IntervalRat.scale (2963 / 32) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-51171989577 / 1000000000000) (-51171972964 / 1000000000000), orderedInterval (73194876613 / 1000000000000) (73194893225 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 2) <| besselDerivativeNearFromState (3215286959434981 / 64000000000000) 2 (IntervalRat.scale (2963 / 32) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (77246025116 / 1000000000000) (77246025117 / 1000000000000), orderedInterval (81115034516 / 1000000000000) (81115034517 / 1000000000000)))) (orderedInterval (10143122500 / 1000000000000) (10143123238 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 2) <| besselDerivativeNearFromState (1729192020345627 / 64000000000000) 2 (IntervalRat.scale (2963 / 32) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (70186391335 / 1000000000000) (70186396675 / 1000000000000), orderedInterval (-137821188910 / 1000000000000) (-137821183569 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 2) <| besselDerivativeNearFromState (4695092710997881 / 64000000000000) 2 (IntervalRat.scale (2963 / 32) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-88510242876 / 1000000000000) (-88510241094 / 1000000000000), orderedInterval (29649744840 / 1000000000000) (29649746622 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 2) <| besselDerivativeNearFromState (6410747701045337 / 64000000000000) 2 (IntervalRat.scale (2963 / 32) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (32588469662 / 1000000000000) (32588469663 / 1000000000000), orderedInterval (72594252519 / 1000000000000) (72594252520 / 1000000000000)))) (orderedInterval (1835467860 / 1000000000000) (1835467905 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 2) <| besselDerivativeNearFromState (2710713040565019 / 64000000000000) 2 (IntervalRat.scale (2963 / 32) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-91694235258 / 1000000000000) (-91694150970 / 1000000000000), orderedInterval (82461970526 / 1000000000000) (82462054814 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 2) <| besselDerivativeNearFromState (11018898015608699 / 64000000000000) 2 (IntervalRat.scale (2963 / 32) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-10129231955 / 1000000000000) (-10129231954 / 1000000000000), orderedInterval (-59929156792 / 1000000000000) (-59929156791 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 2) <| besselDerivativeNearFromState (7360113213915541 / 64000000000000) 2 (IntervalRat.scale (2963 / 32) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (32553056643 / 1000000000000) (32553059353 / 1000000000000), orderedInterval (-67044966741 / 1000000000000) (-67044964032 / 1000000000000)))) (orderedInterval (6417480890 / 1000000000000) (6417481844 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate209_chunkChecks2 :
    compactCertificate209.chunkChecks (2 : Fin 5) 0 9 = true :=
  compactCertificate209.chunkChecks_nine_of_three (2 : Fin 5) compactCertificate209_chunkChecks2_0
    compactCertificate209_chunkChecks2_1 compactCertificate209_chunkChecks2_2

theorem compactCertificate209_chunkChecks3_0 :
    compactCertificate209.chunkChecks (3 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 3) <| besselDerivativeNearFromState (2963 / 32) 3 (IntervalRat.scale (2963 / 32) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-63375266443 / 1000000000000) (-63375182967 / 1000000000000), orderedInterval (53811517147 / 1000000000000) (53811600624 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 3) <| besselDerivativeNearFromState (4365064778630663 / 64000000000000) 3 (IntervalRat.scale (2963 / 32) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-12268864344 / 1000000000000) (-12268864285 / 1000000000000), orderedInterval (95921832680 / 1000000000000) (95921832738 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 3) <| besselDerivativeNearFromState (1411572263493479 / 12800000000000) 3 (IntervalRat.scale (2963 / 32) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-67972815577 / 1000000000000) (-67972815576 / 1000000000000), orderedInterval (-33639823537 / 1000000000000) (-33639823536 / 1000000000000)))) (orderedInterval (-18679804225 / 1000000000000) (-18679770777 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 3) <| besselDerivativeNearFromState (1273715015777941 / 64000000000000) 3 (IntervalRat.scale (2963 / 32) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (172787413872 / 1000000000000) (172787414573 / 1000000000000), orderedInterval (-50423486746 / 1000000000000) (-50423486045 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 3) <| besselDerivativeNearFromState (3421377695216977 / 64000000000000) 3 (IntervalRat.scale (2963 / 32) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-80894056429 / 1000000000000) (-80894056428 / 1000000000000), orderedInterval (-72487275100 / 1000000000000) (-72487275099 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 3) <| besselDerivativeNearFromState (9289705995260109 / 64000000000000) 3 (IntervalRat.scale (2963 / 32) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (65503218626 / 1000000000000) (65503218631 / 1000000000000), orderedInterval (9531282111 / 1000000000000) (9531282116 / 1000000000000)))) (orderedInterval (2978411951 / 1000000000000) (2978411979 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 3) <| besselDerivativeNearFromState (6842755390436917 / 64000000000000) 3 (IntervalRat.scale (2963 / 32) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (59870773850 / 1000000000000) (59870773851 / 1000000000000), orderedInterval (48400149074 / 1000000000000) (48400149075 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 3) <| besselDerivativeNearFromState (11725177992543241 / 64000000000000) 3 (IntervalRat.scale (2963 / 32) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (57684150757 / 1000000000000) (57684151696 / 1000000000000), orderedInterval (-12298828708 / 1000000000000) (-12298827769 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 3) <| besselDerivativeNearFromState (8636713040565019 / 64000000000000) 3 (IntervalRat.scale (2963 / 32) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-41272231504 / 1000000000000) (-41272231503 / 1000000000000), orderedInterval (-54747981991 / 1000000000000) (-54747981990 / 1000000000000)))) (orderedInterval (1059332601 / 1000000000000) (1059332857 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate209_chunkChecks3_1 :
    compactCertificate209.chunkChecks (3 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 3) <| besselDerivativeNearFromState (13250938834662037 / 64000000000000) 3 (IntervalRat.scale (2963 / 32) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (25880883652 / 1000000000000) (25880883653 / 1000000000000), orderedInterval (48977898400 / 1000000000000) (48977898401 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 3) <| besselDerivativeNearFromState (7650433103206573 / 64000000000000) 3 (IntervalRat.scale (2963 / 32) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (59012527660 / 1000000000000) (59012527661 / 1000000000000), orderedInterval (42685383285 / 1000000000000) (42685383286 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 3) <| besselDerivativeNearFromState (13575827793915857 / 64000000000000) 3 (IntervalRat.scale (2963 / 32) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-36171790063 / 1000000000000) (-36171765111 / 1000000000000), orderedInterval (41228844478 / 1000000000000) (41228869430 / 1000000000000)))) (orderedInterval (19567500348 / 1000000000000) (19567543554 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 3) <| besselDerivativeNearFromState (12684299335140533 / 64000000000000) 3 (IntervalRat.scale (2963 / 32) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-49346985872 / 1000000000000) (-49346985871 / 1000000000000), orderedInterval (-27750289009 / 1000000000000) (-27750289008 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 3) <| besselDerivativeNearFromState (9052114522766789 / 64000000000000) 3 (IntervalRat.scale (2963 / 32) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-50497316941 / 1000000000000) (-50497316940 / 1000000000000), orderedInterval (-43991933197 / 1000000000000) (-43991933196 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 3) <| besselDerivativeNearFromState (10264133085650931 / 64000000000000) 3 (IntervalRat.scale (2963 / 32) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-50896925950 / 1000000000000) (-50896925949 / 1000000000000), orderedInterval (-36976420159 / 1000000000000) (-36976420158 / 1000000000000)))) (orderedInterval (8872961536 / 1000000000000) (8872961588 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 3) <| besselDerivativeNearFromState (8557164077148739 / 64000000000000) 3 (IntervalRat.scale (2963 / 32) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (38866585152 / 1000000000000) (38866596368 / 1000000000000), orderedInterval (-57160710853 / 1000000000000) (-57160699636 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 3) <| besselDerivativeNearFromState (7560513974911519 / 64000000000000) 3 (IntervalRat.scale (2963 / 32) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-32797058184 / 1000000000000) (-32797055201 / 1000000000000), orderedInterval (65815209304 / 1000000000000) (65815212287 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 3) <| besselDerivativeNearFromState (2191331635116381 / 12800000000000) 3 (IntervalRat.scale (2963 / 32) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (43962569801 / 1000000000000) (43962633521 / 1000000000000), orderedInterval (-42388460616 / 1000000000000) (-42388396896 / 1000000000000)))) (orderedInterval (16751537559 / 1000000000000) (16751548711 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate209_chunkChecks3_2 :
    compactCertificate209.chunkChecks (3 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 3) <| besselDerivativeNearFromState (6061338626197607 / 64000000000000) 3 (IntervalRat.scale (2963 / 32) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (77666280212 / 1000000000000) (77666280213 / 1000000000000), orderedInterval (25853394465 / 1000000000000) (25853394466 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 3) <| besselDerivativeNearFromState (5138263880914927 / 64000000000000) 3 (IntervalRat.scale (2963 / 32) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-51171989577 / 1000000000000) (-51171972964 / 1000000000000), orderedInterval (73194876613 / 1000000000000) (73194893225 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 3) <| besselDerivativeNearFromState (3215286959434981 / 64000000000000) 3 (IntervalRat.scale (2963 / 32) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (77246025116 / 1000000000000) (77246025117 / 1000000000000), orderedInterval (81115034516 / 1000000000000) (81115034517 / 1000000000000)))) (orderedInterval (6592026634 / 1000000000000) (6592027276 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 3) <| besselDerivativeNearFromState (1729192020345627 / 64000000000000) 3 (IntervalRat.scale (2963 / 32) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (70186391335 / 1000000000000) (70186396675 / 1000000000000), orderedInterval (-137821188910 / 1000000000000) (-137821183569 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 3) <| besselDerivativeNearFromState (4695092710997881 / 64000000000000) 3 (IntervalRat.scale (2963 / 32) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-88510242876 / 1000000000000) (-88510241094 / 1000000000000), orderedInterval (29649744840 / 1000000000000) (29649746622 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 3) <| besselDerivativeNearFromState (6410747701045337 / 64000000000000) 3 (IntervalRat.scale (2963 / 32) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (32588469662 / 1000000000000) (32588469663 / 1000000000000), orderedInterval (72594252519 / 1000000000000) (72594252520 / 1000000000000)))) (orderedInterval (7294370914 / 1000000000000) (7294370948 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 3) <| besselDerivativeNearFromState (2710713040565019 / 64000000000000) 3 (IntervalRat.scale (2963 / 32) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-91694235258 / 1000000000000) (-91694150970 / 1000000000000), orderedInterval (82461970526 / 1000000000000) (82462054814 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 3) <| besselDerivativeNearFromState (11018898015608699 / 64000000000000) 3 (IntervalRat.scale (2963 / 32) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-10129231955 / 1000000000000) (-10129231954 / 1000000000000), orderedInterval (-59929156792 / 1000000000000) (-59929156791 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 3) <| besselDerivativeNearFromState (7360113213915541 / 64000000000000) 3 (IntervalRat.scale (2963 / 32) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (32553056643 / 1000000000000) (32553059353 / 1000000000000), orderedInterval (-67044966741 / 1000000000000) (-67044964032 / 1000000000000)))) (orderedInterval (-55576486616 / 1000000000000) (-55576485501 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate209_chunkChecks3 :
    compactCertificate209.chunkChecks (3 : Fin 5) 0 9 = true :=
  compactCertificate209.chunkChecks_nine_of_three (3 : Fin 5) compactCertificate209_chunkChecks3_0
    compactCertificate209_chunkChecks3_1 compactCertificate209_chunkChecks3_2

theorem compactCertificate209_chunkChecks4_0 :
    compactCertificate209.chunkChecks (4 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 4) <| besselDerivativeNearFromState (2963 / 32) 4 (IntervalRat.scale (2963 / 32) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-63375266443 / 1000000000000) (-63375182967 / 1000000000000), orderedInterval (53811517147 / 1000000000000) (53811600624 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 4) <| besselDerivativeNearFromState (4365064778630663 / 64000000000000) 4 (IntervalRat.scale (2963 / 32) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-12268864344 / 1000000000000) (-12268864285 / 1000000000000), orderedInterval (95921832680 / 1000000000000) (95921832738 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 4) <| besselDerivativeNearFromState (1411572263493479 / 12800000000000) 4 (IntervalRat.scale (2963 / 32) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-67972815577 / 1000000000000) (-67972815576 / 1000000000000), orderedInterval (-33639823537 / 1000000000000) (-33639823536 / 1000000000000)))) (orderedInterval (-32772006554 / 1000000000000) (-32771972752 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 4) <| besselDerivativeNearFromState (1273715015777941 / 64000000000000) 4 (IntervalRat.scale (2963 / 32) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (172787413872 / 1000000000000) (172787414573 / 1000000000000), orderedInterval (-50423486746 / 1000000000000) (-50423486045 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 4) <| besselDerivativeNearFromState (3421377695216977 / 64000000000000) 4 (IntervalRat.scale (2963 / 32) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-80894056429 / 1000000000000) (-80894056428 / 1000000000000), orderedInterval (-72487275100 / 1000000000000) (-72487275099 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 4) <| besselDerivativeNearFromState (9289705995260109 / 64000000000000) 4 (IntervalRat.scale (2963 / 32) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (65503218626 / 1000000000000) (65503218631 / 1000000000000), orderedInterval (9531282111 / 1000000000000) (9531282116 / 1000000000000)))) (orderedInterval (-28516010846 / 1000000000000) (-28516010803 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 4) <| besselDerivativeNearFromState (6842755390436917 / 64000000000000) 4 (IntervalRat.scale (2963 / 32) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (59870773850 / 1000000000000) (59870773851 / 1000000000000), orderedInterval (48400149074 / 1000000000000) (48400149075 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 4) <| besselDerivativeNearFromState (11725177992543241 / 64000000000000) 4 (IntervalRat.scale (2963 / 32) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (57684150757 / 1000000000000) (57684151696 / 1000000000000), orderedInterval (-12298828708 / 1000000000000) (-12298827769 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 4) <| besselDerivativeNearFromState (8636713040565019 / 64000000000000) 4 (IntervalRat.scale (2963 / 32) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-41272231504 / 1000000000000) (-41272231503 / 1000000000000), orderedInterval (-54747981991 / 1000000000000) (-54747981990 / 1000000000000)))) (orderedInterval (-31790492778 / 1000000000000) (-31790492274 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate209_chunkChecks4_1 :
    compactCertificate209.chunkChecks (4 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 4) <| besselDerivativeNearFromState (13250938834662037 / 64000000000000) 4 (IntervalRat.scale (2963 / 32) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (25880883652 / 1000000000000) (25880883653 / 1000000000000), orderedInterval (48977898400 / 1000000000000) (48977898401 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 4) <| besselDerivativeNearFromState (7650433103206573 / 64000000000000) 4 (IntervalRat.scale (2963 / 32) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (59012527660 / 1000000000000) (59012527661 / 1000000000000), orderedInterval (42685383285 / 1000000000000) (42685383286 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 4) <| besselDerivativeNearFromState (13575827793915857 / 64000000000000) 4 (IntervalRat.scale (2963 / 32) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-36171790063 / 1000000000000) (-36171765111 / 1000000000000), orderedInterval (41228844478 / 1000000000000) (41228869430 / 1000000000000)))) (orderedInterval (-244869733738 / 1000000000000) (-244869634326 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 4) <| besselDerivativeNearFromState (12684299335140533 / 64000000000000) 4 (IntervalRat.scale (2963 / 32) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-49346985872 / 1000000000000) (-49346985871 / 1000000000000), orderedInterval (-27750289009 / 1000000000000) (-27750289008 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 4) <| besselDerivativeNearFromState (9052114522766789 / 64000000000000) 4 (IntervalRat.scale (2963 / 32) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-50497316941 / 1000000000000) (-50497316940 / 1000000000000), orderedInterval (-43991933197 / 1000000000000) (-43991933196 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 4) <| besselDerivativeNearFromState (10264133085650931 / 64000000000000) 4 (IntervalRat.scale (2963 / 32) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-50896925950 / 1000000000000) (-50896925949 / 1000000000000), orderedInterval (-36976420159 / 1000000000000) (-36976420158 / 1000000000000)))) (orderedInterval (-5171389671 / 1000000000000) (-5171389581 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 4) <| besselDerivativeNearFromState (8557164077148739 / 64000000000000) 4 (IntervalRat.scale (2963 / 32) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (38866585152 / 1000000000000) (38866596368 / 1000000000000), orderedInterval (-57160710853 / 1000000000000) (-57160699636 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 4) <| besselDerivativeNearFromState (7560513974911519 / 64000000000000) 4 (IntervalRat.scale (2963 / 32) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-32797058184 / 1000000000000) (-32797055201 / 1000000000000), orderedInterval (65815209304 / 1000000000000) (65815212287 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 4) <| besselDerivativeNearFromState (2191331635116381 / 12800000000000) 4 (IntervalRat.scale (2963 / 32) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (43962569801 / 1000000000000) (43962633521 / 1000000000000), orderedInterval (-42388460616 / 1000000000000) (-42388396896 / 1000000000000)))) (orderedInterval (19715303474 / 1000000000000) (19715323839 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate209_chunkChecks4_2 :
    compactCertificate209.chunkChecks (4 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 4) <| besselDerivativeNearFromState (6061338626197607 / 64000000000000) 4 (IntervalRat.scale (2963 / 32) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (77666280212 / 1000000000000) (77666280213 / 1000000000000), orderedInterval (25853394465 / 1000000000000) (25853394466 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 4) <| besselDerivativeNearFromState (5138263880914927 / 64000000000000) 4 (IntervalRat.scale (2963 / 32) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-51171989577 / 1000000000000) (-51171972964 / 1000000000000), orderedInterval (73194876613 / 1000000000000) (73194893225 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 4) <| besselDerivativeNearFromState (3215286959434981 / 64000000000000) 4 (IntervalRat.scale (2963 / 32) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (77246025116 / 1000000000000) (77246025117 / 1000000000000), orderedInterval (81115034516 / 1000000000000) (81115034517 / 1000000000000)))) (orderedInterval (-11878334679 / 1000000000000) (-11878334114 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 4) <| besselDerivativeNearFromState (1729192020345627 / 64000000000000) 4 (IntervalRat.scale (2963 / 32) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (70186391335 / 1000000000000) (70186396675 / 1000000000000), orderedInterval (-137821188910 / 1000000000000) (-137821183569 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 4) <| besselDerivativeNearFromState (4695092710997881 / 64000000000000) 4 (IntervalRat.scale (2963 / 32) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-88510242876 / 1000000000000) (-88510241094 / 1000000000000), orderedInterval (29649744840 / 1000000000000) (29649746622 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 4) <| besselDerivativeNearFromState (6410747701045337 / 64000000000000) 4 (IntervalRat.scale (2963 / 32) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (32588469662 / 1000000000000) (32588469663 / 1000000000000), orderedInterval (72594252519 / 1000000000000) (72594252520 / 1000000000000)))) (orderedInterval (-2796100840 / 1000000000000) (-2796100811 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 4) <| besselDerivativeNearFromState (2710713040565019 / 64000000000000) 4 (IntervalRat.scale (2963 / 32) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-91694235258 / 1000000000000) (-91694150970 / 1000000000000), orderedInterval (82461970526 / 1000000000000) (82462054814 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 4) <| besselDerivativeNearFromState (11018898015608699 / 64000000000000) 4 (IntervalRat.scale (2963 / 32) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-10129231955 / 1000000000000) (-10129231954 / 1000000000000), orderedInterval (-59929156792 / 1000000000000) (-59929156791 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 4) <| besselDerivativeNearFromState (7360113213915541 / 64000000000000) 4 (IntervalRat.scale (2963 / 32) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (32553056643 / 1000000000000) (32553059353 / 1000000000000), orderedInterval (-67044966741 / 1000000000000) (-67044964032 / 1000000000000)))) (orderedInterval (-3500430318 / 1000000000000) (-3500428931 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate209_chunkChecks4 :
    compactCertificate209.chunkChecks (4 : Fin 5) 0 9 = true :=
  compactCertificate209.chunkChecks_nine_of_three (4 : Fin 5) compactCertificate209_chunkChecks4_0
    compactCertificate209_chunkChecks4_1 compactCertificate209_chunkChecks4_2

theorem compactCertificate209_chunks :
    ∀ r : Fin 5, ∀ b, compactCertificate209.chunkCheck r b = true :=
  compactCertificate209.chunkChecks_all (by
    intro r
    fin_cases r
    · exact compactCertificate209_chunkChecks0
    · exact compactCertificate209_chunkChecks1
    · exact compactCertificate209_chunkChecks2
    · exact compactCertificate209_chunkChecks3
    · exact compactCertificate209_chunkChecks4)

theorem compactCertificate209_coefficient0 :
    compactCertificate209.coefficientCheck (0 : Fin 5) = true := by
  norm_num [CompactCertificate.coefficientCheck, intervalFinSumHull,
    compactCertificate209, rationalIntervalSubset, orderedInterval, Fin.sum_univ_succ]

theorem compactCertificate209_coefficient1 :
    compactCertificate209.coefficientCheck (1 : Fin 5) = true := by
  norm_num [CompactCertificate.coefficientCheck, intervalFinSumHull,
    compactCertificate209, rationalIntervalSubset, orderedInterval, Fin.sum_univ_succ]

theorem compactCertificate209_coefficient2 :
    compactCertificate209.coefficientCheck (2 : Fin 5) = true := by
  norm_num [CompactCertificate.coefficientCheck, intervalFinSumHull,
    compactCertificate209, rationalIntervalSubset, orderedInterval, Fin.sum_univ_succ]

theorem compactCertificate209_coefficient3 :
    compactCertificate209.coefficientCheck (3 : Fin 5) = true := by
  norm_num [CompactCertificate.coefficientCheck, intervalFinSumHull,
    compactCertificate209, rationalIntervalSubset, orderedInterval, Fin.sum_univ_succ]

theorem compactCertificate209_coefficient4 :
    compactCertificate209.coefficientCheck (4 : Fin 5) = true := by
  norm_num [CompactCertificate.coefficientCheck, intervalFinSumHull,
    compactCertificate209, rationalIntervalSubset, orderedInterval, Fin.sum_univ_succ]

theorem compactCertificate209_coefficients : ∀ r : Fin 5,
    compactCertificate209.coefficientCheck r = true := by
  intro r
  fin_cases r
  · exact compactCertificate209_coefficient0
  · exact compactCertificate209_coefficient1
  · exact compactCertificate209_coefficient2
  · exact compactCertificate209_coefficient3
  · exact compactCertificate209_coefficient4

theorem compactCertificate209_lower : (1 : ℚ) ≤ compactCertificate209.output.lo := by
  norm_num [CompactCertificate.output, CompactCertificate.interval,
    CompactCertificate.coefficientTargetNat, compactCertificate209, dualConstant,
    intervalTaylorSum, intervalPow, intervalSub, intervalMaxAbs, widenInterval,
    rationalErrorInterval, orderedInterval, IntervalRat.add, IntervalRat.mul, IntervalRat.scale,
    IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4]

theorem compactCertificate209_proves {t : ℝ} (ht : t ∈ compactCertificate209.interval) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t :=
  compactCertificate209.proves compactCertificate209_states compactCertificate209_chunks
    compactCertificate209_coefficients compactCertificate209_lower ht

end Erdos232
