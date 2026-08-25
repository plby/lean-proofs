/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, OpenAI Codex
-/
import ErdosProblems.Erdos232.CompactBase

open LeanCert.Core
namespace Erdos232

def compactCertificate273 : CompactCertificate where
  left := 147
  right := 148
  center := 295 / 2
  grid := fun i =>
    match i.val with
    | 0 => 47
    | 1 => 35
    | 2 => 56
    | 3 => 10
    | 4 => 27
    | 5 => 74
    | 6 => 54
    | 7 => 93
    | 8 => 68
    | 9 => 105
    | 10 => 61
    | 11 => 108
    | 12 => 101
    | 13 => 72
    | 14 => 81
    | 15 => 68
    | 16 => 60
    | 17 => 87
    | 18 => 48
    | 19 => 41
    | 20 => 25
    | 21 => 14
    | 22 => 37
    | 23 => 51
    | 24 => 21
    | 25 => 87
    | _ => 58
  point := fun i =>
    match i.val with
    | 0 => 295 / 2
    | 1 => 86918265926159 / 800000000000
    | 2 => 28107581352047 / 160000000000
    | 3 => 25362533220013 / 800000000000
    | 4 => 68127331764361 / 800000000000
    | 5 => 184978958393637 / 800000000000
    | 6 => 136254663528781 / 800000000000
    | 7 => 233474688342913 / 800000000000
    | 8 => 171976398715267 / 800000000000
    | 9 => 263856021344941 / 800000000000
    | 10 => 152337344950789 / 800000000000
    | 11 => 270325291880201 / 800000000000
    | 12 => 252572953349069 / 800000000000
    | 13 => 180247977334877 / 800000000000
    | 14 => 204381995293083 / 800000000000
    | 15 => 170392399781227 / 800000000000
    | 16 => 150546852689767 / 800000000000
    | 17 => 43634345754933 / 160000000000
    | 18 => 120694896707951 / 800000000000
    | 19 => 102314400598711 / 800000000000
    | 20 => 64023601284733 / 800000000000
    | 21 => 34432105703811 / 800000000000
    | 22 => 93489864984433 / 800000000000
    | 23 => 127652417941841 / 800000000000
    | 24 => 53976398715267 / 800000000000
    | 25 => 219411064097507 / 800000000000
    | _ => 146556422416813 / 800000000000
  state := fun i =>
    match i.val with
    | 0 => (orderedInterval (-38688660328 / 1000000000000) (-38688660327 / 1000000000000), orderedInterval (-52965571040 / 1000000000000) (-52965571039 / 1000000000000))
    | 1 => (orderedInterval (38277655058 / 1000000000000) (38277661035 / 1000000000000), orderedInterval (-66465908933 / 1000000000000) (-66465902956 / 1000000000000))
    | 2 => (orderedInterval (30322368239 / 1000000000000) (30322368240 / 1000000000000), orderedInterval (51918165559 / 1000000000000) (51918165560 / 1000000000000))
    | 3 => (orderedInterval (124208274422 / 1000000000000) (124208274423 / 1000000000000), orderedInterval (66244222844 / 1000000000000) (66244222845 / 1000000000000))
    | 4 => (orderedInterval (-77827171712 / 1000000000000) (-77827171711 / 1000000000000), orderedInterval (-37206009790 / 1000000000000) (-37206009789 / 1000000000000))
    | 5 => (orderedInterval (-23730902828 / 1000000000000) (-23730901136 / 1000000000000), orderedInterval (46849943096 / 1000000000000) (46849944788 / 1000000000000))
    | 6 => (orderedInterval (60742112646 / 1000000000000) (60742112656 / 1000000000000), orderedInterval (6764525976 / 1000000000000) (6764525986 / 1000000000000))
    | 7 => (orderedInterval (-20743600445 / 1000000000000) (-20743600444 / 1000000000000), orderedInterval (-41810367175 / 1000000000000) (-41810367174 / 1000000000000))
    | 8 => (orderedInterval (46215685878 / 1000000000000) (46215726288 / 1000000000000), orderedInterval (-28839609900 / 1000000000000) (-28839569491 / 1000000000000))
    | 9 => (orderedInterval (-29553314675 / 1000000000000) (-29553314674 / 1000000000000), orderedInterval (-32463740030 / 1000000000000) (-32463740029 / 1000000000000))
    | 10 => (orderedInterval (24141941748 / 1000000000000) (24141943123 / 1000000000000), orderedInterval (-52602753965 / 1000000000000) (-52602752590 / 1000000000000))
    | 11 => (orderedInterval (-24521425570 / 1000000000000) (-24521421599 / 1000000000000), orderedInterval (35851244267 / 1000000000000) (35851248238 / 1000000000000))
    | 12 => (orderedInterval (32202100087 / 1000000000000) (32202131829 / 1000000000000), orderedInterval (-31347246278 / 1000000000000) (-31347214536 / 1000000000000))
    | 13 => (orderedInterval (-5299093190 / 1000000000000) (-5299093178 / 1000000000000), orderedInterval (52902732699 / 1000000000000) (52902732711 / 1000000000000))
    | 14 => (orderedInterval (-48687031516 / 1000000000000) (-48687029801 / 1000000000000), orderedInterval (11115754625 / 1000000000000) (11115756340 / 1000000000000))
    | 15 => (orderedInterval (8008339001 / 1000000000000) (8008339002 / 1000000000000), orderedInterval (54062924849 / 1000000000000) (54062924850 / 1000000000000))
    | 16 => (orderedInterval (26483342526 / 1000000000000) (26483342527 / 1000000000000), orderedInterval (51713915803 / 1000000000000) (51713915804 / 1000000000000))
    | 17 => (orderedInterval (-8699310546 / 1000000000000) (-8699310545 / 1000000000000), orderedInterval (-47509897366 / 1000000000000) (-47509897365 / 1000000000000))
    | 18 => (orderedInterval (49090412657 / 1000000000000) (49090412658 / 1000000000000), orderedInterval (42379340921 / 1000000000000) (42379340922 / 1000000000000))
    | 19 => (orderedInterval (8997543607 / 1000000000000) (8997543645 / 1000000000000), orderedInterval (-70012557897 / 1000000000000) (-70012557859 / 1000000000000))
    | 20 => (orderedInterval (-68058624132 / 1000000000000) (-68058543612 / 1000000000000), orderedInterval (58069030327 / 1000000000000) (58069110847 / 1000000000000))
    | 21 => (orderedInterval (-19335965219 / 1000000000000) (-19335965109 / 1000000000000), orderedInterval (120301128534 / 1000000000000) (120301128643 / 1000000000000))
    | 22 => (orderedInterval (-72828449385 / 1000000000000) (-72828449382 / 1000000000000), orderedInterval (-11670656820 / 1000000000000) (-11670656817 / 1000000000000))
    | 23 => (orderedInterval (-8120054152 / 1000000000000) (-8120054151 / 1000000000000), orderedInterval (-62614728616 / 1000000000000) (-62614728615 / 1000000000000))
    | 24 => (orderedInterval (-73676287801 / 1000000000000) (-73676206596 / 1000000000000), orderedInterval (63849146930 / 1000000000000) (63849228135 / 1000000000000))
    | 25 => (orderedInterval (-47567846060 / 1000000000000) (-47567845144 / 1000000000000), orderedInterval (7734671438 / 1000000000000) (7734672354 / 1000000000000))
    | _ => (orderedInterval (57808684288 / 1000000000000) (57808685117 / 1000000000000), orderedInterval (-11700204227 / 1000000000000) (-11700203398 / 1000000000000))
  chunkTarget := fun r b =>
    match r.val with
    | 0 =>
      match b.val with
      | 0 => orderedInterval (-13198805963 / 1000000000000) (-13198805896 / 1000000000000)
      | 1 => orderedInterval (-2502156406 / 1000000000000) (-2502156267 / 1000000000000)
      | 2 => orderedInterval (1756757572 / 1000000000000) (1756758558 / 1000000000000)
      | 3 => orderedInterval (3554121256 / 1000000000000) (3554121981 / 1000000000000)
      | 4 => orderedInterval (-836060889 / 1000000000000) (-836060288 / 1000000000000)
      | 5 => orderedInterval (-1645812752 / 1000000000000) (-1645812737 / 1000000000000)
      | 6 => orderedInterval (-10574113504 / 1000000000000) (-10574110843 / 1000000000000)
      | 7 => orderedInterval (2631601604 / 1000000000000) (2631601625 / 1000000000000)
      | _ => orderedInterval (-7418480546 / 1000000000000) (-7418479784 / 1000000000000)
    | 1 =>
      match b.val with
      | 0 => orderedInterval (-17821377718 / 1000000000000) (-17821377664 / 1000000000000)
      | 1 => orderedInterval (-6159805249 / 1000000000000) (-6159805040 / 1000000000000)
      | 2 => orderedInterval (1535777817 / 1000000000000) (1535779255 / 1000000000000)
      | 3 => orderedInterval (19542458983 / 1000000000000) (19542460529 / 1000000000000)
      | 4 => orderedInterval (8755527966 / 1000000000000) (8755529239 / 1000000000000)
      | 5 => orderedInterval (-5123284990 / 1000000000000) (-5123284969 / 1000000000000)
      | 6 => orderedInterval (-2469232214 / 1000000000000) (-2469230755 / 1000000000000)
      | 7 => orderedInterval (4752841004 / 1000000000000) (4752841021 / 1000000000000)
      | _ => orderedInterval (1731878608 / 1000000000000) (1731879222 / 1000000000000)
    | 2 =>
      match b.val with
      | 0 => orderedInterval (12738159647 / 1000000000000) (12738159692 / 1000000000000)
      | 1 => orderedInterval (-3094513836 / 1000000000000) (-3094513510 / 1000000000000)
      | 2 => orderedInterval (-4887688508 / 1000000000000) (-4887686397 / 1000000000000)
      | 3 => orderedInterval (-11075555228 / 1000000000000) (-11075551825 / 1000000000000)
      | 4 => orderedInterval (3034169255 / 1000000000000) (3034171966 / 1000000000000)
      | 5 => orderedInterval (3070220569 / 1000000000000) (3070220601 / 1000000000000)
      | 6 => orderedInterval (9263669114 / 1000000000000) (9263669930 / 1000000000000)
      | 7 => orderedInterval (-1828056950 / 1000000000000) (-1828056933 / 1000000000000)
      | _ => orderedInterval (3425091011 / 1000000000000) (3425091700 / 1000000000000)
    | 3 =>
      match b.val with
      | 0 => orderedInterval (16007061483 / 1000000000000) (16007061522 / 1000000000000)
      | 1 => orderedInterval (13119554633 / 1000000000000) (13119555141 / 1000000000000)
      | 2 => orderedInterval (-7798234937 / 1000000000000) (-7798231853 / 1000000000000)
      | 3 => orderedInterval (-117305891528 / 1000000000000) (-117305883929 / 1000000000000)
      | 4 => orderedInterval (-23108036535 / 1000000000000) (-23108030767 / 1000000000000)
      | 5 => orderedInterval (11933436813 / 1000000000000) (11933436861 / 1000000000000)
      | 6 => orderedInterval (4303020501 / 1000000000000) (4303020958 / 1000000000000)
      | 7 => orderedInterval (-6139162156 / 1000000000000) (-6139162139 / 1000000000000)
      | _ => orderedInterval (-218183057 / 1000000000000) (-218182098 / 1000000000000)
    | _ =>
      match b.val with
      | 0 => orderedInterval (-11866082812 / 1000000000000) (-11866082776 / 1000000000000)
      | 1 => orderedInterval (9691190891 / 1000000000000) (9691191689 / 1000000000000)
      | 2 => orderedInterval (14950771419 / 1000000000000) (14950775953 / 1000000000000)
      | 3 => orderedInterval (41827586358 / 1000000000000) (41827603552 / 1000000000000)
      | 4 => orderedInterval (-12399956960 / 1000000000000) (-12399944631 / 1000000000000)
      | 5 => orderedInterval (-6377901477 / 1000000000000) (-6377901401 / 1000000000000)
      | 6 => orderedInterval (-9128948645 / 1000000000000) (-9128948378 / 1000000000000)
      | 7 => orderedInterval (1589089949 / 1000000000000) (1589089967 / 1000000000000)
      | _ => orderedInterval (20460624347 / 1000000000000) (20460625851 / 1000000000000)
  coefficientTarget := fun i =>
    match i.val with
    | 0 => orderedInterval (-28232949628 / 1000000000000) (-28232943651 / 1000000000000)
    | 1 => orderedInterval (4744784207 / 1000000000000) (4744790838 / 1000000000000)
    | 2 => orderedInterval (10645495074 / 1000000000000) (10645505224 / 1000000000000)
    | 3 => orderedInterval (-109206434783 / 1000000000000) (-109206416304 / 1000000000000)
    | _ => orderedInterval (48746373070 / 1000000000000) (48746409826 / 1000000000000)

theorem compactCertificate273_stateChecks0 :
    compactCertificate273.stateChecks 0 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 47 12 (295 / 2)) (orderedInterval (-38688660328 / 1000000000000) (-38688660327 / 1000000000000), orderedInterval (-52965571040 / 1000000000000) (-52965571039 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 35 12 (86918265926159 / 800000000000)) (orderedInterval (38277655058 / 1000000000000) (38277661035 / 1000000000000), orderedInterval (-66465908933 / 1000000000000) (-66465902956 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 56 12 (28107581352047 / 160000000000)) (orderedInterval (30322368239 / 1000000000000) (30322368240 / 1000000000000), orderedInterval (51918165559 / 1000000000000) (51918165560 / 1000000000000))) = true
  norm_num [besselStateAtRationalPoint, besselIntervalStepZero,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, besselZeroTransition,
    besselInitial, besselGridStateAt, besselGridStateBlock00, besselGridStateBlock01,
    besselGridStateBlock02, besselGridStateBlock03, besselGridStateBlock04,
    besselGridStateBlock05, besselGridStateBlock06, besselGridStateBlock07,
    besselGridStateBlock08, besselGridStateBlock09, besselGridStateBlock10,
    besselGridStateBlock11, besselGridStateBlock12, besselGridStateBlock13,
    besselGridStateBlock14, besselGridState010, besselGridState014, besselGridState021, besselGridState025, besselGridState027, besselGridState035, besselGridState037, besselGridState041, besselGridState047, besselGridState048, besselGridState051, besselGridState054, besselGridState056, besselGridState058, besselGridState060, besselGridState061, besselGridState068, besselGridState072, besselGridState074, besselGridState081, besselGridState087, besselGridState093, besselGridState101, besselGridState105, besselGridState108, besselStateSubset, linearInterval, widenInterval,
    rationalErrorInterval, rationalIntervalSubset, orderedInterval, Finset.sum_range_succ,
    IntervalRat.add, IntervalRat.mul, IntervalRat.scale, IntervalRat.singleton]

theorem compactCertificate273_stateChecks1 :
    compactCertificate273.stateChecks 3 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 10 12 (25362533220013 / 800000000000)) (orderedInterval (124208274422 / 1000000000000) (124208274423 / 1000000000000), orderedInterval (66244222844 / 1000000000000) (66244222845 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 27 12 (68127331764361 / 800000000000)) (orderedInterval (-77827171712 / 1000000000000) (-77827171711 / 1000000000000), orderedInterval (-37206009790 / 1000000000000) (-37206009789 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 74 12 (184978958393637 / 800000000000)) (orderedInterval (-23730902828 / 1000000000000) (-23730901136 / 1000000000000), orderedInterval (46849943096 / 1000000000000) (46849944788 / 1000000000000))) = true
  norm_num [besselStateAtRationalPoint, besselIntervalStepZero,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, besselZeroTransition,
    besselInitial, besselGridStateAt, besselGridStateBlock00, besselGridStateBlock01,
    besselGridStateBlock02, besselGridStateBlock03, besselGridStateBlock04,
    besselGridStateBlock05, besselGridStateBlock06, besselGridStateBlock07,
    besselGridStateBlock08, besselGridStateBlock09, besselGridStateBlock10,
    besselGridStateBlock11, besselGridStateBlock12, besselGridStateBlock13,
    besselGridStateBlock14, besselGridState010, besselGridState014, besselGridState021, besselGridState025, besselGridState027, besselGridState035, besselGridState037, besselGridState041, besselGridState047, besselGridState048, besselGridState051, besselGridState054, besselGridState056, besselGridState058, besselGridState060, besselGridState061, besselGridState068, besselGridState072, besselGridState074, besselGridState081, besselGridState087, besselGridState093, besselGridState101, besselGridState105, besselGridState108, besselStateSubset, linearInterval, widenInterval,
    rationalErrorInterval, rationalIntervalSubset, orderedInterval, Finset.sum_range_succ,
    IntervalRat.add, IntervalRat.mul, IntervalRat.scale, IntervalRat.singleton]

theorem compactCertificate273_stateChecks2 :
    compactCertificate273.stateChecks 6 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 54 12 (136254663528781 / 800000000000)) (orderedInterval (60742112646 / 1000000000000) (60742112656 / 1000000000000), orderedInterval (6764525976 / 1000000000000) (6764525986 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 93 12 (233474688342913 / 800000000000)) (orderedInterval (-20743600445 / 1000000000000) (-20743600444 / 1000000000000), orderedInterval (-41810367175 / 1000000000000) (-41810367174 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 68 12 (171976398715267 / 800000000000)) (orderedInterval (46215685878 / 1000000000000) (46215726288 / 1000000000000), orderedInterval (-28839609900 / 1000000000000) (-28839569491 / 1000000000000))) = true
  norm_num [besselStateAtRationalPoint, besselIntervalStepZero,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, besselZeroTransition,
    besselInitial, besselGridStateAt, besselGridStateBlock00, besselGridStateBlock01,
    besselGridStateBlock02, besselGridStateBlock03, besselGridStateBlock04,
    besselGridStateBlock05, besselGridStateBlock06, besselGridStateBlock07,
    besselGridStateBlock08, besselGridStateBlock09, besselGridStateBlock10,
    besselGridStateBlock11, besselGridStateBlock12, besselGridStateBlock13,
    besselGridStateBlock14, besselGridState010, besselGridState014, besselGridState021, besselGridState025, besselGridState027, besselGridState035, besselGridState037, besselGridState041, besselGridState047, besselGridState048, besselGridState051, besselGridState054, besselGridState056, besselGridState058, besselGridState060, besselGridState061, besselGridState068, besselGridState072, besselGridState074, besselGridState081, besselGridState087, besselGridState093, besselGridState101, besselGridState105, besselGridState108, besselStateSubset, linearInterval, widenInterval,
    rationalErrorInterval, rationalIntervalSubset, orderedInterval, Finset.sum_range_succ,
    IntervalRat.add, IntervalRat.mul, IntervalRat.scale, IntervalRat.singleton]

theorem compactCertificate273_stateChecks3 :
    compactCertificate273.stateChecks 9 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 105 12 (263856021344941 / 800000000000)) (orderedInterval (-29553314675 / 1000000000000) (-29553314674 / 1000000000000), orderedInterval (-32463740030 / 1000000000000) (-32463740029 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 61 12 (152337344950789 / 800000000000)) (orderedInterval (24141941748 / 1000000000000) (24141943123 / 1000000000000), orderedInterval (-52602753965 / 1000000000000) (-52602752590 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 108 12 (270325291880201 / 800000000000)) (orderedInterval (-24521425570 / 1000000000000) (-24521421599 / 1000000000000), orderedInterval (35851244267 / 1000000000000) (35851248238 / 1000000000000))) = true
  norm_num [besselStateAtRationalPoint, besselIntervalStepZero,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, besselZeroTransition,
    besselInitial, besselGridStateAt, besselGridStateBlock00, besselGridStateBlock01,
    besselGridStateBlock02, besselGridStateBlock03, besselGridStateBlock04,
    besselGridStateBlock05, besselGridStateBlock06, besselGridStateBlock07,
    besselGridStateBlock08, besselGridStateBlock09, besselGridStateBlock10,
    besselGridStateBlock11, besselGridStateBlock12, besselGridStateBlock13,
    besselGridStateBlock14, besselGridState010, besselGridState014, besselGridState021, besselGridState025, besselGridState027, besselGridState035, besselGridState037, besselGridState041, besselGridState047, besselGridState048, besselGridState051, besselGridState054, besselGridState056, besselGridState058, besselGridState060, besselGridState061, besselGridState068, besselGridState072, besselGridState074, besselGridState081, besselGridState087, besselGridState093, besselGridState101, besselGridState105, besselGridState108, besselStateSubset, linearInterval, widenInterval,
    rationalErrorInterval, rationalIntervalSubset, orderedInterval, Finset.sum_range_succ,
    IntervalRat.add, IntervalRat.mul, IntervalRat.scale, IntervalRat.singleton]

theorem compactCertificate273_stateChecks4 :
    compactCertificate273.stateChecks 12 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 101 12 (252572953349069 / 800000000000)) (orderedInterval (32202100087 / 1000000000000) (32202131829 / 1000000000000), orderedInterval (-31347246278 / 1000000000000) (-31347214536 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 72 12 (180247977334877 / 800000000000)) (orderedInterval (-5299093190 / 1000000000000) (-5299093178 / 1000000000000), orderedInterval (52902732699 / 1000000000000) (52902732711 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 81 12 (204381995293083 / 800000000000)) (orderedInterval (-48687031516 / 1000000000000) (-48687029801 / 1000000000000), orderedInterval (11115754625 / 1000000000000) (11115756340 / 1000000000000))) = true
  norm_num [besselStateAtRationalPoint, besselIntervalStepZero,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, besselZeroTransition,
    besselInitial, besselGridStateAt, besselGridStateBlock00, besselGridStateBlock01,
    besselGridStateBlock02, besselGridStateBlock03, besselGridStateBlock04,
    besselGridStateBlock05, besselGridStateBlock06, besselGridStateBlock07,
    besselGridStateBlock08, besselGridStateBlock09, besselGridStateBlock10,
    besselGridStateBlock11, besselGridStateBlock12, besselGridStateBlock13,
    besselGridStateBlock14, besselGridState010, besselGridState014, besselGridState021, besselGridState025, besselGridState027, besselGridState035, besselGridState037, besselGridState041, besselGridState047, besselGridState048, besselGridState051, besselGridState054, besselGridState056, besselGridState058, besselGridState060, besselGridState061, besselGridState068, besselGridState072, besselGridState074, besselGridState081, besselGridState087, besselGridState093, besselGridState101, besselGridState105, besselGridState108, besselStateSubset, linearInterval, widenInterval,
    rationalErrorInterval, rationalIntervalSubset, orderedInterval, Finset.sum_range_succ,
    IntervalRat.add, IntervalRat.mul, IntervalRat.scale, IntervalRat.singleton]

theorem compactCertificate273_stateChecks5 :
    compactCertificate273.stateChecks 15 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 68 12 (170392399781227 / 800000000000)) (orderedInterval (8008339001 / 1000000000000) (8008339002 / 1000000000000), orderedInterval (54062924849 / 1000000000000) (54062924850 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 60 12 (150546852689767 / 800000000000)) (orderedInterval (26483342526 / 1000000000000) (26483342527 / 1000000000000), orderedInterval (51713915803 / 1000000000000) (51713915804 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 87 12 (43634345754933 / 160000000000)) (orderedInterval (-8699310546 / 1000000000000) (-8699310545 / 1000000000000), orderedInterval (-47509897366 / 1000000000000) (-47509897365 / 1000000000000))) = true
  norm_num [besselStateAtRationalPoint, besselIntervalStepZero,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, besselZeroTransition,
    besselInitial, besselGridStateAt, besselGridStateBlock00, besselGridStateBlock01,
    besselGridStateBlock02, besselGridStateBlock03, besselGridStateBlock04,
    besselGridStateBlock05, besselGridStateBlock06, besselGridStateBlock07,
    besselGridStateBlock08, besselGridStateBlock09, besselGridStateBlock10,
    besselGridStateBlock11, besselGridStateBlock12, besselGridStateBlock13,
    besselGridStateBlock14, besselGridState010, besselGridState014, besselGridState021, besselGridState025, besselGridState027, besselGridState035, besselGridState037, besselGridState041, besselGridState047, besselGridState048, besselGridState051, besselGridState054, besselGridState056, besselGridState058, besselGridState060, besselGridState061, besselGridState068, besselGridState072, besselGridState074, besselGridState081, besselGridState087, besselGridState093, besselGridState101, besselGridState105, besselGridState108, besselStateSubset, linearInterval, widenInterval,
    rationalErrorInterval, rationalIntervalSubset, orderedInterval, Finset.sum_range_succ,
    IntervalRat.add, IntervalRat.mul, IntervalRat.scale, IntervalRat.singleton]

theorem compactCertificate273_stateChecks6 :
    compactCertificate273.stateChecks 18 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 48 12 (120694896707951 / 800000000000)) (orderedInterval (49090412657 / 1000000000000) (49090412658 / 1000000000000), orderedInterval (42379340921 / 1000000000000) (42379340922 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 41 12 (102314400598711 / 800000000000)) (orderedInterval (8997543607 / 1000000000000) (8997543645 / 1000000000000), orderedInterval (-70012557897 / 1000000000000) (-70012557859 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 25 12 (64023601284733 / 800000000000)) (orderedInterval (-68058624132 / 1000000000000) (-68058543612 / 1000000000000), orderedInterval (58069030327 / 1000000000000) (58069110847 / 1000000000000))) = true
  norm_num [besselStateAtRationalPoint, besselIntervalStepZero,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, besselZeroTransition,
    besselInitial, besselGridStateAt, besselGridStateBlock00, besselGridStateBlock01,
    besselGridStateBlock02, besselGridStateBlock03, besselGridStateBlock04,
    besselGridStateBlock05, besselGridStateBlock06, besselGridStateBlock07,
    besselGridStateBlock08, besselGridStateBlock09, besselGridStateBlock10,
    besselGridStateBlock11, besselGridStateBlock12, besselGridStateBlock13,
    besselGridStateBlock14, besselGridState010, besselGridState014, besselGridState021, besselGridState025, besselGridState027, besselGridState035, besselGridState037, besselGridState041, besselGridState047, besselGridState048, besselGridState051, besselGridState054, besselGridState056, besselGridState058, besselGridState060, besselGridState061, besselGridState068, besselGridState072, besselGridState074, besselGridState081, besselGridState087, besselGridState093, besselGridState101, besselGridState105, besselGridState108, besselStateSubset, linearInterval, widenInterval,
    rationalErrorInterval, rationalIntervalSubset, orderedInterval, Finset.sum_range_succ,
    IntervalRat.add, IntervalRat.mul, IntervalRat.scale, IntervalRat.singleton]

theorem compactCertificate273_stateChecks7 :
    compactCertificate273.stateChecks 21 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 14 12 (34432105703811 / 800000000000)) (orderedInterval (-19335965219 / 1000000000000) (-19335965109 / 1000000000000), orderedInterval (120301128534 / 1000000000000) (120301128643 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 37 12 (93489864984433 / 800000000000)) (orderedInterval (-72828449385 / 1000000000000) (-72828449382 / 1000000000000), orderedInterval (-11670656820 / 1000000000000) (-11670656817 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 51 12 (127652417941841 / 800000000000)) (orderedInterval (-8120054152 / 1000000000000) (-8120054151 / 1000000000000), orderedInterval (-62614728616 / 1000000000000) (-62614728615 / 1000000000000))) = true
  norm_num [besselStateAtRationalPoint, besselIntervalStepZero,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, besselZeroTransition,
    besselInitial, besselGridStateAt, besselGridStateBlock00, besselGridStateBlock01,
    besselGridStateBlock02, besselGridStateBlock03, besselGridStateBlock04,
    besselGridStateBlock05, besselGridStateBlock06, besselGridStateBlock07,
    besselGridStateBlock08, besselGridStateBlock09, besselGridStateBlock10,
    besselGridStateBlock11, besselGridStateBlock12, besselGridStateBlock13,
    besselGridStateBlock14, besselGridState010, besselGridState014, besselGridState021, besselGridState025, besselGridState027, besselGridState035, besselGridState037, besselGridState041, besselGridState047, besselGridState048, besselGridState051, besselGridState054, besselGridState056, besselGridState058, besselGridState060, besselGridState061, besselGridState068, besselGridState072, besselGridState074, besselGridState081, besselGridState087, besselGridState093, besselGridState101, besselGridState105, besselGridState108, besselStateSubset, linearInterval, widenInterval,
    rationalErrorInterval, rationalIntervalSubset, orderedInterval, Finset.sum_range_succ,
    IntervalRat.add, IntervalRat.mul, IntervalRat.scale, IntervalRat.singleton]

theorem compactCertificate273_stateChecks8 :
    compactCertificate273.stateChecks 24 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 21 12 (53976398715267 / 800000000000)) (orderedInterval (-73676287801 / 1000000000000) (-73676206596 / 1000000000000), orderedInterval (63849146930 / 1000000000000) (63849228135 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 87 12 (219411064097507 / 800000000000)) (orderedInterval (-47567846060 / 1000000000000) (-47567845144 / 1000000000000), orderedInterval (7734671438 / 1000000000000) (7734672354 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 58 12 (146556422416813 / 800000000000)) (orderedInterval (57808684288 / 1000000000000) (57808685117 / 1000000000000), orderedInterval (-11700204227 / 1000000000000) (-11700203398 / 1000000000000))) = true
  norm_num [besselStateAtRationalPoint, besselIntervalStepZero,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, besselZeroTransition,
    besselInitial, besselGridStateAt, besselGridStateBlock00, besselGridStateBlock01,
    besselGridStateBlock02, besselGridStateBlock03, besselGridStateBlock04,
    besselGridStateBlock05, besselGridStateBlock06, besselGridStateBlock07,
    besselGridStateBlock08, besselGridStateBlock09, besselGridStateBlock10,
    besselGridStateBlock11, besselGridStateBlock12, besselGridStateBlock13,
    besselGridStateBlock14, besselGridState010, besselGridState014, besselGridState021, besselGridState025, besselGridState027, besselGridState035, besselGridState037, besselGridState041, besselGridState047, besselGridState048, besselGridState051, besselGridState054, besselGridState056, besselGridState058, besselGridState060, besselGridState061, besselGridState068, besselGridState072, besselGridState074, besselGridState081, besselGridState087, besselGridState093, besselGridState101, besselGridState105, besselGridState108, besselStateSubset, linearInterval, widenInterval,
    rationalErrorInterval, rationalIntervalSubset, orderedInterval, Finset.sum_range_succ,
    IntervalRat.add, IntervalRat.mul, IntervalRat.scale, IntervalRat.singleton]

theorem compactCertificate273_states : ∀ j,
    BesselStateValid (compactCertificate273.point j) (compactCertificate273.state j) :=
  compactCertificate273.statesValid_of_checks3 compactCertificate273_stateChecks0
    compactCertificate273_stateChecks1 compactCertificate273_stateChecks2
    compactCertificate273_stateChecks3 compactCertificate273_stateChecks4
    compactCertificate273_stateChecks5 compactCertificate273_stateChecks6
    compactCertificate273_stateChecks7 compactCertificate273_stateChecks8

theorem compactCertificate273_chunkChecks0_0 :
    compactCertificate273.chunkChecks (0 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 0) <| besselDerivativeNearFromState (295 / 2) 0 (IntervalRat.scale (295 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-38688660328 / 1000000000000) (-38688660327 / 1000000000000), orderedInterval (-52965571040 / 1000000000000) (-52965571039 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 0) <| besselDerivativeNearFromState (86918265926159 / 800000000000) 0 (IntervalRat.scale (295 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (38277655058 / 1000000000000) (38277661035 / 1000000000000), orderedInterval (-66465908933 / 1000000000000) (-66465902956 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 0) <| besselDerivativeNearFromState (28107581352047 / 160000000000) 0 (IntervalRat.scale (295 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (30322368239 / 1000000000000) (30322368240 / 1000000000000), orderedInterval (51918165559 / 1000000000000) (51918165560 / 1000000000000)))) (orderedInterval (-13198805963 / 1000000000000) (-13198805896 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 0) <| besselDerivativeNearFromState (25362533220013 / 800000000000) 0 (IntervalRat.scale (295 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (124208274422 / 1000000000000) (124208274423 / 1000000000000), orderedInterval (66244222844 / 1000000000000) (66244222845 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 0) <| besselDerivativeNearFromState (68127331764361 / 800000000000) 0 (IntervalRat.scale (295 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-77827171712 / 1000000000000) (-77827171711 / 1000000000000), orderedInterval (-37206009790 / 1000000000000) (-37206009789 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 0) <| besselDerivativeNearFromState (184978958393637 / 800000000000) 0 (IntervalRat.scale (295 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-23730902828 / 1000000000000) (-23730901136 / 1000000000000), orderedInterval (46849943096 / 1000000000000) (46849944788 / 1000000000000)))) (orderedInterval (-2502156406 / 1000000000000) (-2502156267 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 0) <| besselDerivativeNearFromState (136254663528781 / 800000000000) 0 (IntervalRat.scale (295 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (60742112646 / 1000000000000) (60742112656 / 1000000000000), orderedInterval (6764525976 / 1000000000000) (6764525986 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 0) <| besselDerivativeNearFromState (233474688342913 / 800000000000) 0 (IntervalRat.scale (295 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-20743600445 / 1000000000000) (-20743600444 / 1000000000000), orderedInterval (-41810367175 / 1000000000000) (-41810367174 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 0) <| besselDerivativeNearFromState (171976398715267 / 800000000000) 0 (IntervalRat.scale (295 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (46215685878 / 1000000000000) (46215726288 / 1000000000000), orderedInterval (-28839609900 / 1000000000000) (-28839569491 / 1000000000000)))) (orderedInterval (1756757572 / 1000000000000) (1756758558 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate273_chunkChecks0_1 :
    compactCertificate273.chunkChecks (0 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 0) <| besselDerivativeNearFromState (263856021344941 / 800000000000) 0 (IntervalRat.scale (295 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-29553314675 / 1000000000000) (-29553314674 / 1000000000000), orderedInterval (-32463740030 / 1000000000000) (-32463740029 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 0) <| besselDerivativeNearFromState (152337344950789 / 800000000000) 0 (IntervalRat.scale (295 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (24141941748 / 1000000000000) (24141943123 / 1000000000000), orderedInterval (-52602753965 / 1000000000000) (-52602752590 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 0) <| besselDerivativeNearFromState (270325291880201 / 800000000000) 0 (IntervalRat.scale (295 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-24521425570 / 1000000000000) (-24521421599 / 1000000000000), orderedInterval (35851244267 / 1000000000000) (35851248238 / 1000000000000)))) (orderedInterval (3554121256 / 1000000000000) (3554121981 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 0) <| besselDerivativeNearFromState (252572953349069 / 800000000000) 0 (IntervalRat.scale (295 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (32202100087 / 1000000000000) (32202131829 / 1000000000000), orderedInterval (-31347246278 / 1000000000000) (-31347214536 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 0) <| besselDerivativeNearFromState (180247977334877 / 800000000000) 0 (IntervalRat.scale (295 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-5299093190 / 1000000000000) (-5299093178 / 1000000000000), orderedInterval (52902732699 / 1000000000000) (52902732711 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 0) <| besselDerivativeNearFromState (204381995293083 / 800000000000) 0 (IntervalRat.scale (295 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-48687031516 / 1000000000000) (-48687029801 / 1000000000000), orderedInterval (11115754625 / 1000000000000) (11115756340 / 1000000000000)))) (orderedInterval (-836060889 / 1000000000000) (-836060288 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 0) <| besselDerivativeNearFromState (170392399781227 / 800000000000) 0 (IntervalRat.scale (295 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (8008339001 / 1000000000000) (8008339002 / 1000000000000), orderedInterval (54062924849 / 1000000000000) (54062924850 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 0) <| besselDerivativeNearFromState (150546852689767 / 800000000000) 0 (IntervalRat.scale (295 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (26483342526 / 1000000000000) (26483342527 / 1000000000000), orderedInterval (51713915803 / 1000000000000) (51713915804 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 0) <| besselDerivativeNearFromState (43634345754933 / 160000000000) 0 (IntervalRat.scale (295 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-8699310546 / 1000000000000) (-8699310545 / 1000000000000), orderedInterval (-47509897366 / 1000000000000) (-47509897365 / 1000000000000)))) (orderedInterval (-1645812752 / 1000000000000) (-1645812737 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate273_chunkChecks0_2 :
    compactCertificate273.chunkChecks (0 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 0) <| besselDerivativeNearFromState (120694896707951 / 800000000000) 0 (IntervalRat.scale (295 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (49090412657 / 1000000000000) (49090412658 / 1000000000000), orderedInterval (42379340921 / 1000000000000) (42379340922 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 0) <| besselDerivativeNearFromState (102314400598711 / 800000000000) 0 (IntervalRat.scale (295 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (8997543607 / 1000000000000) (8997543645 / 1000000000000), orderedInterval (-70012557897 / 1000000000000) (-70012557859 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 0) <| besselDerivativeNearFromState (64023601284733 / 800000000000) 0 (IntervalRat.scale (295 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-68058624132 / 1000000000000) (-68058543612 / 1000000000000), orderedInterval (58069030327 / 1000000000000) (58069110847 / 1000000000000)))) (orderedInterval (-10574113504 / 1000000000000) (-10574110843 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 0) <| besselDerivativeNearFromState (34432105703811 / 800000000000) 0 (IntervalRat.scale (295 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-19335965219 / 1000000000000) (-19335965109 / 1000000000000), orderedInterval (120301128534 / 1000000000000) (120301128643 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 0) <| besselDerivativeNearFromState (93489864984433 / 800000000000) 0 (IntervalRat.scale (295 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-72828449385 / 1000000000000) (-72828449382 / 1000000000000), orderedInterval (-11670656820 / 1000000000000) (-11670656817 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 0) <| besselDerivativeNearFromState (127652417941841 / 800000000000) 0 (IntervalRat.scale (295 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-8120054152 / 1000000000000) (-8120054151 / 1000000000000), orderedInterval (-62614728616 / 1000000000000) (-62614728615 / 1000000000000)))) (orderedInterval (2631601604 / 1000000000000) (2631601625 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 0) <| besselDerivativeNearFromState (53976398715267 / 800000000000) 0 (IntervalRat.scale (295 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-73676287801 / 1000000000000) (-73676206596 / 1000000000000), orderedInterval (63849146930 / 1000000000000) (63849228135 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 0) <| besselDerivativeNearFromState (219411064097507 / 800000000000) 0 (IntervalRat.scale (295 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-47567846060 / 1000000000000) (-47567845144 / 1000000000000), orderedInterval (7734671438 / 1000000000000) (7734672354 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 0) <| besselDerivativeNearFromState (146556422416813 / 800000000000) 0 (IntervalRat.scale (295 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (57808684288 / 1000000000000) (57808685117 / 1000000000000), orderedInterval (-11700204227 / 1000000000000) (-11700203398 / 1000000000000)))) (orderedInterval (-7418480546 / 1000000000000) (-7418479784 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate273_chunkChecks0 :
    compactCertificate273.chunkChecks (0 : Fin 5) 0 9 = true :=
  compactCertificate273.chunkChecks_nine_of_three (0 : Fin 5) compactCertificate273_chunkChecks0_0
    compactCertificate273_chunkChecks0_1 compactCertificate273_chunkChecks0_2

theorem compactCertificate273_chunkChecks1_0 :
    compactCertificate273.chunkChecks (1 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 1) <| besselDerivativeNearFromState (295 / 2) 1 (IntervalRat.scale (295 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-38688660328 / 1000000000000) (-38688660327 / 1000000000000), orderedInterval (-52965571040 / 1000000000000) (-52965571039 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 1) <| besselDerivativeNearFromState (86918265926159 / 800000000000) 1 (IntervalRat.scale (295 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (38277655058 / 1000000000000) (38277661035 / 1000000000000), orderedInterval (-66465908933 / 1000000000000) (-66465902956 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 1) <| besselDerivativeNearFromState (28107581352047 / 160000000000) 1 (IntervalRat.scale (295 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (30322368239 / 1000000000000) (30322368240 / 1000000000000), orderedInterval (51918165559 / 1000000000000) (51918165560 / 1000000000000)))) (orderedInterval (-17821377718 / 1000000000000) (-17821377664 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 1) <| besselDerivativeNearFromState (25362533220013 / 800000000000) 1 (IntervalRat.scale (295 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (124208274422 / 1000000000000) (124208274423 / 1000000000000), orderedInterval (66244222844 / 1000000000000) (66244222845 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 1) <| besselDerivativeNearFromState (68127331764361 / 800000000000) 1 (IntervalRat.scale (295 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-77827171712 / 1000000000000) (-77827171711 / 1000000000000), orderedInterval (-37206009790 / 1000000000000) (-37206009789 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 1) <| besselDerivativeNearFromState (184978958393637 / 800000000000) 1 (IntervalRat.scale (295 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-23730902828 / 1000000000000) (-23730901136 / 1000000000000), orderedInterval (46849943096 / 1000000000000) (46849944788 / 1000000000000)))) (orderedInterval (-6159805249 / 1000000000000) (-6159805040 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 1) <| besselDerivativeNearFromState (136254663528781 / 800000000000) 1 (IntervalRat.scale (295 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (60742112646 / 1000000000000) (60742112656 / 1000000000000), orderedInterval (6764525976 / 1000000000000) (6764525986 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 1) <| besselDerivativeNearFromState (233474688342913 / 800000000000) 1 (IntervalRat.scale (295 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-20743600445 / 1000000000000) (-20743600444 / 1000000000000), orderedInterval (-41810367175 / 1000000000000) (-41810367174 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 1) <| besselDerivativeNearFromState (171976398715267 / 800000000000) 1 (IntervalRat.scale (295 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (46215685878 / 1000000000000) (46215726288 / 1000000000000), orderedInterval (-28839609900 / 1000000000000) (-28839569491 / 1000000000000)))) (orderedInterval (1535777817 / 1000000000000) (1535779255 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate273_chunkChecks1_1 :
    compactCertificate273.chunkChecks (1 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 1) <| besselDerivativeNearFromState (263856021344941 / 800000000000) 1 (IntervalRat.scale (295 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-29553314675 / 1000000000000) (-29553314674 / 1000000000000), orderedInterval (-32463740030 / 1000000000000) (-32463740029 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 1) <| besselDerivativeNearFromState (152337344950789 / 800000000000) 1 (IntervalRat.scale (295 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (24141941748 / 1000000000000) (24141943123 / 1000000000000), orderedInterval (-52602753965 / 1000000000000) (-52602752590 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 1) <| besselDerivativeNearFromState (270325291880201 / 800000000000) 1 (IntervalRat.scale (295 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-24521425570 / 1000000000000) (-24521421599 / 1000000000000), orderedInterval (35851244267 / 1000000000000) (35851248238 / 1000000000000)))) (orderedInterval (19542458983 / 1000000000000) (19542460529 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 1) <| besselDerivativeNearFromState (252572953349069 / 800000000000) 1 (IntervalRat.scale (295 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (32202100087 / 1000000000000) (32202131829 / 1000000000000), orderedInterval (-31347246278 / 1000000000000) (-31347214536 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 1) <| besselDerivativeNearFromState (180247977334877 / 800000000000) 1 (IntervalRat.scale (295 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-5299093190 / 1000000000000) (-5299093178 / 1000000000000), orderedInterval (52902732699 / 1000000000000) (52902732711 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 1) <| besselDerivativeNearFromState (204381995293083 / 800000000000) 1 (IntervalRat.scale (295 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-48687031516 / 1000000000000) (-48687029801 / 1000000000000), orderedInterval (11115754625 / 1000000000000) (11115756340 / 1000000000000)))) (orderedInterval (8755527966 / 1000000000000) (8755529239 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 1) <| besselDerivativeNearFromState (170392399781227 / 800000000000) 1 (IntervalRat.scale (295 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (8008339001 / 1000000000000) (8008339002 / 1000000000000), orderedInterval (54062924849 / 1000000000000) (54062924850 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 1) <| besselDerivativeNearFromState (150546852689767 / 800000000000) 1 (IntervalRat.scale (295 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (26483342526 / 1000000000000) (26483342527 / 1000000000000), orderedInterval (51713915803 / 1000000000000) (51713915804 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 1) <| besselDerivativeNearFromState (43634345754933 / 160000000000) 1 (IntervalRat.scale (295 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-8699310546 / 1000000000000) (-8699310545 / 1000000000000), orderedInterval (-47509897366 / 1000000000000) (-47509897365 / 1000000000000)))) (orderedInterval (-5123284990 / 1000000000000) (-5123284969 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate273_chunkChecks1_2 :
    compactCertificate273.chunkChecks (1 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 1) <| besselDerivativeNearFromState (120694896707951 / 800000000000) 1 (IntervalRat.scale (295 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (49090412657 / 1000000000000) (49090412658 / 1000000000000), orderedInterval (42379340921 / 1000000000000) (42379340922 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 1) <| besselDerivativeNearFromState (102314400598711 / 800000000000) 1 (IntervalRat.scale (295 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (8997543607 / 1000000000000) (8997543645 / 1000000000000), orderedInterval (-70012557897 / 1000000000000) (-70012557859 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 1) <| besselDerivativeNearFromState (64023601284733 / 800000000000) 1 (IntervalRat.scale (295 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-68058624132 / 1000000000000) (-68058543612 / 1000000000000), orderedInterval (58069030327 / 1000000000000) (58069110847 / 1000000000000)))) (orderedInterval (-2469232214 / 1000000000000) (-2469230755 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 1) <| besselDerivativeNearFromState (34432105703811 / 800000000000) 1 (IntervalRat.scale (295 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-19335965219 / 1000000000000) (-19335965109 / 1000000000000), orderedInterval (120301128534 / 1000000000000) (120301128643 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 1) <| besselDerivativeNearFromState (93489864984433 / 800000000000) 1 (IntervalRat.scale (295 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-72828449385 / 1000000000000) (-72828449382 / 1000000000000), orderedInterval (-11670656820 / 1000000000000) (-11670656817 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 1) <| besselDerivativeNearFromState (127652417941841 / 800000000000) 1 (IntervalRat.scale (295 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-8120054152 / 1000000000000) (-8120054151 / 1000000000000), orderedInterval (-62614728616 / 1000000000000) (-62614728615 / 1000000000000)))) (orderedInterval (4752841004 / 1000000000000) (4752841021 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 1) <| besselDerivativeNearFromState (53976398715267 / 800000000000) 1 (IntervalRat.scale (295 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-73676287801 / 1000000000000) (-73676206596 / 1000000000000), orderedInterval (63849146930 / 1000000000000) (63849228135 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 1) <| besselDerivativeNearFromState (219411064097507 / 800000000000) 1 (IntervalRat.scale (295 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-47567846060 / 1000000000000) (-47567845144 / 1000000000000), orderedInterval (7734671438 / 1000000000000) (7734672354 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 1) <| besselDerivativeNearFromState (146556422416813 / 800000000000) 1 (IntervalRat.scale (295 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (57808684288 / 1000000000000) (57808685117 / 1000000000000), orderedInterval (-11700204227 / 1000000000000) (-11700203398 / 1000000000000)))) (orderedInterval (1731878608 / 1000000000000) (1731879222 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate273_chunkChecks1 :
    compactCertificate273.chunkChecks (1 : Fin 5) 0 9 = true :=
  compactCertificate273.chunkChecks_nine_of_three (1 : Fin 5) compactCertificate273_chunkChecks1_0
    compactCertificate273_chunkChecks1_1 compactCertificate273_chunkChecks1_2

theorem compactCertificate273_chunkChecks2_0 :
    compactCertificate273.chunkChecks (2 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 2) <| besselDerivativeNearFromState (295 / 2) 2 (IntervalRat.scale (295 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-38688660328 / 1000000000000) (-38688660327 / 1000000000000), orderedInterval (-52965571040 / 1000000000000) (-52965571039 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 2) <| besselDerivativeNearFromState (86918265926159 / 800000000000) 2 (IntervalRat.scale (295 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (38277655058 / 1000000000000) (38277661035 / 1000000000000), orderedInterval (-66465908933 / 1000000000000) (-66465902956 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 2) <| besselDerivativeNearFromState (28107581352047 / 160000000000) 2 (IntervalRat.scale (295 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (30322368239 / 1000000000000) (30322368240 / 1000000000000), orderedInterval (51918165559 / 1000000000000) (51918165560 / 1000000000000)))) (orderedInterval (12738159647 / 1000000000000) (12738159692 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 2) <| besselDerivativeNearFromState (25362533220013 / 800000000000) 2 (IntervalRat.scale (295 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (124208274422 / 1000000000000) (124208274423 / 1000000000000), orderedInterval (66244222844 / 1000000000000) (66244222845 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 2) <| besselDerivativeNearFromState (68127331764361 / 800000000000) 2 (IntervalRat.scale (295 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-77827171712 / 1000000000000) (-77827171711 / 1000000000000), orderedInterval (-37206009790 / 1000000000000) (-37206009789 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 2) <| besselDerivativeNearFromState (184978958393637 / 800000000000) 2 (IntervalRat.scale (295 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-23730902828 / 1000000000000) (-23730901136 / 1000000000000), orderedInterval (46849943096 / 1000000000000) (46849944788 / 1000000000000)))) (orderedInterval (-3094513836 / 1000000000000) (-3094513510 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 2) <| besselDerivativeNearFromState (136254663528781 / 800000000000) 2 (IntervalRat.scale (295 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (60742112646 / 1000000000000) (60742112656 / 1000000000000), orderedInterval (6764525976 / 1000000000000) (6764525986 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 2) <| besselDerivativeNearFromState (233474688342913 / 800000000000) 2 (IntervalRat.scale (295 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-20743600445 / 1000000000000) (-20743600444 / 1000000000000), orderedInterval (-41810367175 / 1000000000000) (-41810367174 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 2) <| besselDerivativeNearFromState (171976398715267 / 800000000000) 2 (IntervalRat.scale (295 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (46215685878 / 1000000000000) (46215726288 / 1000000000000), orderedInterval (-28839609900 / 1000000000000) (-28839569491 / 1000000000000)))) (orderedInterval (-4887688508 / 1000000000000) (-4887686397 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate273_chunkChecks2_1 :
    compactCertificate273.chunkChecks (2 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 2) <| besselDerivativeNearFromState (263856021344941 / 800000000000) 2 (IntervalRat.scale (295 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-29553314675 / 1000000000000) (-29553314674 / 1000000000000), orderedInterval (-32463740030 / 1000000000000) (-32463740029 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 2) <| besselDerivativeNearFromState (152337344950789 / 800000000000) 2 (IntervalRat.scale (295 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (24141941748 / 1000000000000) (24141943123 / 1000000000000), orderedInterval (-52602753965 / 1000000000000) (-52602752590 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 2) <| besselDerivativeNearFromState (270325291880201 / 800000000000) 2 (IntervalRat.scale (295 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-24521425570 / 1000000000000) (-24521421599 / 1000000000000), orderedInterval (35851244267 / 1000000000000) (35851248238 / 1000000000000)))) (orderedInterval (-11075555228 / 1000000000000) (-11075551825 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 2) <| besselDerivativeNearFromState (252572953349069 / 800000000000) 2 (IntervalRat.scale (295 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (32202100087 / 1000000000000) (32202131829 / 1000000000000), orderedInterval (-31347246278 / 1000000000000) (-31347214536 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 2) <| besselDerivativeNearFromState (180247977334877 / 800000000000) 2 (IntervalRat.scale (295 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-5299093190 / 1000000000000) (-5299093178 / 1000000000000), orderedInterval (52902732699 / 1000000000000) (52902732711 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 2) <| besselDerivativeNearFromState (204381995293083 / 800000000000) 2 (IntervalRat.scale (295 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-48687031516 / 1000000000000) (-48687029801 / 1000000000000), orderedInterval (11115754625 / 1000000000000) (11115756340 / 1000000000000)))) (orderedInterval (3034169255 / 1000000000000) (3034171966 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 2) <| besselDerivativeNearFromState (170392399781227 / 800000000000) 2 (IntervalRat.scale (295 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (8008339001 / 1000000000000) (8008339002 / 1000000000000), orderedInterval (54062924849 / 1000000000000) (54062924850 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 2) <| besselDerivativeNearFromState (150546852689767 / 800000000000) 2 (IntervalRat.scale (295 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (26483342526 / 1000000000000) (26483342527 / 1000000000000), orderedInterval (51713915803 / 1000000000000) (51713915804 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 2) <| besselDerivativeNearFromState (43634345754933 / 160000000000) 2 (IntervalRat.scale (295 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-8699310546 / 1000000000000) (-8699310545 / 1000000000000), orderedInterval (-47509897366 / 1000000000000) (-47509897365 / 1000000000000)))) (orderedInterval (3070220569 / 1000000000000) (3070220601 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate273_chunkChecks2_2 :
    compactCertificate273.chunkChecks (2 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 2) <| besselDerivativeNearFromState (120694896707951 / 800000000000) 2 (IntervalRat.scale (295 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (49090412657 / 1000000000000) (49090412658 / 1000000000000), orderedInterval (42379340921 / 1000000000000) (42379340922 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 2) <| besselDerivativeNearFromState (102314400598711 / 800000000000) 2 (IntervalRat.scale (295 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (8997543607 / 1000000000000) (8997543645 / 1000000000000), orderedInterval (-70012557897 / 1000000000000) (-70012557859 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 2) <| besselDerivativeNearFromState (64023601284733 / 800000000000) 2 (IntervalRat.scale (295 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-68058624132 / 1000000000000) (-68058543612 / 1000000000000), orderedInterval (58069030327 / 1000000000000) (58069110847 / 1000000000000)))) (orderedInterval (9263669114 / 1000000000000) (9263669930 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 2) <| besselDerivativeNearFromState (34432105703811 / 800000000000) 2 (IntervalRat.scale (295 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-19335965219 / 1000000000000) (-19335965109 / 1000000000000), orderedInterval (120301128534 / 1000000000000) (120301128643 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 2) <| besselDerivativeNearFromState (93489864984433 / 800000000000) 2 (IntervalRat.scale (295 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-72828449385 / 1000000000000) (-72828449382 / 1000000000000), orderedInterval (-11670656820 / 1000000000000) (-11670656817 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 2) <| besselDerivativeNearFromState (127652417941841 / 800000000000) 2 (IntervalRat.scale (295 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-8120054152 / 1000000000000) (-8120054151 / 1000000000000), orderedInterval (-62614728616 / 1000000000000) (-62614728615 / 1000000000000)))) (orderedInterval (-1828056950 / 1000000000000) (-1828056933 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 2) <| besselDerivativeNearFromState (53976398715267 / 800000000000) 2 (IntervalRat.scale (295 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-73676287801 / 1000000000000) (-73676206596 / 1000000000000), orderedInterval (63849146930 / 1000000000000) (63849228135 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 2) <| besselDerivativeNearFromState (219411064097507 / 800000000000) 2 (IntervalRat.scale (295 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-47567846060 / 1000000000000) (-47567845144 / 1000000000000), orderedInterval (7734671438 / 1000000000000) (7734672354 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 2) <| besselDerivativeNearFromState (146556422416813 / 800000000000) 2 (IntervalRat.scale (295 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (57808684288 / 1000000000000) (57808685117 / 1000000000000), orderedInterval (-11700204227 / 1000000000000) (-11700203398 / 1000000000000)))) (orderedInterval (3425091011 / 1000000000000) (3425091700 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate273_chunkChecks2 :
    compactCertificate273.chunkChecks (2 : Fin 5) 0 9 = true :=
  compactCertificate273.chunkChecks_nine_of_three (2 : Fin 5) compactCertificate273_chunkChecks2_0
    compactCertificate273_chunkChecks2_1 compactCertificate273_chunkChecks2_2

theorem compactCertificate273_chunkChecks3_0 :
    compactCertificate273.chunkChecks (3 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 3) <| besselDerivativeNearFromState (295 / 2) 3 (IntervalRat.scale (295 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-38688660328 / 1000000000000) (-38688660327 / 1000000000000), orderedInterval (-52965571040 / 1000000000000) (-52965571039 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 3) <| besselDerivativeNearFromState (86918265926159 / 800000000000) 3 (IntervalRat.scale (295 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (38277655058 / 1000000000000) (38277661035 / 1000000000000), orderedInterval (-66465908933 / 1000000000000) (-66465902956 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 3) <| besselDerivativeNearFromState (28107581352047 / 160000000000) 3 (IntervalRat.scale (295 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (30322368239 / 1000000000000) (30322368240 / 1000000000000), orderedInterval (51918165559 / 1000000000000) (51918165560 / 1000000000000)))) (orderedInterval (16007061483 / 1000000000000) (16007061522 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 3) <| besselDerivativeNearFromState (25362533220013 / 800000000000) 3 (IntervalRat.scale (295 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (124208274422 / 1000000000000) (124208274423 / 1000000000000), orderedInterval (66244222844 / 1000000000000) (66244222845 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 3) <| besselDerivativeNearFromState (68127331764361 / 800000000000) 3 (IntervalRat.scale (295 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-77827171712 / 1000000000000) (-77827171711 / 1000000000000), orderedInterval (-37206009790 / 1000000000000) (-37206009789 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 3) <| besselDerivativeNearFromState (184978958393637 / 800000000000) 3 (IntervalRat.scale (295 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-23730902828 / 1000000000000) (-23730901136 / 1000000000000), orderedInterval (46849943096 / 1000000000000) (46849944788 / 1000000000000)))) (orderedInterval (13119554633 / 1000000000000) (13119555141 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 3) <| besselDerivativeNearFromState (136254663528781 / 800000000000) 3 (IntervalRat.scale (295 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (60742112646 / 1000000000000) (60742112656 / 1000000000000), orderedInterval (6764525976 / 1000000000000) (6764525986 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 3) <| besselDerivativeNearFromState (233474688342913 / 800000000000) 3 (IntervalRat.scale (295 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-20743600445 / 1000000000000) (-20743600444 / 1000000000000), orderedInterval (-41810367175 / 1000000000000) (-41810367174 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 3) <| besselDerivativeNearFromState (171976398715267 / 800000000000) 3 (IntervalRat.scale (295 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (46215685878 / 1000000000000) (46215726288 / 1000000000000), orderedInterval (-28839609900 / 1000000000000) (-28839569491 / 1000000000000)))) (orderedInterval (-7798234937 / 1000000000000) (-7798231853 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate273_chunkChecks3_1 :
    compactCertificate273.chunkChecks (3 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 3) <| besselDerivativeNearFromState (263856021344941 / 800000000000) 3 (IntervalRat.scale (295 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-29553314675 / 1000000000000) (-29553314674 / 1000000000000), orderedInterval (-32463740030 / 1000000000000) (-32463740029 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 3) <| besselDerivativeNearFromState (152337344950789 / 800000000000) 3 (IntervalRat.scale (295 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (24141941748 / 1000000000000) (24141943123 / 1000000000000), orderedInterval (-52602753965 / 1000000000000) (-52602752590 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 3) <| besselDerivativeNearFromState (270325291880201 / 800000000000) 3 (IntervalRat.scale (295 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-24521425570 / 1000000000000) (-24521421599 / 1000000000000), orderedInterval (35851244267 / 1000000000000) (35851248238 / 1000000000000)))) (orderedInterval (-117305891528 / 1000000000000) (-117305883929 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 3) <| besselDerivativeNearFromState (252572953349069 / 800000000000) 3 (IntervalRat.scale (295 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (32202100087 / 1000000000000) (32202131829 / 1000000000000), orderedInterval (-31347246278 / 1000000000000) (-31347214536 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 3) <| besselDerivativeNearFromState (180247977334877 / 800000000000) 3 (IntervalRat.scale (295 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-5299093190 / 1000000000000) (-5299093178 / 1000000000000), orderedInterval (52902732699 / 1000000000000) (52902732711 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 3) <| besselDerivativeNearFromState (204381995293083 / 800000000000) 3 (IntervalRat.scale (295 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-48687031516 / 1000000000000) (-48687029801 / 1000000000000), orderedInterval (11115754625 / 1000000000000) (11115756340 / 1000000000000)))) (orderedInterval (-23108036535 / 1000000000000) (-23108030767 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 3) <| besselDerivativeNearFromState (170392399781227 / 800000000000) 3 (IntervalRat.scale (295 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (8008339001 / 1000000000000) (8008339002 / 1000000000000), orderedInterval (54062924849 / 1000000000000) (54062924850 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 3) <| besselDerivativeNearFromState (150546852689767 / 800000000000) 3 (IntervalRat.scale (295 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (26483342526 / 1000000000000) (26483342527 / 1000000000000), orderedInterval (51713915803 / 1000000000000) (51713915804 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 3) <| besselDerivativeNearFromState (43634345754933 / 160000000000) 3 (IntervalRat.scale (295 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-8699310546 / 1000000000000) (-8699310545 / 1000000000000), orderedInterval (-47509897366 / 1000000000000) (-47509897365 / 1000000000000)))) (orderedInterval (11933436813 / 1000000000000) (11933436861 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate273_chunkChecks3_2 :
    compactCertificate273.chunkChecks (3 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 3) <| besselDerivativeNearFromState (120694896707951 / 800000000000) 3 (IntervalRat.scale (295 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (49090412657 / 1000000000000) (49090412658 / 1000000000000), orderedInterval (42379340921 / 1000000000000) (42379340922 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 3) <| besselDerivativeNearFromState (102314400598711 / 800000000000) 3 (IntervalRat.scale (295 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (8997543607 / 1000000000000) (8997543645 / 1000000000000), orderedInterval (-70012557897 / 1000000000000) (-70012557859 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 3) <| besselDerivativeNearFromState (64023601284733 / 800000000000) 3 (IntervalRat.scale (295 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-68058624132 / 1000000000000) (-68058543612 / 1000000000000), orderedInterval (58069030327 / 1000000000000) (58069110847 / 1000000000000)))) (orderedInterval (4303020501 / 1000000000000) (4303020958 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 3) <| besselDerivativeNearFromState (34432105703811 / 800000000000) 3 (IntervalRat.scale (295 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-19335965219 / 1000000000000) (-19335965109 / 1000000000000), orderedInterval (120301128534 / 1000000000000) (120301128643 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 3) <| besselDerivativeNearFromState (93489864984433 / 800000000000) 3 (IntervalRat.scale (295 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-72828449385 / 1000000000000) (-72828449382 / 1000000000000), orderedInterval (-11670656820 / 1000000000000) (-11670656817 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 3) <| besselDerivativeNearFromState (127652417941841 / 800000000000) 3 (IntervalRat.scale (295 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-8120054152 / 1000000000000) (-8120054151 / 1000000000000), orderedInterval (-62614728616 / 1000000000000) (-62614728615 / 1000000000000)))) (orderedInterval (-6139162156 / 1000000000000) (-6139162139 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 3) <| besselDerivativeNearFromState (53976398715267 / 800000000000) 3 (IntervalRat.scale (295 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-73676287801 / 1000000000000) (-73676206596 / 1000000000000), orderedInterval (63849146930 / 1000000000000) (63849228135 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 3) <| besselDerivativeNearFromState (219411064097507 / 800000000000) 3 (IntervalRat.scale (295 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-47567846060 / 1000000000000) (-47567845144 / 1000000000000), orderedInterval (7734671438 / 1000000000000) (7734672354 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 3) <| besselDerivativeNearFromState (146556422416813 / 800000000000) 3 (IntervalRat.scale (295 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (57808684288 / 1000000000000) (57808685117 / 1000000000000), orderedInterval (-11700204227 / 1000000000000) (-11700203398 / 1000000000000)))) (orderedInterval (-218183057 / 1000000000000) (-218182098 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate273_chunkChecks3 :
    compactCertificate273.chunkChecks (3 : Fin 5) 0 9 = true :=
  compactCertificate273.chunkChecks_nine_of_three (3 : Fin 5) compactCertificate273_chunkChecks3_0
    compactCertificate273_chunkChecks3_1 compactCertificate273_chunkChecks3_2

theorem compactCertificate273_chunkChecks4_0 :
    compactCertificate273.chunkChecks (4 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 4) <| besselDerivativeNearFromState (295 / 2) 4 (IntervalRat.scale (295 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-38688660328 / 1000000000000) (-38688660327 / 1000000000000), orderedInterval (-52965571040 / 1000000000000) (-52965571039 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 4) <| besselDerivativeNearFromState (86918265926159 / 800000000000) 4 (IntervalRat.scale (295 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (38277655058 / 1000000000000) (38277661035 / 1000000000000), orderedInterval (-66465908933 / 1000000000000) (-66465902956 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 4) <| besselDerivativeNearFromState (28107581352047 / 160000000000) 4 (IntervalRat.scale (295 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (30322368239 / 1000000000000) (30322368240 / 1000000000000), orderedInterval (51918165559 / 1000000000000) (51918165560 / 1000000000000)))) (orderedInterval (-11866082812 / 1000000000000) (-11866082776 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 4) <| besselDerivativeNearFromState (25362533220013 / 800000000000) 4 (IntervalRat.scale (295 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (124208274422 / 1000000000000) (124208274423 / 1000000000000), orderedInterval (66244222844 / 1000000000000) (66244222845 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 4) <| besselDerivativeNearFromState (68127331764361 / 800000000000) 4 (IntervalRat.scale (295 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-77827171712 / 1000000000000) (-77827171711 / 1000000000000), orderedInterval (-37206009790 / 1000000000000) (-37206009789 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 4) <| besselDerivativeNearFromState (184978958393637 / 800000000000) 4 (IntervalRat.scale (295 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-23730902828 / 1000000000000) (-23730901136 / 1000000000000), orderedInterval (46849943096 / 1000000000000) (46849944788 / 1000000000000)))) (orderedInterval (9691190891 / 1000000000000) (9691191689 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 4) <| besselDerivativeNearFromState (136254663528781 / 800000000000) 4 (IntervalRat.scale (295 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (60742112646 / 1000000000000) (60742112656 / 1000000000000), orderedInterval (6764525976 / 1000000000000) (6764525986 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 4) <| besselDerivativeNearFromState (233474688342913 / 800000000000) 4 (IntervalRat.scale (295 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-20743600445 / 1000000000000) (-20743600444 / 1000000000000), orderedInterval (-41810367175 / 1000000000000) (-41810367174 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 4) <| besselDerivativeNearFromState (171976398715267 / 800000000000) 4 (IntervalRat.scale (295 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (46215685878 / 1000000000000) (46215726288 / 1000000000000), orderedInterval (-28839609900 / 1000000000000) (-28839569491 / 1000000000000)))) (orderedInterval (14950771419 / 1000000000000) (14950775953 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate273_chunkChecks4_1 :
    compactCertificate273.chunkChecks (4 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 4) <| besselDerivativeNearFromState (263856021344941 / 800000000000) 4 (IntervalRat.scale (295 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-29553314675 / 1000000000000) (-29553314674 / 1000000000000), orderedInterval (-32463740030 / 1000000000000) (-32463740029 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 4) <| besselDerivativeNearFromState (152337344950789 / 800000000000) 4 (IntervalRat.scale (295 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (24141941748 / 1000000000000) (24141943123 / 1000000000000), orderedInterval (-52602753965 / 1000000000000) (-52602752590 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 4) <| besselDerivativeNearFromState (270325291880201 / 800000000000) 4 (IntervalRat.scale (295 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-24521425570 / 1000000000000) (-24521421599 / 1000000000000), orderedInterval (35851244267 / 1000000000000) (35851248238 / 1000000000000)))) (orderedInterval (41827586358 / 1000000000000) (41827603552 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 4) <| besselDerivativeNearFromState (252572953349069 / 800000000000) 4 (IntervalRat.scale (295 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (32202100087 / 1000000000000) (32202131829 / 1000000000000), orderedInterval (-31347246278 / 1000000000000) (-31347214536 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 4) <| besselDerivativeNearFromState (180247977334877 / 800000000000) 4 (IntervalRat.scale (295 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-5299093190 / 1000000000000) (-5299093178 / 1000000000000), orderedInterval (52902732699 / 1000000000000) (52902732711 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 4) <| besselDerivativeNearFromState (204381995293083 / 800000000000) 4 (IntervalRat.scale (295 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-48687031516 / 1000000000000) (-48687029801 / 1000000000000), orderedInterval (11115754625 / 1000000000000) (11115756340 / 1000000000000)))) (orderedInterval (-12399956960 / 1000000000000) (-12399944631 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 4) <| besselDerivativeNearFromState (170392399781227 / 800000000000) 4 (IntervalRat.scale (295 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (8008339001 / 1000000000000) (8008339002 / 1000000000000), orderedInterval (54062924849 / 1000000000000) (54062924850 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 4) <| besselDerivativeNearFromState (150546852689767 / 800000000000) 4 (IntervalRat.scale (295 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (26483342526 / 1000000000000) (26483342527 / 1000000000000), orderedInterval (51713915803 / 1000000000000) (51713915804 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 4) <| besselDerivativeNearFromState (43634345754933 / 160000000000) 4 (IntervalRat.scale (295 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-8699310546 / 1000000000000) (-8699310545 / 1000000000000), orderedInterval (-47509897366 / 1000000000000) (-47509897365 / 1000000000000)))) (orderedInterval (-6377901477 / 1000000000000) (-6377901401 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate273_chunkChecks4_2 :
    compactCertificate273.chunkChecks (4 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 4) <| besselDerivativeNearFromState (120694896707951 / 800000000000) 4 (IntervalRat.scale (295 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (49090412657 / 1000000000000) (49090412658 / 1000000000000), orderedInterval (42379340921 / 1000000000000) (42379340922 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 4) <| besselDerivativeNearFromState (102314400598711 / 800000000000) 4 (IntervalRat.scale (295 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (8997543607 / 1000000000000) (8997543645 / 1000000000000), orderedInterval (-70012557897 / 1000000000000) (-70012557859 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 4) <| besselDerivativeNearFromState (64023601284733 / 800000000000) 4 (IntervalRat.scale (295 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-68058624132 / 1000000000000) (-68058543612 / 1000000000000), orderedInterval (58069030327 / 1000000000000) (58069110847 / 1000000000000)))) (orderedInterval (-9128948645 / 1000000000000) (-9128948378 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 4) <| besselDerivativeNearFromState (34432105703811 / 800000000000) 4 (IntervalRat.scale (295 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-19335965219 / 1000000000000) (-19335965109 / 1000000000000), orderedInterval (120301128534 / 1000000000000) (120301128643 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 4) <| besselDerivativeNearFromState (93489864984433 / 800000000000) 4 (IntervalRat.scale (295 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-72828449385 / 1000000000000) (-72828449382 / 1000000000000), orderedInterval (-11670656820 / 1000000000000) (-11670656817 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 4) <| besselDerivativeNearFromState (127652417941841 / 800000000000) 4 (IntervalRat.scale (295 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-8120054152 / 1000000000000) (-8120054151 / 1000000000000), orderedInterval (-62614728616 / 1000000000000) (-62614728615 / 1000000000000)))) (orderedInterval (1589089949 / 1000000000000) (1589089967 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 4) <| besselDerivativeNearFromState (53976398715267 / 800000000000) 4 (IntervalRat.scale (295 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-73676287801 / 1000000000000) (-73676206596 / 1000000000000), orderedInterval (63849146930 / 1000000000000) (63849228135 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 4) <| besselDerivativeNearFromState (219411064097507 / 800000000000) 4 (IntervalRat.scale (295 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-47567846060 / 1000000000000) (-47567845144 / 1000000000000), orderedInterval (7734671438 / 1000000000000) (7734672354 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 4) <| besselDerivativeNearFromState (146556422416813 / 800000000000) 4 (IntervalRat.scale (295 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (57808684288 / 1000000000000) (57808685117 / 1000000000000), orderedInterval (-11700204227 / 1000000000000) (-11700203398 / 1000000000000)))) (orderedInterval (20460624347 / 1000000000000) (20460625851 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate273_chunkChecks4 :
    compactCertificate273.chunkChecks (4 : Fin 5) 0 9 = true :=
  compactCertificate273.chunkChecks_nine_of_three (4 : Fin 5) compactCertificate273_chunkChecks4_0
    compactCertificate273_chunkChecks4_1 compactCertificate273_chunkChecks4_2

theorem compactCertificate273_chunks :
    ∀ r : Fin 5, ∀ b, compactCertificate273.chunkCheck r b = true :=
  compactCertificate273.chunkChecks_all (by
    intro r
    fin_cases r
    · exact compactCertificate273_chunkChecks0
    · exact compactCertificate273_chunkChecks1
    · exact compactCertificate273_chunkChecks2
    · exact compactCertificate273_chunkChecks3
    · exact compactCertificate273_chunkChecks4)

theorem compactCertificate273_coefficient0 :
    compactCertificate273.coefficientCheck (0 : Fin 5) = true := by
  norm_num [CompactCertificate.coefficientCheck, intervalFinSumHull,
    compactCertificate273, rationalIntervalSubset, orderedInterval, Fin.sum_univ_succ]

theorem compactCertificate273_coefficient1 :
    compactCertificate273.coefficientCheck (1 : Fin 5) = true := by
  norm_num [CompactCertificate.coefficientCheck, intervalFinSumHull,
    compactCertificate273, rationalIntervalSubset, orderedInterval, Fin.sum_univ_succ]

theorem compactCertificate273_coefficient2 :
    compactCertificate273.coefficientCheck (2 : Fin 5) = true := by
  norm_num [CompactCertificate.coefficientCheck, intervalFinSumHull,
    compactCertificate273, rationalIntervalSubset, orderedInterval, Fin.sum_univ_succ]

theorem compactCertificate273_coefficient3 :
    compactCertificate273.coefficientCheck (3 : Fin 5) = true := by
  norm_num [CompactCertificate.coefficientCheck, intervalFinSumHull,
    compactCertificate273, rationalIntervalSubset, orderedInterval, Fin.sum_univ_succ]

theorem compactCertificate273_coefficient4 :
    compactCertificate273.coefficientCheck (4 : Fin 5) = true := by
  norm_num [CompactCertificate.coefficientCheck, intervalFinSumHull,
    compactCertificate273, rationalIntervalSubset, orderedInterval, Fin.sum_univ_succ]

theorem compactCertificate273_coefficients : ∀ r : Fin 5,
    compactCertificate273.coefficientCheck r = true := by
  intro r
  fin_cases r
  · exact compactCertificate273_coefficient0
  · exact compactCertificate273_coefficient1
  · exact compactCertificate273_coefficient2
  · exact compactCertificate273_coefficient3
  · exact compactCertificate273_coefficient4

theorem compactCertificate273_lower : (1 : ℚ) ≤ compactCertificate273.output.lo := by
  norm_num [CompactCertificate.output, CompactCertificate.interval,
    CompactCertificate.coefficientTargetNat, compactCertificate273, dualConstant,
    intervalTaylorSum, intervalPow, intervalSub, intervalMaxAbs, widenInterval,
    rationalErrorInterval, orderedInterval, IntervalRat.add, IntervalRat.mul, IntervalRat.scale,
    IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4]

theorem compactCertificate273_proves {t : ℝ} (ht : t ∈ compactCertificate273.interval) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t :=
  compactCertificate273.proves compactCertificate273_states compactCertificate273_chunks
    compactCertificate273_coefficients compactCertificate273_lower ht

end Erdos232
