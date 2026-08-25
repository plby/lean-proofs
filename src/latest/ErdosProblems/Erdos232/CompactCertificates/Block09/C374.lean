/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, OpenAI Codex
-/
import ErdosProblems.Erdos232.CompactBase

open LeanCert.Core
namespace Erdos232

def compactCertificate374 : CompactCertificate where
  left := 245
  right := 246
  center := 491 / 2
  grid := fun i =>
    match i.val with
    | 0 => 78
    | 1 => 58
    | 2 => 93
    | 3 => 17
    | 4 => 45
    | 5 => 123
    | 6 => 90
    | 7 => 155
    | 8 => 114
    | 9 => 175
    | 10 => 101
    | 11 => 179
    | 12 => 167
    | 13 => 119
    | 14 => 135
    | 15 => 113
    | 16 => 100
    | 17 => 145
    | 18 => 80
    | 19 => 68
    | 20 => 42
    | 21 => 23
    | 22 => 62
    | 23 => 85
    | 24 => 36
    | 25 => 145
    | _ => 97
  point := fun i =>
    match i.val with
    | 0 => 491 / 2
    | 1 => 723336755419391 / 4000000000000
    | 2 => 233912244811103 / 800000000000
    | 3 => 211067861203837 / 4000000000000
    | 4 => 566957964344089 / 4000000000000
    | 5 => 1539401162225013 / 4000000000000
    | 6 => 1133915928688669 / 4000000000000
    | 7 => 1942984270785937 / 4000000000000
    | 8 => 1431193419816883 / 4000000000000
    | 9 => 2195818753904509 / 4000000000000
    | 10 => 1267756548658261 / 4000000000000
    | 11 => 2249656242596249 / 4000000000000
    | 12 => 2101920679565981 / 4000000000000
    | 13 => 1500029777481773 / 4000000000000
    | 14 => 1700873893032267 / 4000000000000
    | 15 => 1418011326992923 / 4000000000000
    | 16 => 1252856011367383 / 4000000000000
    | 17 => 363126504502917 / 800000000000
    | 18 => 1004427021755999 / 4000000000000
    | 19 => 851463910067239 / 4000000000000
    | 20 => 532806580183117 / 4000000000000
    | 21 => 286545150857139 / 4000000000000
    | 22 => 778025825548417 / 4000000000000
    | 23 => 1062327749312609 / 4000000000000
    | 24 => 449193419816883 / 4000000000000
    | 25 => 1825946313082643 / 4000000000000
    | _ => 1219647515367037 / 4000000000000
  state := fun i =>
    match i.val with
    | 0 => (orderedInterval (48173084532 / 1000000000000) (48173084533 / 1000000000000), orderedInterval (16409631083 / 1000000000000) (16409631085 / 1000000000000))
    | 1 => (orderedInterval (-33182054216 / 1000000000000) (-33182045780 / 1000000000000), orderedInterval (49279321150 / 1000000000000) (49279329585 / 1000000000000))
    | 2 => (orderedInterval (-39443760876 / 1000000000000) (-39443760875 / 1000000000000), orderedInterval (-24862105420 / 1000000000000) (-24862105419 / 1000000000000))
    | 3 => (orderedInterval (-15644526872 / 1000000000000) (-15644526871 / 1000000000000), orderedInterval (-108573936762 / 1000000000000) (-108573936760 / 1000000000000))
    | 4 => (orderedInterval (-61235706162 / 1000000000000) (-61235706161 / 1000000000000), orderedInterval (-27017190582 / 1000000000000) (-27017190581 / 1000000000000))
    | 5 => (orderedInterval (28619059801 / 1000000000000) (28619078985 / 1000000000000), orderedInterval (-28936152599 / 1000000000000) (-28936133415 / 1000000000000))
    | 6 => (orderedInterval (47329501886 / 1000000000000) (47329501947 / 1000000000000), orderedInterval (2294261899 / 1000000000000) (2294261960 / 1000000000000))
    | 7 => (orderedInterval (14617996782 / 1000000000000) (14617996957 / 1000000000000), orderedInterval (-33134778978 / 1000000000000) (-33134778803 / 1000000000000))
    | 8 => (orderedInterval (18036948511 / 1000000000000) (18036948512 / 1000000000000), orderedInterval (38105350470 / 1000000000000) (38105350471 / 1000000000000))
    | 9 => (orderedInterval (1322861299 / 1000000000000) (1322861300 / 1000000000000), orderedInterval (-34029797123 / 1000000000000) (-34029797122 / 1000000000000))
    | 10 => (orderedInterval (-18409229469 / 1000000000000) (-18409229468 / 1000000000000), orderedInterval (-40833555009 / 1000000000000) (-40833555008 / 1000000000000))
    | 11 => (orderedInterval (-25368292372 / 1000000000000) (-25368292371 / 1000000000000), orderedInterval (-22077019470 / 1000000000000) (-22077019469 / 1000000000000))
    | 12 => (orderedInterval (-34765584769 / 1000000000000) (-34765583657 / 1000000000000), orderedInterval (1722649437 / 1000000000000) (1722650549 / 1000000000000))
    | 13 => (orderedInterval (-38381224388 / 1000000000000) (-38381208885 / 1000000000000), orderedInterval (15034493520 / 1000000000000) (15034509023 / 1000000000000))
    | 14 => (orderedInterval (-36755910248 / 1000000000000) (-36755898561 / 1000000000000), orderedInterval (12132957562 / 1000000000000) (12132969249 / 1000000000000))
    | 15 => (orderedInterval (-12032791770 / 1000000000000) (-12032791769 / 1000000000000), orderedInterval (-40615817638 / 1000000000000) (-40615817637 / 1000000000000))
    | 16 => (orderedInterval (-7194373310 / 1000000000000) (-7194373295 / 1000000000000), orderedInterval (44517470361 / 1000000000000) (44517470376 / 1000000000000))
    | 17 => (orderedInterval (27829104407 / 1000000000000) (27829128041 / 1000000000000), orderedInterval (-25091995042 / 1000000000000) (-25091971408 / 1000000000000))
    | 18 => (orderedInterval (26926688807 / 1000000000000) (26926688808 / 1000000000000), orderedInterval (42492959138 / 1000000000000) (42492959139 / 1000000000000))
    | 19 => (orderedInterval (1229704969 / 1000000000000) (1229704971 / 1000000000000), orderedInterval (54670716561 / 1000000000000) (54670716563 / 1000000000000))
    | 20 => (orderedInterval (61686032071 / 1000000000000) (61686044130 / 1000000000000), orderedInterval (-31443433279 / 1000000000000) (-31443421221 / 1000000000000))
    | 21 => (orderedInterval (-15326715691 / 1000000000000) (-15326715690 / 1000000000000), orderedInterval (-92909857865 / 1000000000000) (-92909857863 / 1000000000000))
    | 22 => (orderedInterval (28051755855 / 1000000000000) (28051755856 / 1000000000000), orderedInterval (49788750090 / 1000000000000) (49788750091 / 1000000000000))
    | 23 => (orderedInterval (30346212019 / 1000000000000) (30346223659 / 1000000000000), orderedInterval (-38478261989 / 1000000000000) (-38478250349 / 1000000000000))
    | 24 => (orderedInterval (-1106417710 / 1000000000000) (-1106417702 / 1000000000000), orderedInterval (75289954834 / 1000000000000) (75289954841 / 1000000000000))
    | 25 => (orderedInterval (-36806290391 / 1000000000000) (-36806287421 / 1000000000000), orderedInterval (6357287949 / 1000000000000) (6357290919 / 1000000000000))
    | _ => (orderedInterval (-37493827655 / 1000000000000) (-37493827654 / 1000000000000), orderedInterval (-26055429093 / 1000000000000) (-26055429092 / 1000000000000))
  chunkTarget := fun r b =>
    match r.val with
    | 0 =>
      match b.val with
      | 0 => orderedInterval (16470327078 / 1000000000000) (16470327175 / 1000000000000)
      | 1 => orderedInterval (-4100610591 / 1000000000000) (-4100609197 / 1000000000000)
      | 2 => orderedInterval (-14960061 / 1000000000000) (-14960041 / 1000000000000)
      | 3 => orderedInterval (-5205281174 / 1000000000000) (-5205281076 / 1000000000000)
      | 4 => orderedInterval (-2815806504 / 1000000000000) (-2815804929 / 1000000000000)
      | 5 => orderedInterval (985294354 / 1000000000000) (985294984 / 1000000000000)
      | 6 => orderedInterval (-2366769816 / 1000000000000) (-2366769361 / 1000000000000)
      | 7 => orderedInterval (-2679097020 / 1000000000000) (-2679096098 / 1000000000000)
      | _ => orderedInterval (10024263984 / 1000000000000) (10024264295 / 1000000000000)
    | 1 =>
      match b.val with
      | 0 => orderedInterval (5104846416 / 1000000000000) (5104846495 / 1000000000000)
      | 1 => orderedInterval (2908344417 / 1000000000000) (2908346589 / 1000000000000)
      | 2 => orderedInterval (3364336332 / 1000000000000) (3364336368 / 1000000000000)
      | 3 => orderedInterval (2425295751 / 1000000000000) (2425295953 / 1000000000000)
      | 4 => orderedInterval (1998776173 / 1000000000000) (1998778606 / 1000000000000)
      | 5 => orderedInterval (-5115369870 / 1000000000000) (-5115368715 / 1000000000000)
      | 6 => orderedInterval (-10187907066 / 1000000000000) (-10187906795 / 1000000000000)
      | 7 => orderedInterval (2795829626 / 1000000000000) (2795830618 / 1000000000000)
      | _ => orderedInterval (5317145662 / 1000000000000) (5317146208 / 1000000000000)
    | 2 =>
      match b.val with
      | 0 => orderedInterval (-15663939989 / 1000000000000) (-15663939923 / 1000000000000)
      | 1 => orderedInterval (5725267662 / 1000000000000) (5725271069 / 1000000000000)
      | 2 => orderedInterval (825486111 / 1000000000000) (825486175 / 1000000000000)
      | 3 => orderedInterval (22364978592 / 1000000000000) (22364979026 / 1000000000000)
      | 4 => orderedInterval (5027044615 / 1000000000000) (5027048394 / 1000000000000)
      | 5 => orderedInterval (-2795367271 / 1000000000000) (-2795365145 / 1000000000000)
      | 6 => orderedInterval (4006912093 / 1000000000000) (4006912265 / 1000000000000)
      | 7 => orderedInterval (3085745127 / 1000000000000) (3085746202 / 1000000000000)
      | _ => orderedInterval (-21230799770 / 1000000000000) (-21230798791 / 1000000000000)
    | 3 =>
      match b.val with
      | 0 => orderedInterval (-4159093269 / 1000000000000) (-4159093210 / 1000000000000)
      | 1 => orderedInterval (-7769558569 / 1000000000000) (-7769553231 / 1000000000000)
      | 2 => orderedInterval (-10770652282 / 1000000000000) (-10770652162 / 1000000000000)
      | 3 => orderedInterval (-23452527967 / 1000000000000) (-23452527016 / 1000000000000)
      | 4 => orderedInterval (-4463708936 / 1000000000000) (-4463703058 / 1000000000000)
      | 5 => orderedInterval (10774619712 / 1000000000000) (10774623626 / 1000000000000)
      | 6 => orderedInterval (9434670452 / 1000000000000) (9434670569 / 1000000000000)
      | 7 => orderedInterval (-3226793886 / 1000000000000) (-3226792724 / 1000000000000)
      | _ => orderedInterval (-5996154884 / 1000000000000) (-5996153108 / 1000000000000)
    | _ =>
      match b.val with
      | 0 => orderedInterval (14379547892 / 1000000000000) (14379547947 / 1000000000000)
      | 1 => orderedInterval (-12471032758 / 1000000000000) (-12471024372 / 1000000000000)
      | 2 => orderedInterval (-4855667190 / 1000000000000) (-4855666963 / 1000000000000)
      | 3 => orderedInterval (-108802504447 / 1000000000000) (-108802502335 / 1000000000000)
      | 4 => orderedInterval (-4875694590 / 1000000000000) (-4875685377 / 1000000000000)
      | 5 => orderedInterval (8725538785 / 1000000000000) (8725546014 / 1000000000000)
      | 6 => orderedInterval (-4654457581 / 1000000000000) (-4654457494 / 1000000000000)
      | 7 => orderedInterval (-3407611456 / 1000000000000) (-3407610196 / 1000000000000)
      | _ => orderedInterval (52602569846 / 1000000000000) (52602573098 / 1000000000000)
  coefficientTarget := fun i =>
    match i.val with
    | 0 => orderedInterval (10297360250 / 1000000000000) (10297365752 / 1000000000000)
    | 1 => orderedInterval (8611297441 / 1000000000000) (8611305327 / 1000000000000)
    | 2 => orderedInterval (1345327170 / 1000000000000) (1345339272 / 1000000000000)
    | 3 => orderedInterval (-39629199629 / 1000000000000) (-39629180314 / 1000000000000)
    | _ => orderedInterval (-63359311499 / 1000000000000) (-63359279678 / 1000000000000)

theorem compactCertificate374_stateChecks0 :
    compactCertificate374.stateChecks 0 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 78 12 (491 / 2)) (orderedInterval (48173084532 / 1000000000000) (48173084533 / 1000000000000), orderedInterval (16409631083 / 1000000000000) (16409631085 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 58 12 (723336755419391 / 4000000000000)) (orderedInterval (-33182054216 / 1000000000000) (-33182045780 / 1000000000000), orderedInterval (49279321150 / 1000000000000) (49279329585 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 93 12 (233912244811103 / 800000000000)) (orderedInterval (-39443760876 / 1000000000000) (-39443760875 / 1000000000000), orderedInterval (-24862105420 / 1000000000000) (-24862105419 / 1000000000000))) = true
  rfl'

theorem compactCertificate374_stateChecks1 :
    compactCertificate374.stateChecks 3 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 17 12 (211067861203837 / 4000000000000)) (orderedInterval (-15644526872 / 1000000000000) (-15644526871 / 1000000000000), orderedInterval (-108573936762 / 1000000000000) (-108573936760 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 45 12 (566957964344089 / 4000000000000)) (orderedInterval (-61235706162 / 1000000000000) (-61235706161 / 1000000000000), orderedInterval (-27017190582 / 1000000000000) (-27017190581 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 123 12 (1539401162225013 / 4000000000000)) (orderedInterval (28619059801 / 1000000000000) (28619078985 / 1000000000000), orderedInterval (-28936152599 / 1000000000000) (-28936133415 / 1000000000000))) = true
  rfl'

theorem compactCertificate374_stateChecks2 :
    compactCertificate374.stateChecks 6 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 90 12 (1133915928688669 / 4000000000000)) (orderedInterval (47329501886 / 1000000000000) (47329501947 / 1000000000000), orderedInterval (2294261899 / 1000000000000) (2294261960 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 155 12 (1942984270785937 / 4000000000000)) (orderedInterval (14617996782 / 1000000000000) (14617996957 / 1000000000000), orderedInterval (-33134778978 / 1000000000000) (-33134778803 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 114 12 (1431193419816883 / 4000000000000)) (orderedInterval (18036948511 / 1000000000000) (18036948512 / 1000000000000), orderedInterval (38105350470 / 1000000000000) (38105350471 / 1000000000000))) = true
  rfl'

theorem compactCertificate374_stateChecks3 :
    compactCertificate374.stateChecks 9 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 175 12 (2195818753904509 / 4000000000000)) (orderedInterval (1322861299 / 1000000000000) (1322861300 / 1000000000000), orderedInterval (-34029797123 / 1000000000000) (-34029797122 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 101 12 (1267756548658261 / 4000000000000)) (orderedInterval (-18409229469 / 1000000000000) (-18409229468 / 1000000000000), orderedInterval (-40833555009 / 1000000000000) (-40833555008 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 179 12 (2249656242596249 / 4000000000000)) (orderedInterval (-25368292372 / 1000000000000) (-25368292371 / 1000000000000), orderedInterval (-22077019470 / 1000000000000) (-22077019469 / 1000000000000))) = true
  rfl'

theorem compactCertificate374_stateChecks4 :
    compactCertificate374.stateChecks 12 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 167 12 (2101920679565981 / 4000000000000)) (orderedInterval (-34765584769 / 1000000000000) (-34765583657 / 1000000000000), orderedInterval (1722649437 / 1000000000000) (1722650549 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 119 12 (1500029777481773 / 4000000000000)) (orderedInterval (-38381224388 / 1000000000000) (-38381208885 / 1000000000000), orderedInterval (15034493520 / 1000000000000) (15034509023 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 135 12 (1700873893032267 / 4000000000000)) (orderedInterval (-36755910248 / 1000000000000) (-36755898561 / 1000000000000), orderedInterval (12132957562 / 1000000000000) (12132969249 / 1000000000000))) = true
  rfl'

theorem compactCertificate374_stateChecks5 :
    compactCertificate374.stateChecks 15 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 113 12 (1418011326992923 / 4000000000000)) (orderedInterval (-12032791770 / 1000000000000) (-12032791769 / 1000000000000), orderedInterval (-40615817638 / 1000000000000) (-40615817637 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 100 12 (1252856011367383 / 4000000000000)) (orderedInterval (-7194373310 / 1000000000000) (-7194373295 / 1000000000000), orderedInterval (44517470361 / 1000000000000) (44517470376 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 145 12 (363126504502917 / 800000000000)) (orderedInterval (27829104407 / 1000000000000) (27829128041 / 1000000000000), orderedInterval (-25091995042 / 1000000000000) (-25091971408 / 1000000000000))) = true
  rfl'

theorem compactCertificate374_stateChecks6 :
    compactCertificate374.stateChecks 18 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 80 12 (1004427021755999 / 4000000000000)) (orderedInterval (26926688807 / 1000000000000) (26926688808 / 1000000000000), orderedInterval (42492959138 / 1000000000000) (42492959139 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 68 12 (851463910067239 / 4000000000000)) (orderedInterval (1229704969 / 1000000000000) (1229704971 / 1000000000000), orderedInterval (54670716561 / 1000000000000) (54670716563 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 42 12 (532806580183117 / 4000000000000)) (orderedInterval (61686032071 / 1000000000000) (61686044130 / 1000000000000), orderedInterval (-31443433279 / 1000000000000) (-31443421221 / 1000000000000))) = true
  rfl'

theorem compactCertificate374_stateChecks7 :
    compactCertificate374.stateChecks 21 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 23 12 (286545150857139 / 4000000000000)) (orderedInterval (-15326715691 / 1000000000000) (-15326715690 / 1000000000000), orderedInterval (-92909857865 / 1000000000000) (-92909857863 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 62 12 (778025825548417 / 4000000000000)) (orderedInterval (28051755855 / 1000000000000) (28051755856 / 1000000000000), orderedInterval (49788750090 / 1000000000000) (49788750091 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 85 12 (1062327749312609 / 4000000000000)) (orderedInterval (30346212019 / 1000000000000) (30346223659 / 1000000000000), orderedInterval (-38478261989 / 1000000000000) (-38478250349 / 1000000000000))) = true
  rfl'

theorem compactCertificate374_stateChecks8 :
    compactCertificate374.stateChecks 24 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 36 12 (449193419816883 / 4000000000000)) (orderedInterval (-1106417710 / 1000000000000) (-1106417702 / 1000000000000), orderedInterval (75289954834 / 1000000000000) (75289954841 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 145 12 (1825946313082643 / 4000000000000)) (orderedInterval (-36806290391 / 1000000000000) (-36806287421 / 1000000000000), orderedInterval (6357287949 / 1000000000000) (6357290919 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 97 12 (1219647515367037 / 4000000000000)) (orderedInterval (-37493827655 / 1000000000000) (-37493827654 / 1000000000000), orderedInterval (-26055429093 / 1000000000000) (-26055429092 / 1000000000000))) = true
  rfl'

theorem compactCertificate374_states : ∀ j,
    BesselStateValid (compactCertificate374.point j) (compactCertificate374.state j) :=
  compactCertificate374.statesValid_of_checks3 compactCertificate374_stateChecks0
    compactCertificate374_stateChecks1 compactCertificate374_stateChecks2
    compactCertificate374_stateChecks3 compactCertificate374_stateChecks4
    compactCertificate374_stateChecks5 compactCertificate374_stateChecks6
    compactCertificate374_stateChecks7 compactCertificate374_stateChecks8

theorem compactCertificate374_chunkChecks0_0 :
    compactCertificate374.chunkChecks (0 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 0) <| besselDerivativeNearFromState (491 / 2) 0 (IntervalRat.scale (491 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (48173084532 / 1000000000000) (48173084533 / 1000000000000), orderedInterval (16409631083 / 1000000000000) (16409631085 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 0) <| besselDerivativeNearFromState (723336755419391 / 4000000000000) 0 (IntervalRat.scale (491 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-33182054216 / 1000000000000) (-33182045780 / 1000000000000), orderedInterval (49279321150 / 1000000000000) (49279329585 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 0) <| besselDerivativeNearFromState (233912244811103 / 800000000000) 0 (IntervalRat.scale (491 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-39443760876 / 1000000000000) (-39443760875 / 1000000000000), orderedInterval (-24862105420 / 1000000000000) (-24862105419 / 1000000000000)))) (orderedInterval (16470327078 / 1000000000000) (16470327175 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 0) <| besselDerivativeNearFromState (211067861203837 / 4000000000000) 0 (IntervalRat.scale (491 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-15644526872 / 1000000000000) (-15644526871 / 1000000000000), orderedInterval (-108573936762 / 1000000000000) (-108573936760 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 0) <| besselDerivativeNearFromState (566957964344089 / 4000000000000) 0 (IntervalRat.scale (491 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-61235706162 / 1000000000000) (-61235706161 / 1000000000000), orderedInterval (-27017190582 / 1000000000000) (-27017190581 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 0) <| besselDerivativeNearFromState (1539401162225013 / 4000000000000) 0 (IntervalRat.scale (491 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (28619059801 / 1000000000000) (28619078985 / 1000000000000), orderedInterval (-28936152599 / 1000000000000) (-28936133415 / 1000000000000)))) (orderedInterval (-4100610591 / 1000000000000) (-4100609197 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 0) <| besselDerivativeNearFromState (1133915928688669 / 4000000000000) 0 (IntervalRat.scale (491 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (47329501886 / 1000000000000) (47329501947 / 1000000000000), orderedInterval (2294261899 / 1000000000000) (2294261960 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 0) <| besselDerivativeNearFromState (1942984270785937 / 4000000000000) 0 (IntervalRat.scale (491 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (14617996782 / 1000000000000) (14617996957 / 1000000000000), orderedInterval (-33134778978 / 1000000000000) (-33134778803 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 0) <| besselDerivativeNearFromState (1431193419816883 / 4000000000000) 0 (IntervalRat.scale (491 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (18036948511 / 1000000000000) (18036948512 / 1000000000000), orderedInterval (38105350470 / 1000000000000) (38105350471 / 1000000000000)))) (orderedInterval (-14960061 / 1000000000000) (-14960041 / 1000000000000))) = true
  rfl'

theorem compactCertificate374_chunkChecks0_1 :
    compactCertificate374.chunkChecks (0 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 0) <| besselDerivativeNearFromState (2195818753904509 / 4000000000000) 0 (IntervalRat.scale (491 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (1322861299 / 1000000000000) (1322861300 / 1000000000000), orderedInterval (-34029797123 / 1000000000000) (-34029797122 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 0) <| besselDerivativeNearFromState (1267756548658261 / 4000000000000) 0 (IntervalRat.scale (491 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-18409229469 / 1000000000000) (-18409229468 / 1000000000000), orderedInterval (-40833555009 / 1000000000000) (-40833555008 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 0) <| besselDerivativeNearFromState (2249656242596249 / 4000000000000) 0 (IntervalRat.scale (491 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-25368292372 / 1000000000000) (-25368292371 / 1000000000000), orderedInterval (-22077019470 / 1000000000000) (-22077019469 / 1000000000000)))) (orderedInterval (-5205281174 / 1000000000000) (-5205281076 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 0) <| besselDerivativeNearFromState (2101920679565981 / 4000000000000) 0 (IntervalRat.scale (491 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-34765584769 / 1000000000000) (-34765583657 / 1000000000000), orderedInterval (1722649437 / 1000000000000) (1722650549 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 0) <| besselDerivativeNearFromState (1500029777481773 / 4000000000000) 0 (IntervalRat.scale (491 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-38381224388 / 1000000000000) (-38381208885 / 1000000000000), orderedInterval (15034493520 / 1000000000000) (15034509023 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 0) <| besselDerivativeNearFromState (1700873893032267 / 4000000000000) 0 (IntervalRat.scale (491 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-36755910248 / 1000000000000) (-36755898561 / 1000000000000), orderedInterval (12132957562 / 1000000000000) (12132969249 / 1000000000000)))) (orderedInterval (-2815806504 / 1000000000000) (-2815804929 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 0) <| besselDerivativeNearFromState (1418011326992923 / 4000000000000) 0 (IntervalRat.scale (491 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-12032791770 / 1000000000000) (-12032791769 / 1000000000000), orderedInterval (-40615817638 / 1000000000000) (-40615817637 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 0) <| besselDerivativeNearFromState (1252856011367383 / 4000000000000) 0 (IntervalRat.scale (491 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-7194373310 / 1000000000000) (-7194373295 / 1000000000000), orderedInterval (44517470361 / 1000000000000) (44517470376 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 0) <| besselDerivativeNearFromState (363126504502917 / 800000000000) 0 (IntervalRat.scale (491 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (27829104407 / 1000000000000) (27829128041 / 1000000000000), orderedInterval (-25091995042 / 1000000000000) (-25091971408 / 1000000000000)))) (orderedInterval (985294354 / 1000000000000) (985294984 / 1000000000000))) = true
  rfl'

theorem compactCertificate374_chunkChecks0_2 :
    compactCertificate374.chunkChecks (0 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 0) <| besselDerivativeNearFromState (1004427021755999 / 4000000000000) 0 (IntervalRat.scale (491 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (26926688807 / 1000000000000) (26926688808 / 1000000000000), orderedInterval (42492959138 / 1000000000000) (42492959139 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 0) <| besselDerivativeNearFromState (851463910067239 / 4000000000000) 0 (IntervalRat.scale (491 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (1229704969 / 1000000000000) (1229704971 / 1000000000000), orderedInterval (54670716561 / 1000000000000) (54670716563 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 0) <| besselDerivativeNearFromState (532806580183117 / 4000000000000) 0 (IntervalRat.scale (491 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (61686032071 / 1000000000000) (61686044130 / 1000000000000), orderedInterval (-31443433279 / 1000000000000) (-31443421221 / 1000000000000)))) (orderedInterval (-2366769816 / 1000000000000) (-2366769361 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 0) <| besselDerivativeNearFromState (286545150857139 / 4000000000000) 0 (IntervalRat.scale (491 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-15326715691 / 1000000000000) (-15326715690 / 1000000000000), orderedInterval (-92909857865 / 1000000000000) (-92909857863 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 0) <| besselDerivativeNearFromState (778025825548417 / 4000000000000) 0 (IntervalRat.scale (491 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (28051755855 / 1000000000000) (28051755856 / 1000000000000), orderedInterval (49788750090 / 1000000000000) (49788750091 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 0) <| besselDerivativeNearFromState (1062327749312609 / 4000000000000) 0 (IntervalRat.scale (491 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (30346212019 / 1000000000000) (30346223659 / 1000000000000), orderedInterval (-38478261989 / 1000000000000) (-38478250349 / 1000000000000)))) (orderedInterval (-2679097020 / 1000000000000) (-2679096098 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 0) <| besselDerivativeNearFromState (449193419816883 / 4000000000000) 0 (IntervalRat.scale (491 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-1106417710 / 1000000000000) (-1106417702 / 1000000000000), orderedInterval (75289954834 / 1000000000000) (75289954841 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 0) <| besselDerivativeNearFromState (1825946313082643 / 4000000000000) 0 (IntervalRat.scale (491 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-36806290391 / 1000000000000) (-36806287421 / 1000000000000), orderedInterval (6357287949 / 1000000000000) (6357290919 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 0) <| besselDerivativeNearFromState (1219647515367037 / 4000000000000) 0 (IntervalRat.scale (491 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-37493827655 / 1000000000000) (-37493827654 / 1000000000000), orderedInterval (-26055429093 / 1000000000000) (-26055429092 / 1000000000000)))) (orderedInterval (10024263984 / 1000000000000) (10024264295 / 1000000000000))) = true
  rfl'

theorem compactCertificate374_chunkChecks0 :
    compactCertificate374.chunkChecks (0 : Fin 5) 0 9 = true :=
  compactCertificate374.chunkChecks_nine_of_three (0 : Fin 5) compactCertificate374_chunkChecks0_0
    compactCertificate374_chunkChecks0_1 compactCertificate374_chunkChecks0_2

theorem compactCertificate374_chunkChecks1_0 :
    compactCertificate374.chunkChecks (1 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 1) <| besselDerivativeNearFromState (491 / 2) 1 (IntervalRat.scale (491 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (48173084532 / 1000000000000) (48173084533 / 1000000000000), orderedInterval (16409631083 / 1000000000000) (16409631085 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 1) <| besselDerivativeNearFromState (723336755419391 / 4000000000000) 1 (IntervalRat.scale (491 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-33182054216 / 1000000000000) (-33182045780 / 1000000000000), orderedInterval (49279321150 / 1000000000000) (49279329585 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 1) <| besselDerivativeNearFromState (233912244811103 / 800000000000) 1 (IntervalRat.scale (491 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-39443760876 / 1000000000000) (-39443760875 / 1000000000000), orderedInterval (-24862105420 / 1000000000000) (-24862105419 / 1000000000000)))) (orderedInterval (5104846416 / 1000000000000) (5104846495 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 1) <| besselDerivativeNearFromState (211067861203837 / 4000000000000) 1 (IntervalRat.scale (491 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-15644526872 / 1000000000000) (-15644526871 / 1000000000000), orderedInterval (-108573936762 / 1000000000000) (-108573936760 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 1) <| besselDerivativeNearFromState (566957964344089 / 4000000000000) 1 (IntervalRat.scale (491 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-61235706162 / 1000000000000) (-61235706161 / 1000000000000), orderedInterval (-27017190582 / 1000000000000) (-27017190581 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 1) <| besselDerivativeNearFromState (1539401162225013 / 4000000000000) 1 (IntervalRat.scale (491 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (28619059801 / 1000000000000) (28619078985 / 1000000000000), orderedInterval (-28936152599 / 1000000000000) (-28936133415 / 1000000000000)))) (orderedInterval (2908344417 / 1000000000000) (2908346589 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 1) <| besselDerivativeNearFromState (1133915928688669 / 4000000000000) 1 (IntervalRat.scale (491 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (47329501886 / 1000000000000) (47329501947 / 1000000000000), orderedInterval (2294261899 / 1000000000000) (2294261960 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 1) <| besselDerivativeNearFromState (1942984270785937 / 4000000000000) 1 (IntervalRat.scale (491 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (14617996782 / 1000000000000) (14617996957 / 1000000000000), orderedInterval (-33134778978 / 1000000000000) (-33134778803 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 1) <| besselDerivativeNearFromState (1431193419816883 / 4000000000000) 1 (IntervalRat.scale (491 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (18036948511 / 1000000000000) (18036948512 / 1000000000000), orderedInterval (38105350470 / 1000000000000) (38105350471 / 1000000000000)))) (orderedInterval (3364336332 / 1000000000000) (3364336368 / 1000000000000))) = true
  rfl'

theorem compactCertificate374_chunkChecks1_1 :
    compactCertificate374.chunkChecks (1 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 1) <| besselDerivativeNearFromState (2195818753904509 / 4000000000000) 1 (IntervalRat.scale (491 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (1322861299 / 1000000000000) (1322861300 / 1000000000000), orderedInterval (-34029797123 / 1000000000000) (-34029797122 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 1) <| besselDerivativeNearFromState (1267756548658261 / 4000000000000) 1 (IntervalRat.scale (491 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-18409229469 / 1000000000000) (-18409229468 / 1000000000000), orderedInterval (-40833555009 / 1000000000000) (-40833555008 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 1) <| besselDerivativeNearFromState (2249656242596249 / 4000000000000) 1 (IntervalRat.scale (491 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-25368292372 / 1000000000000) (-25368292371 / 1000000000000), orderedInterval (-22077019470 / 1000000000000) (-22077019469 / 1000000000000)))) (orderedInterval (2425295751 / 1000000000000) (2425295953 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 1) <| besselDerivativeNearFromState (2101920679565981 / 4000000000000) 1 (IntervalRat.scale (491 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-34765584769 / 1000000000000) (-34765583657 / 1000000000000), orderedInterval (1722649437 / 1000000000000) (1722650549 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 1) <| besselDerivativeNearFromState (1500029777481773 / 4000000000000) 1 (IntervalRat.scale (491 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-38381224388 / 1000000000000) (-38381208885 / 1000000000000), orderedInterval (15034493520 / 1000000000000) (15034509023 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 1) <| besselDerivativeNearFromState (1700873893032267 / 4000000000000) 1 (IntervalRat.scale (491 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-36755910248 / 1000000000000) (-36755898561 / 1000000000000), orderedInterval (12132957562 / 1000000000000) (12132969249 / 1000000000000)))) (orderedInterval (1998776173 / 1000000000000) (1998778606 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 1) <| besselDerivativeNearFromState (1418011326992923 / 4000000000000) 1 (IntervalRat.scale (491 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-12032791770 / 1000000000000) (-12032791769 / 1000000000000), orderedInterval (-40615817638 / 1000000000000) (-40615817637 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 1) <| besselDerivativeNearFromState (1252856011367383 / 4000000000000) 1 (IntervalRat.scale (491 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-7194373310 / 1000000000000) (-7194373295 / 1000000000000), orderedInterval (44517470361 / 1000000000000) (44517470376 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 1) <| besselDerivativeNearFromState (363126504502917 / 800000000000) 1 (IntervalRat.scale (491 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (27829104407 / 1000000000000) (27829128041 / 1000000000000), orderedInterval (-25091995042 / 1000000000000) (-25091971408 / 1000000000000)))) (orderedInterval (-5115369870 / 1000000000000) (-5115368715 / 1000000000000))) = true
  rfl'

theorem compactCertificate374_chunkChecks1_2 :
    compactCertificate374.chunkChecks (1 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 1) <| besselDerivativeNearFromState (1004427021755999 / 4000000000000) 1 (IntervalRat.scale (491 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (26926688807 / 1000000000000) (26926688808 / 1000000000000), orderedInterval (42492959138 / 1000000000000) (42492959139 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 1) <| besselDerivativeNearFromState (851463910067239 / 4000000000000) 1 (IntervalRat.scale (491 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (1229704969 / 1000000000000) (1229704971 / 1000000000000), orderedInterval (54670716561 / 1000000000000) (54670716563 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 1) <| besselDerivativeNearFromState (532806580183117 / 4000000000000) 1 (IntervalRat.scale (491 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (61686032071 / 1000000000000) (61686044130 / 1000000000000), orderedInterval (-31443433279 / 1000000000000) (-31443421221 / 1000000000000)))) (orderedInterval (-10187907066 / 1000000000000) (-10187906795 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 1) <| besselDerivativeNearFromState (286545150857139 / 4000000000000) 1 (IntervalRat.scale (491 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-15326715691 / 1000000000000) (-15326715690 / 1000000000000), orderedInterval (-92909857865 / 1000000000000) (-92909857863 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 1) <| besselDerivativeNearFromState (778025825548417 / 4000000000000) 1 (IntervalRat.scale (491 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (28051755855 / 1000000000000) (28051755856 / 1000000000000), orderedInterval (49788750090 / 1000000000000) (49788750091 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 1) <| besselDerivativeNearFromState (1062327749312609 / 4000000000000) 1 (IntervalRat.scale (491 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (30346212019 / 1000000000000) (30346223659 / 1000000000000), orderedInterval (-38478261989 / 1000000000000) (-38478250349 / 1000000000000)))) (orderedInterval (2795829626 / 1000000000000) (2795830618 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 1) <| besselDerivativeNearFromState (449193419816883 / 4000000000000) 1 (IntervalRat.scale (491 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-1106417710 / 1000000000000) (-1106417702 / 1000000000000), orderedInterval (75289954834 / 1000000000000) (75289954841 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 1) <| besselDerivativeNearFromState (1825946313082643 / 4000000000000) 1 (IntervalRat.scale (491 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-36806290391 / 1000000000000) (-36806287421 / 1000000000000), orderedInterval (6357287949 / 1000000000000) (6357290919 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 1) <| besselDerivativeNearFromState (1219647515367037 / 4000000000000) 1 (IntervalRat.scale (491 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-37493827655 / 1000000000000) (-37493827654 / 1000000000000), orderedInterval (-26055429093 / 1000000000000) (-26055429092 / 1000000000000)))) (orderedInterval (5317145662 / 1000000000000) (5317146208 / 1000000000000))) = true
  rfl'

theorem compactCertificate374_chunkChecks1 :
    compactCertificate374.chunkChecks (1 : Fin 5) 0 9 = true :=
  compactCertificate374.chunkChecks_nine_of_three (1 : Fin 5) compactCertificate374_chunkChecks1_0
    compactCertificate374_chunkChecks1_1 compactCertificate374_chunkChecks1_2

theorem compactCertificate374_chunkChecks2_0 :
    compactCertificate374.chunkChecks (2 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 2) <| besselDerivativeNearFromState (491 / 2) 2 (IntervalRat.scale (491 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (48173084532 / 1000000000000) (48173084533 / 1000000000000), orderedInterval (16409631083 / 1000000000000) (16409631085 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 2) <| besselDerivativeNearFromState (723336755419391 / 4000000000000) 2 (IntervalRat.scale (491 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-33182054216 / 1000000000000) (-33182045780 / 1000000000000), orderedInterval (49279321150 / 1000000000000) (49279329585 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 2) <| besselDerivativeNearFromState (233912244811103 / 800000000000) 2 (IntervalRat.scale (491 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-39443760876 / 1000000000000) (-39443760875 / 1000000000000), orderedInterval (-24862105420 / 1000000000000) (-24862105419 / 1000000000000)))) (orderedInterval (-15663939989 / 1000000000000) (-15663939923 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 2) <| besselDerivativeNearFromState (211067861203837 / 4000000000000) 2 (IntervalRat.scale (491 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-15644526872 / 1000000000000) (-15644526871 / 1000000000000), orderedInterval (-108573936762 / 1000000000000) (-108573936760 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 2) <| besselDerivativeNearFromState (566957964344089 / 4000000000000) 2 (IntervalRat.scale (491 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-61235706162 / 1000000000000) (-61235706161 / 1000000000000), orderedInterval (-27017190582 / 1000000000000) (-27017190581 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 2) <| besselDerivativeNearFromState (1539401162225013 / 4000000000000) 2 (IntervalRat.scale (491 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (28619059801 / 1000000000000) (28619078985 / 1000000000000), orderedInterval (-28936152599 / 1000000000000) (-28936133415 / 1000000000000)))) (orderedInterval (5725267662 / 1000000000000) (5725271069 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 2) <| besselDerivativeNearFromState (1133915928688669 / 4000000000000) 2 (IntervalRat.scale (491 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (47329501886 / 1000000000000) (47329501947 / 1000000000000), orderedInterval (2294261899 / 1000000000000) (2294261960 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 2) <| besselDerivativeNearFromState (1942984270785937 / 4000000000000) 2 (IntervalRat.scale (491 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (14617996782 / 1000000000000) (14617996957 / 1000000000000), orderedInterval (-33134778978 / 1000000000000) (-33134778803 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 2) <| besselDerivativeNearFromState (1431193419816883 / 4000000000000) 2 (IntervalRat.scale (491 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (18036948511 / 1000000000000) (18036948512 / 1000000000000), orderedInterval (38105350470 / 1000000000000) (38105350471 / 1000000000000)))) (orderedInterval (825486111 / 1000000000000) (825486175 / 1000000000000))) = true
  rfl'

theorem compactCertificate374_chunkChecks2_1 :
    compactCertificate374.chunkChecks (2 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 2) <| besselDerivativeNearFromState (2195818753904509 / 4000000000000) 2 (IntervalRat.scale (491 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (1322861299 / 1000000000000) (1322861300 / 1000000000000), orderedInterval (-34029797123 / 1000000000000) (-34029797122 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 2) <| besselDerivativeNearFromState (1267756548658261 / 4000000000000) 2 (IntervalRat.scale (491 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-18409229469 / 1000000000000) (-18409229468 / 1000000000000), orderedInterval (-40833555009 / 1000000000000) (-40833555008 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 2) <| besselDerivativeNearFromState (2249656242596249 / 4000000000000) 2 (IntervalRat.scale (491 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-25368292372 / 1000000000000) (-25368292371 / 1000000000000), orderedInterval (-22077019470 / 1000000000000) (-22077019469 / 1000000000000)))) (orderedInterval (22364978592 / 1000000000000) (22364979026 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 2) <| besselDerivativeNearFromState (2101920679565981 / 4000000000000) 2 (IntervalRat.scale (491 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-34765584769 / 1000000000000) (-34765583657 / 1000000000000), orderedInterval (1722649437 / 1000000000000) (1722650549 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 2) <| besselDerivativeNearFromState (1500029777481773 / 4000000000000) 2 (IntervalRat.scale (491 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-38381224388 / 1000000000000) (-38381208885 / 1000000000000), orderedInterval (15034493520 / 1000000000000) (15034509023 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 2) <| besselDerivativeNearFromState (1700873893032267 / 4000000000000) 2 (IntervalRat.scale (491 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-36755910248 / 1000000000000) (-36755898561 / 1000000000000), orderedInterval (12132957562 / 1000000000000) (12132969249 / 1000000000000)))) (orderedInterval (5027044615 / 1000000000000) (5027048394 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 2) <| besselDerivativeNearFromState (1418011326992923 / 4000000000000) 2 (IntervalRat.scale (491 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-12032791770 / 1000000000000) (-12032791769 / 1000000000000), orderedInterval (-40615817638 / 1000000000000) (-40615817637 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 2) <| besselDerivativeNearFromState (1252856011367383 / 4000000000000) 2 (IntervalRat.scale (491 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-7194373310 / 1000000000000) (-7194373295 / 1000000000000), orderedInterval (44517470361 / 1000000000000) (44517470376 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 2) <| besselDerivativeNearFromState (363126504502917 / 800000000000) 2 (IntervalRat.scale (491 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (27829104407 / 1000000000000) (27829128041 / 1000000000000), orderedInterval (-25091995042 / 1000000000000) (-25091971408 / 1000000000000)))) (orderedInterval (-2795367271 / 1000000000000) (-2795365145 / 1000000000000))) = true
  rfl'

theorem compactCertificate374_chunkChecks2_2 :
    compactCertificate374.chunkChecks (2 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 2) <| besselDerivativeNearFromState (1004427021755999 / 4000000000000) 2 (IntervalRat.scale (491 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (26926688807 / 1000000000000) (26926688808 / 1000000000000), orderedInterval (42492959138 / 1000000000000) (42492959139 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 2) <| besselDerivativeNearFromState (851463910067239 / 4000000000000) 2 (IntervalRat.scale (491 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (1229704969 / 1000000000000) (1229704971 / 1000000000000), orderedInterval (54670716561 / 1000000000000) (54670716563 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 2) <| besselDerivativeNearFromState (532806580183117 / 4000000000000) 2 (IntervalRat.scale (491 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (61686032071 / 1000000000000) (61686044130 / 1000000000000), orderedInterval (-31443433279 / 1000000000000) (-31443421221 / 1000000000000)))) (orderedInterval (4006912093 / 1000000000000) (4006912265 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 2) <| besselDerivativeNearFromState (286545150857139 / 4000000000000) 2 (IntervalRat.scale (491 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-15326715691 / 1000000000000) (-15326715690 / 1000000000000), orderedInterval (-92909857865 / 1000000000000) (-92909857863 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 2) <| besselDerivativeNearFromState (778025825548417 / 4000000000000) 2 (IntervalRat.scale (491 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (28051755855 / 1000000000000) (28051755856 / 1000000000000), orderedInterval (49788750090 / 1000000000000) (49788750091 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 2) <| besselDerivativeNearFromState (1062327749312609 / 4000000000000) 2 (IntervalRat.scale (491 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (30346212019 / 1000000000000) (30346223659 / 1000000000000), orderedInterval (-38478261989 / 1000000000000) (-38478250349 / 1000000000000)))) (orderedInterval (3085745127 / 1000000000000) (3085746202 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 2) <| besselDerivativeNearFromState (449193419816883 / 4000000000000) 2 (IntervalRat.scale (491 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-1106417710 / 1000000000000) (-1106417702 / 1000000000000), orderedInterval (75289954834 / 1000000000000) (75289954841 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 2) <| besselDerivativeNearFromState (1825946313082643 / 4000000000000) 2 (IntervalRat.scale (491 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-36806290391 / 1000000000000) (-36806287421 / 1000000000000), orderedInterval (6357287949 / 1000000000000) (6357290919 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 2) <| besselDerivativeNearFromState (1219647515367037 / 4000000000000) 2 (IntervalRat.scale (491 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-37493827655 / 1000000000000) (-37493827654 / 1000000000000), orderedInterval (-26055429093 / 1000000000000) (-26055429092 / 1000000000000)))) (orderedInterval (-21230799770 / 1000000000000) (-21230798791 / 1000000000000))) = true
  rfl'

theorem compactCertificate374_chunkChecks2 :
    compactCertificate374.chunkChecks (2 : Fin 5) 0 9 = true :=
  compactCertificate374.chunkChecks_nine_of_three (2 : Fin 5) compactCertificate374_chunkChecks2_0
    compactCertificate374_chunkChecks2_1 compactCertificate374_chunkChecks2_2

theorem compactCertificate374_chunkChecks3_0 :
    compactCertificate374.chunkChecks (3 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 3) <| besselDerivativeNearFromState (491 / 2) 3 (IntervalRat.scale (491 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (48173084532 / 1000000000000) (48173084533 / 1000000000000), orderedInterval (16409631083 / 1000000000000) (16409631085 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 3) <| besselDerivativeNearFromState (723336755419391 / 4000000000000) 3 (IntervalRat.scale (491 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-33182054216 / 1000000000000) (-33182045780 / 1000000000000), orderedInterval (49279321150 / 1000000000000) (49279329585 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 3) <| besselDerivativeNearFromState (233912244811103 / 800000000000) 3 (IntervalRat.scale (491 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-39443760876 / 1000000000000) (-39443760875 / 1000000000000), orderedInterval (-24862105420 / 1000000000000) (-24862105419 / 1000000000000)))) (orderedInterval (-4159093269 / 1000000000000) (-4159093210 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 3) <| besselDerivativeNearFromState (211067861203837 / 4000000000000) 3 (IntervalRat.scale (491 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-15644526872 / 1000000000000) (-15644526871 / 1000000000000), orderedInterval (-108573936762 / 1000000000000) (-108573936760 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 3) <| besselDerivativeNearFromState (566957964344089 / 4000000000000) 3 (IntervalRat.scale (491 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-61235706162 / 1000000000000) (-61235706161 / 1000000000000), orderedInterval (-27017190582 / 1000000000000) (-27017190581 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 3) <| besselDerivativeNearFromState (1539401162225013 / 4000000000000) 3 (IntervalRat.scale (491 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (28619059801 / 1000000000000) (28619078985 / 1000000000000), orderedInterval (-28936152599 / 1000000000000) (-28936133415 / 1000000000000)))) (orderedInterval (-7769558569 / 1000000000000) (-7769553231 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 3) <| besselDerivativeNearFromState (1133915928688669 / 4000000000000) 3 (IntervalRat.scale (491 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (47329501886 / 1000000000000) (47329501947 / 1000000000000), orderedInterval (2294261899 / 1000000000000) (2294261960 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 3) <| besselDerivativeNearFromState (1942984270785937 / 4000000000000) 3 (IntervalRat.scale (491 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (14617996782 / 1000000000000) (14617996957 / 1000000000000), orderedInterval (-33134778978 / 1000000000000) (-33134778803 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 3) <| besselDerivativeNearFromState (1431193419816883 / 4000000000000) 3 (IntervalRat.scale (491 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (18036948511 / 1000000000000) (18036948512 / 1000000000000), orderedInterval (38105350470 / 1000000000000) (38105350471 / 1000000000000)))) (orderedInterval (-10770652282 / 1000000000000) (-10770652162 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate374_chunkChecks3_1 :
    compactCertificate374.chunkChecks (3 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 3) <| besselDerivativeNearFromState (2195818753904509 / 4000000000000) 3 (IntervalRat.scale (491 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (1322861299 / 1000000000000) (1322861300 / 1000000000000), orderedInterval (-34029797123 / 1000000000000) (-34029797122 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 3) <| besselDerivativeNearFromState (1267756548658261 / 4000000000000) 3 (IntervalRat.scale (491 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-18409229469 / 1000000000000) (-18409229468 / 1000000000000), orderedInterval (-40833555009 / 1000000000000) (-40833555008 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 3) <| besselDerivativeNearFromState (2249656242596249 / 4000000000000) 3 (IntervalRat.scale (491 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-25368292372 / 1000000000000) (-25368292371 / 1000000000000), orderedInterval (-22077019470 / 1000000000000) (-22077019469 / 1000000000000)))) (orderedInterval (-23452527967 / 1000000000000) (-23452527016 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 3) <| besselDerivativeNearFromState (2101920679565981 / 4000000000000) 3 (IntervalRat.scale (491 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-34765584769 / 1000000000000) (-34765583657 / 1000000000000), orderedInterval (1722649437 / 1000000000000) (1722650549 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 3) <| besselDerivativeNearFromState (1500029777481773 / 4000000000000) 3 (IntervalRat.scale (491 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-38381224388 / 1000000000000) (-38381208885 / 1000000000000), orderedInterval (15034493520 / 1000000000000) (15034509023 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 3) <| besselDerivativeNearFromState (1700873893032267 / 4000000000000) 3 (IntervalRat.scale (491 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-36755910248 / 1000000000000) (-36755898561 / 1000000000000), orderedInterval (12132957562 / 1000000000000) (12132969249 / 1000000000000)))) (orderedInterval (-4463708936 / 1000000000000) (-4463703058 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 3) <| besselDerivativeNearFromState (1418011326992923 / 4000000000000) 3 (IntervalRat.scale (491 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-12032791770 / 1000000000000) (-12032791769 / 1000000000000), orderedInterval (-40615817638 / 1000000000000) (-40615817637 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 3) <| besselDerivativeNearFromState (1252856011367383 / 4000000000000) 3 (IntervalRat.scale (491 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-7194373310 / 1000000000000) (-7194373295 / 1000000000000), orderedInterval (44517470361 / 1000000000000) (44517470376 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 3) <| besselDerivativeNearFromState (363126504502917 / 800000000000) 3 (IntervalRat.scale (491 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (27829104407 / 1000000000000) (27829128041 / 1000000000000), orderedInterval (-25091995042 / 1000000000000) (-25091971408 / 1000000000000)))) (orderedInterval (10774619712 / 1000000000000) (10774623626 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate374_chunkChecks3_2 :
    compactCertificate374.chunkChecks (3 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 3) <| besselDerivativeNearFromState (1004427021755999 / 4000000000000) 3 (IntervalRat.scale (491 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (26926688807 / 1000000000000) (26926688808 / 1000000000000), orderedInterval (42492959138 / 1000000000000) (42492959139 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 3) <| besselDerivativeNearFromState (851463910067239 / 4000000000000) 3 (IntervalRat.scale (491 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (1229704969 / 1000000000000) (1229704971 / 1000000000000), orderedInterval (54670716561 / 1000000000000) (54670716563 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 3) <| besselDerivativeNearFromState (532806580183117 / 4000000000000) 3 (IntervalRat.scale (491 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (61686032071 / 1000000000000) (61686044130 / 1000000000000), orderedInterval (-31443433279 / 1000000000000) (-31443421221 / 1000000000000)))) (orderedInterval (9434670452 / 1000000000000) (9434670569 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 3) <| besselDerivativeNearFromState (286545150857139 / 4000000000000) 3 (IntervalRat.scale (491 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-15326715691 / 1000000000000) (-15326715690 / 1000000000000), orderedInterval (-92909857865 / 1000000000000) (-92909857863 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 3) <| besselDerivativeNearFromState (778025825548417 / 4000000000000) 3 (IntervalRat.scale (491 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (28051755855 / 1000000000000) (28051755856 / 1000000000000), orderedInterval (49788750090 / 1000000000000) (49788750091 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 3) <| besselDerivativeNearFromState (1062327749312609 / 4000000000000) 3 (IntervalRat.scale (491 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (30346212019 / 1000000000000) (30346223659 / 1000000000000), orderedInterval (-38478261989 / 1000000000000) (-38478250349 / 1000000000000)))) (orderedInterval (-3226793886 / 1000000000000) (-3226792724 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 3) <| besselDerivativeNearFromState (449193419816883 / 4000000000000) 3 (IntervalRat.scale (491 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-1106417710 / 1000000000000) (-1106417702 / 1000000000000), orderedInterval (75289954834 / 1000000000000) (75289954841 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 3) <| besselDerivativeNearFromState (1825946313082643 / 4000000000000) 3 (IntervalRat.scale (491 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-36806290391 / 1000000000000) (-36806287421 / 1000000000000), orderedInterval (6357287949 / 1000000000000) (6357290919 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 3) <| besselDerivativeNearFromState (1219647515367037 / 4000000000000) 3 (IntervalRat.scale (491 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-37493827655 / 1000000000000) (-37493827654 / 1000000000000), orderedInterval (-26055429093 / 1000000000000) (-26055429092 / 1000000000000)))) (orderedInterval (-5996154884 / 1000000000000) (-5996153108 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate374_chunkChecks3 :
    compactCertificate374.chunkChecks (3 : Fin 5) 0 9 = true :=
  compactCertificate374.chunkChecks_nine_of_three (3 : Fin 5) compactCertificate374_chunkChecks3_0
    compactCertificate374_chunkChecks3_1 compactCertificate374_chunkChecks3_2

theorem compactCertificate374_chunkChecks4_0 :
    compactCertificate374.chunkChecks (4 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 4) <| besselDerivativeNearFromState (491 / 2) 4 (IntervalRat.scale (491 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (48173084532 / 1000000000000) (48173084533 / 1000000000000), orderedInterval (16409631083 / 1000000000000) (16409631085 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 4) <| besselDerivativeNearFromState (723336755419391 / 4000000000000) 4 (IntervalRat.scale (491 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-33182054216 / 1000000000000) (-33182045780 / 1000000000000), orderedInterval (49279321150 / 1000000000000) (49279329585 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 4) <| besselDerivativeNearFromState (233912244811103 / 800000000000) 4 (IntervalRat.scale (491 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-39443760876 / 1000000000000) (-39443760875 / 1000000000000), orderedInterval (-24862105420 / 1000000000000) (-24862105419 / 1000000000000)))) (orderedInterval (14379547892 / 1000000000000) (14379547947 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 4) <| besselDerivativeNearFromState (211067861203837 / 4000000000000) 4 (IntervalRat.scale (491 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-15644526872 / 1000000000000) (-15644526871 / 1000000000000), orderedInterval (-108573936762 / 1000000000000) (-108573936760 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 4) <| besselDerivativeNearFromState (566957964344089 / 4000000000000) 4 (IntervalRat.scale (491 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-61235706162 / 1000000000000) (-61235706161 / 1000000000000), orderedInterval (-27017190582 / 1000000000000) (-27017190581 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 4) <| besselDerivativeNearFromState (1539401162225013 / 4000000000000) 4 (IntervalRat.scale (491 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (28619059801 / 1000000000000) (28619078985 / 1000000000000), orderedInterval (-28936152599 / 1000000000000) (-28936133415 / 1000000000000)))) (orderedInterval (-12471032758 / 1000000000000) (-12471024372 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 4) <| besselDerivativeNearFromState (1133915928688669 / 4000000000000) 4 (IntervalRat.scale (491 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (47329501886 / 1000000000000) (47329501947 / 1000000000000), orderedInterval (2294261899 / 1000000000000) (2294261960 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 4) <| besselDerivativeNearFromState (1942984270785937 / 4000000000000) 4 (IntervalRat.scale (491 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (14617996782 / 1000000000000) (14617996957 / 1000000000000), orderedInterval (-33134778978 / 1000000000000) (-33134778803 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 4) <| besselDerivativeNearFromState (1431193419816883 / 4000000000000) 4 (IntervalRat.scale (491 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (18036948511 / 1000000000000) (18036948512 / 1000000000000), orderedInterval (38105350470 / 1000000000000) (38105350471 / 1000000000000)))) (orderedInterval (-4855667190 / 1000000000000) (-4855666963 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate374_chunkChecks4_1 :
    compactCertificate374.chunkChecks (4 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 4) <| besselDerivativeNearFromState (2195818753904509 / 4000000000000) 4 (IntervalRat.scale (491 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (1322861299 / 1000000000000) (1322861300 / 1000000000000), orderedInterval (-34029797123 / 1000000000000) (-34029797122 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 4) <| besselDerivativeNearFromState (1267756548658261 / 4000000000000) 4 (IntervalRat.scale (491 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-18409229469 / 1000000000000) (-18409229468 / 1000000000000), orderedInterval (-40833555009 / 1000000000000) (-40833555008 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 4) <| besselDerivativeNearFromState (2249656242596249 / 4000000000000) 4 (IntervalRat.scale (491 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-25368292372 / 1000000000000) (-25368292371 / 1000000000000), orderedInterval (-22077019470 / 1000000000000) (-22077019469 / 1000000000000)))) (orderedInterval (-108802504447 / 1000000000000) (-108802502335 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 4) <| besselDerivativeNearFromState (2101920679565981 / 4000000000000) 4 (IntervalRat.scale (491 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-34765584769 / 1000000000000) (-34765583657 / 1000000000000), orderedInterval (1722649437 / 1000000000000) (1722650549 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 4) <| besselDerivativeNearFromState (1500029777481773 / 4000000000000) 4 (IntervalRat.scale (491 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-38381224388 / 1000000000000) (-38381208885 / 1000000000000), orderedInterval (15034493520 / 1000000000000) (15034509023 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 4) <| besselDerivativeNearFromState (1700873893032267 / 4000000000000) 4 (IntervalRat.scale (491 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-36755910248 / 1000000000000) (-36755898561 / 1000000000000), orderedInterval (12132957562 / 1000000000000) (12132969249 / 1000000000000)))) (orderedInterval (-4875694590 / 1000000000000) (-4875685377 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 4) <| besselDerivativeNearFromState (1418011326992923 / 4000000000000) 4 (IntervalRat.scale (491 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-12032791770 / 1000000000000) (-12032791769 / 1000000000000), orderedInterval (-40615817638 / 1000000000000) (-40615817637 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 4) <| besselDerivativeNearFromState (1252856011367383 / 4000000000000) 4 (IntervalRat.scale (491 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-7194373310 / 1000000000000) (-7194373295 / 1000000000000), orderedInterval (44517470361 / 1000000000000) (44517470376 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 4) <| besselDerivativeNearFromState (363126504502917 / 800000000000) 4 (IntervalRat.scale (491 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (27829104407 / 1000000000000) (27829128041 / 1000000000000), orderedInterval (-25091995042 / 1000000000000) (-25091971408 / 1000000000000)))) (orderedInterval (8725538785 / 1000000000000) (8725546014 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate374_chunkChecks4_2 :
    compactCertificate374.chunkChecks (4 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 4) <| besselDerivativeNearFromState (1004427021755999 / 4000000000000) 4 (IntervalRat.scale (491 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (26926688807 / 1000000000000) (26926688808 / 1000000000000), orderedInterval (42492959138 / 1000000000000) (42492959139 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 4) <| besselDerivativeNearFromState (851463910067239 / 4000000000000) 4 (IntervalRat.scale (491 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (1229704969 / 1000000000000) (1229704971 / 1000000000000), orderedInterval (54670716561 / 1000000000000) (54670716563 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 4) <| besselDerivativeNearFromState (532806580183117 / 4000000000000) 4 (IntervalRat.scale (491 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (61686032071 / 1000000000000) (61686044130 / 1000000000000), orderedInterval (-31443433279 / 1000000000000) (-31443421221 / 1000000000000)))) (orderedInterval (-4654457581 / 1000000000000) (-4654457494 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 4) <| besselDerivativeNearFromState (286545150857139 / 4000000000000) 4 (IntervalRat.scale (491 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-15326715691 / 1000000000000) (-15326715690 / 1000000000000), orderedInterval (-92909857865 / 1000000000000) (-92909857863 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 4) <| besselDerivativeNearFromState (778025825548417 / 4000000000000) 4 (IntervalRat.scale (491 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (28051755855 / 1000000000000) (28051755856 / 1000000000000), orderedInterval (49788750090 / 1000000000000) (49788750091 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 4) <| besselDerivativeNearFromState (1062327749312609 / 4000000000000) 4 (IntervalRat.scale (491 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (30346212019 / 1000000000000) (30346223659 / 1000000000000), orderedInterval (-38478261989 / 1000000000000) (-38478250349 / 1000000000000)))) (orderedInterval (-3407611456 / 1000000000000) (-3407610196 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 4) <| besselDerivativeNearFromState (449193419816883 / 4000000000000) 4 (IntervalRat.scale (491 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-1106417710 / 1000000000000) (-1106417702 / 1000000000000), orderedInterval (75289954834 / 1000000000000) (75289954841 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 4) <| besselDerivativeNearFromState (1825946313082643 / 4000000000000) 4 (IntervalRat.scale (491 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-36806290391 / 1000000000000) (-36806287421 / 1000000000000), orderedInterval (6357287949 / 1000000000000) (6357290919 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 4) <| besselDerivativeNearFromState (1219647515367037 / 4000000000000) 4 (IntervalRat.scale (491 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-37493827655 / 1000000000000) (-37493827654 / 1000000000000), orderedInterval (-26055429093 / 1000000000000) (-26055429092 / 1000000000000)))) (orderedInterval (52602569846 / 1000000000000) (52602573098 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate374_chunkChecks4 :
    compactCertificate374.chunkChecks (4 : Fin 5) 0 9 = true :=
  compactCertificate374.chunkChecks_nine_of_three (4 : Fin 5) compactCertificate374_chunkChecks4_0
    compactCertificate374_chunkChecks4_1 compactCertificate374_chunkChecks4_2

theorem compactCertificate374_chunks :
    ∀ r : Fin 5, ∀ b, compactCertificate374.chunkCheck r b = true :=
  compactCertificate374.chunkChecks_all (by
    intro r
    fin_cases r
    · exact compactCertificate374_chunkChecks0
    · exact compactCertificate374_chunkChecks1
    · exact compactCertificate374_chunkChecks2
    · exact compactCertificate374_chunkChecks3
    · exact compactCertificate374_chunkChecks4)

theorem compactCertificate374_coefficient0 :
    compactCertificate374.coefficientCheck (0 : Fin 5) = true := by
  rfl'

theorem compactCertificate374_coefficient1 :
    compactCertificate374.coefficientCheck (1 : Fin 5) = true := by
  rfl'

theorem compactCertificate374_coefficient2 :
    compactCertificate374.coefficientCheck (2 : Fin 5) = true := by
  rfl'

theorem compactCertificate374_coefficient3 :
    compactCertificate374.coefficientCheck (3 : Fin 5) = true := by
  rfl'

theorem compactCertificate374_coefficient4 :
    compactCertificate374.coefficientCheck (4 : Fin 5) = true := by
  rfl'

theorem compactCertificate374_coefficients : ∀ r : Fin 5,
    compactCertificate374.coefficientCheck r = true := by
  intro r
  fin_cases r
  · exact compactCertificate374_coefficient0
  · exact compactCertificate374_coefficient1
  · exact compactCertificate374_coefficient2
  · exact compactCertificate374_coefficient3
  · exact compactCertificate374_coefficient4

theorem compactCertificate374_lower : (1 : ℚ) ≤ compactCertificate374.output.lo := by
  norm_num [CompactCertificate.output, CompactCertificate.interval,
    CompactCertificate.coefficientTargetNat, compactCertificate374, dualConstant,
    intervalTaylorSum, intervalPow, intervalSub, intervalMaxAbs, widenInterval,
    rationalErrorInterval, orderedInterval, IntervalRat.add, IntervalRat.mul, IntervalRat.scale,
    IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4]

theorem compactCertificate374_proves {t : ℝ} (ht : t ∈ compactCertificate374.interval) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t :=
  compactCertificate374.proves compactCertificate374_states compactCertificate374_chunks
    compactCertificate374_coefficients compactCertificate374_lower ht

end Erdos232
